enum Data {
    Int(i32),
    Flt(f32),
    Str(String),
    Ptr(usize),
}

const MAX_STRING_LENGTH : usize = 256;

const WORD_HIGH_BIT : u32 = 0x8000_0000;
const WORD_SIGN_BIT : u32 = 0x4000_0000;
const WORD_INT_MASK : u32 = 0x7fff_ffff;

const WORD_XT_MASK  : u32 = 0x3fff_ffff;
const WORD_STR_MASK : u32 = 0x3fff_ffff;
const WORD_XT_BITS  : u32 = WORD_HIGH_BIT | WORD_SIGN_BIT;
const WORD_STR_BITS : u32 = WORD_HIGH_BIT;

#[derive(Debug,PartialEq,Eq,Clone,Copy)]
struct Word(u32);

#[derive(Debug,PartialEq,Eq,Clone,Copy)]
struct XT(u32);

impl XT {
    const MAX : u32 = 0x3fff_ffff;
    const MIN : u32 = 0;
    const MASK : u32 = 0x3fff_ffff;
    const BITS : u32 = Word::HIGH_BIT | Word::SIGN_BIT;

    fn to_word(self) -> Word {
        Word::xt(self.0)
    }
}

#[derive(Debug,PartialEq,Eq,Clone,Copy)]
struct ScratchLoc{len:u8, off:u8}

/*
#[derive(Debug,PartialEq,Eq,Clone,Copy)]
struct AllocLoc(u32);
*/

#[derive(Debug,PartialEq,Eq,Clone,Copy)]
enum ST {
    // TODO: Check size.  This needs to fit in 32 bits.

    Allocated(u32),
    PadSpace(ScratchLoc),
    WordSpace(ScratchLoc),
    InputSpace(ScratchLoc),
    // Pic(ScratchLoc),
}

impl ST {
    const MAX : u32 = 0x3fff_ffff;
    const MIN : u32 = 0;
    const MASK : u32 = 0x3fff_ffff;
    const BITS : u32 = Word::HIGH_BIT;

    // Indicates string scratch space
    const SCRATCH_BIT : u32 = 0x2000_0000;
    const ALLOC_MASK  : u32 = 0x1fff_ffff;

    const LOC_MASK : u32 = 0x0007_0000;
    const LEN_MASK : u32 = 0x0000_ff00;
    const OFF_MASK : u32 = 0x0000_00ff;

    const ST_BITS : u32 = Word::HIGH_BIT;

    fn from_u32(val: u32) -> Result<ST,ForthError> {
        // check for valid string encoding
        if (val & Word::HIGH_BIT) == 0 || (val & Word::SIGN_BIT) == 1 {
            return Err(ForthError::InvalidStringValue(val));
        }

        if (val & ST::SCRATCH_BIT) == 0 {
            return Ok(ST::Allocated(val & ST::MASK));
        }

        match (val & ST::LOC_MASK) >> 16 {
            0 => Ok(ST::pad_space((val & ST::OFF_MASK) as u8, ((val & ST::LEN_MASK) >> 8) as u8)),
            1 => Ok(ST::word_space((val & ST::OFF_MASK) as u8, ((val & ST::LEN_MASK) >> 8) as u8)),
            2 => Ok(ST::input_space((val & ST::OFF_MASK) as u8, ((val & ST::LEN_MASK) >> 8) as u8)),
            _ => Err(ForthError::InvalidStringValue(val)),
        }
    }

    fn addr(self) -> u32 {
        match self {
            ST::Allocated(val) => {
                val >> 8
            },
            ST::PadSpace(loc) | ST::WordSpace(loc) | ST::InputSpace(loc) => {
                loc.off as u32
            },
        }
    }

    fn len(self) -> u32 {
        match self {
            ST::Allocated(val) => {
                val & 0xff
            },
            ST::PadSpace(loc) | ST::WordSpace(loc) | ST::InputSpace(loc) => {
                loc.len as u32
            },
        }
    }

    fn offset(self, by: u8) -> ST {
        let addr = self.addr();
        let len  = self.len();

        let off = std::cmp::min(by as u32,len);

        let new_addr = addr + off;
        let new_len  = (len - off) as u8;
        match self {
            ST::Allocated(_) => {
                ST::allocated_space(new_addr, new_len)
            },
            ST::PadSpace(_) => {
                ST::pad_space(new_addr as u8, new_len)
            },
            ST::WordSpace(_) => {
                ST::word_space(new_addr as u8, new_len)
            },
            ST::InputSpace(_) => {
                ST::input_space(new_addr as u8, new_len)
            },
        }
    }

    fn allocated_space(off: u32, len: u8) -> ST {
        // TODO: check for overflow
        ST::Allocated((off<<8) | (len as u32))
    }

    fn pad_space(off: u8, len: u8) -> ST {
        ST::PadSpace(ScratchLoc{off:off, len:len})
    }

    fn word_space(off: u8, len: u8) -> ST {
        ST::WordSpace(ScratchLoc{off:off, len:len})
    }

    fn input_space(off: u8, len: u8) -> ST {
        ST::InputSpace(ScratchLoc{off:off, len:len})
    }

    fn to_word(self) -> Word {
        let v : u32 = match self {
            ST::Allocated(off) => {
                if (ST::ALLOC_MASK & off) != off {
                    panic!("invalid allocated string offset");
                }

                off
            },
            ST::PadSpace(loc) => {
                ST::SCRATCH_BIT | ((0 as u32) << 16) | ((loc.len as u32) << 8) | (loc.off as u32)
            },
            ST::WordSpace(loc) => {
                ST::SCRATCH_BIT | ((1 as u32) << 16) | ((loc.len as u32) << 8) | (loc.off as u32)
            },
            ST::InputSpace(loc) => {
                ST::SCRATCH_BIT | ((2 as u32) << 16) | ((loc.len as u32) << 8) | (loc.off as u32)
            },
        };

        Word(v | ST::ST_BITS)
    }
}

#[derive(Debug,PartialEq,Eq,Clone,Copy)]
enum WordKind {
    Int(i32),
    XT(XT),
    Str(ST),
}

impl Word {
    const HIGH_BIT : u32 = 0x8000_0000;
    const SIGN_BIT : u32 = 0x4000_0000;
    const INT_MASK : u32 = 0x7fff_ffff;

    const INT_MIN  : i32 = -1073741824;
    const INT_MAX  : i32 =  1073741823;

    fn int(x: i32) -> Word {
        // TODO: range check
        Word((x as u32) & WORD_INT_MASK)
    }

    fn xt(x: u32) -> Word {
        // TODO: range check
        Word((x & WORD_XT_MASK) | WORD_XT_BITS)
    }

    fn str(x: u32) -> Word {
        // TODO: range check
        Word((x & WORD_STR_MASK) | WORD_STR_BITS)
    }

    pub fn from_xt(xt: XT) -> Word {
        Word::xt(xt.0)
    }

    pub fn from_str(st: ST) -> Word {
        st.to_word()
    }

    pub fn kind(self) -> WordKind {
        match self.0 {
            x if (x & WORD_HIGH_BIT) == 0 => { WordKind::Int((x | ((x & WORD_SIGN_BIT) << 1)) as i32) },
            x if (x & WORD_SIGN_BIT) == 0 => {
                // FIXME: unwrap!
                WordKind::Str(ST::from_u32(x).unwrap())
            },
            x => { WordKind::XT(XT(x & WORD_XT_MASK)) },
        }
    }

    pub fn to_int(self) -> Option<i32> {
        if let WordKind::Int(x) = self.kind() { Some(x) } else { None }
    }

    pub fn to_xt(self) -> Option<XT> {
        if let WordKind::XT(x) = self.kind() { Some(x) } else { None }
    }

    pub fn to_str(self) -> Option<ST> {
        if let WordKind::Str(x) = self.kind() { Some(x) } else { None }
    }
}

impl std::fmt::Display for Word {
    fn fmt(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.kind() {
            WordKind::Int(x) => { formatter.write_fmt(format_args!("[int] {}", x)) },
            WordKind::XT(XT(x))  => { formatter.write_fmt(format_args!("[xt] {}", x)) },
            WordKind::Str(st) => {
                match st {
                    ST::Allocated(v) => {
                        formatter.write_fmt(format_args!("[str:alloc] @ {} len={},addr={}", v, st.len(), st.addr())) },
                    ST::PadSpace(loc)  => { formatter.write_fmt(format_args!("[str:pad] len={},off={}", loc.len, loc.off)) },
                    ST::WordSpace(loc) => { formatter.write_fmt(format_args!("[str:word] len={},off={}", loc.len, loc.off)) },
                    ST::InputSpace(loc) => { formatter.write_fmt(format_args!("[str:input] len={},off={}", loc.len, loc.off)) },
                }
            },
            /*
            WordKind::Scratch(scratch) => {
                match scratch {
                }
            }
            */
        }
    }
}

#[derive(Clone,Copy)]
struct ForthFunc<'tf>(fn(&mut ToyForth<'tf>) -> Result<(),ForthError>);

impl<'tf> PartialEq for ForthFunc<'tf> {
    fn eq(&self, other: &ForthFunc) -> bool {
        return (self.0 as usize) == (other.0 as usize)
    }
}

impl<'tf> Eq for ForthFunc<'tf> { }

#[derive(Debug,Clone,Copy,PartialEq,Eq)]
enum Primitive {
    Bye,
    Push(Word),
    Drop,
    Dup,
    Swap,
    Math{op:u8},
    EOL,
    Lookup,
    DefStr,
    DefWord,
    Func(u32),
    // ToNumber,
    // Immediate,
}

#[derive(Debug,Clone,Copy,PartialEq,Eq)]
enum Instr {
    Empty,
    Prim(Primitive),
    DoCol(XT),
    Special(),
    Data(Word),
    // Char{bytes:[u8;std::mem::size_of::<Word>()]},
    Execute,
    Unnest,
}

struct DictEntry {
    st: ST,
    xt: XT,
    flags: u32,
}

impl DictEntry {
    const PRIMITIVE : u32 = 0x0000_0001;
    const IMMEDIATE : u32 = 0x0000_0002;

    pub fn is_primitive(&self) -> bool {
        (self.flags & DictEntry::PRIMITIVE) != 0
    }

    pub fn is_immediate(&self) -> bool {
        (self.flags & DictEntry::IMMEDIATE) != 0
    }
}

struct ToyForth<'tf> {
    dstack: Vec<Word>,
    rstack: Vec<Word>,
    ufuncs: Vec<ForthFunc<'tf>>,

    dict: Vec<DictEntry>,
    data: Vec<Word>,
    strings: std::vec::Vec<u8>,
    code: Vec<Instr>,

    pad:  [u8;256],
    word: [u8;256],

    input: String,
    input_off: usize,

    in_stream: Option<&'tf mut dyn std::io::BufRead>,
    out_stream: Option<&'tf mut dyn std::io::Write>,
}

#[derive(Debug,PartialEq)]
enum LexErrorType {
    UnterminatedString,
    InvalidNumber,
    InvalidEscape,
    InvalidIdent,
    // InvalidChar,
}

#[derive(Debug, PartialEq)]
struct LexError {
    error: LexErrorType,
    ind0: usize,
    ind1: usize,
}

#[derive(Debug, PartialEq)]
struct LexError1<'a> {
    error: LexErrorType,
    source: &'a str,
}

#[derive(Debug, PartialEq)]
enum Token {
    Str(String),
    Integer(i32),
    Float(f32),
    Ident(String),
}

#[derive(Debug, PartialEq)]
struct LexToken<'a> {
    token: Token,
    source: &'a str,
}

impl<'a> LexToken<'a> {
    fn str(v: &str, src: &'a str) -> LexToken<'a> {
        return LexToken{
            token: Token::Str(v.to_string()),
            source: src,
        };
    }

    fn string(v: String, src: &'a str) -> LexToken<'a> {
        return LexToken{
            token: Token::Str(v),
            source: src,
        };
    }

    fn ident(v: &'a str) -> LexToken<'a> {
        return LexToken{
            token: Token::Ident(v.to_string()),
            source: v,
        };
    }

    fn int(v: i32, src: &'a str) -> LexToken<'a> {
        return LexToken{
            token: Token::Integer(v),
            source: src,
        };
    }

    fn flt(v: f32, src: &'a str) -> LexToken<'a> {
        return LexToken{
            token: Token::Float(v),
            source: src,
        };
    }

    fn parse_num(v: &'a str) -> std::result::Result<LexToken<'a>, LexError1> {
        /* FIXME: better handling of errors here, especially various kinds of
         * overflow
         */
        if let Ok(x) = v.parse::<i32>() {
            return Ok(LexToken{
                token: Token::Integer(x),
                source: v,
            });
        }
        else if let Ok(x) = v.parse::<f32>() {
            return Ok(LexToken{
                token: Token::Float(x),
                source: v,
            });
        }
        else {
            return Err(LexError1{
                error: LexErrorType::InvalidNumber,
                source: v,
            });
        }
    }
}

impl Data {
    fn from_token(tok: LexToken) -> Result<Data,String> {
        match tok.token {
            Token::Str(v) => { Ok(Data::Str(v)) },
            Token::Integer(v) => { Ok(Data::Int(v)) },
            Token::Float(v) => { Ok(Data::Flt(v)) },
            // FIXME: handle ident lookup
            _ => { Err("ident not yet implemented".to_string()) },
        }
    }
}

struct Lexer<'a> {
    buf: &'a str,
    pos: usize,
}

fn tokenize<'a>(v: &'a str) -> Lexer<'a> {
    return Lexer{ buf: v, pos: 0 };
}

trait Tokenizer<'a> {
    type Item;
    fn next_str(&self, v: &'a str) -> (Option<Self::Item>,usize);
    fn next_num(&self, v: &'a str) -> (Option<Self::Item>,usize);
    fn next_ident(&self, v: &'a str) -> (Option<Self::Item>,usize);
}

impl<'a> Tokenizer<'a> for Lexer<'a> {
    type Item = std::result::Result<LexToken<'a>, LexError1<'a>>;

    fn next_str(&self, v: &'a str) -> (Option<Self::Item>,usize) {
        let mut iter = v.char_indices().peekable();
        let mut is_esc = false;
        let mut s = String::new();

        while let Some((i,ch)) = iter.next() {
            if is_esc {
                let esc_ch = match ch {
                    'n'  => { Some('\n') },
                    'r'  => { Some('\r') },
                    't'  => { Some('\t') },
                    '\\' => { Some('\\') },
                    '"'  => { Some('"')  },
                    _    => { None },
                };

                if let Some(c) = esc_ch {
                    s.push(c);
                    is_esc = false;
                } else {
                    return (Some(Err(LexError1{
                        error: LexErrorType::InvalidEscape,
                        source: &v,
                    })), i);
                }
            } else {
                match ch {
                    '\\' => { is_esc = true; },
                    '"' => {
                        return (Some(Ok(LexToken::string(s, &v[..i]))), i+1);
                    },
                    _ => {
                        s.push(ch);
                    }
                }
            }
        }

        return (Some(Err(LexError1{
            error: LexErrorType::UnterminatedString,
            source: &v,
        })), v.len());
    }

    fn next_num(&self, v: &'a str) -> (Option<Self::Item>,usize) {
        // eprintln!("next_num({})", v);
        let mut it = v.char_indices().peekable();
        if let Some((_,ch)) = it.peek() {
            if *ch == '+' || *ch == '-' {
                it.next();
            }
        }

        let after = it.skip_while(|(_,ch)| !ch.is_whitespace()).next();

        match after {
            Some((i,ch)) if ch.is_whitespace() => {
                return (Some(LexToken::parse_num(&v[..i])), i);
            },
            Some((i,_)) => {
                return (Some(Err(LexError1{
                    error: LexErrorType::InvalidNumber,
                    source: &v[..i],
                })), i);
            },
            None => {
                return (Some(LexToken::parse_num(&v)), v.len());
            }
        }
    }

    fn next_ident(&self, v: &'a str) -> (Option<Self::Item>,usize) {
        let after = v.char_indices().skip_while(|(_,ch)| !ch.is_whitespace()).next();

        match after {
            Some((i,_)) => {
                if let Some(_) = &v[..i].find(|c| c == '"' || c == '\\') {
                    return (Some(Err(LexError1{
                        error: LexErrorType::InvalidIdent,
                        source: &v[..i],
                    })), i);
                }

                return (Some(Ok(LexToken::ident(&v[..i]))), i);
            },
            None => {
                return (Some(Ok(LexToken::ident(v))), v.len());
            }
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = std::result::Result<LexToken<'a>, LexError1<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut iter = self.buf[self.pos..].char_indices().skip_while(|(_,ch)| ch.is_whitespace()).peekable();
        if let Some((i,ch)) = iter.next() {
            // eprintln!("i={}, ch={}, buf=\"{}\" ^ \"{}\"", i, ch, &self.buf[..self.pos], &self.buf[self.pos..]);
            let (res,ind) = match ch {
                ch if ch.is_digit(10) => {
                    let ind0 = self.pos+i;
                    self.next_num(&self.buf[ind0..])
                },

                '"' => {
                    if let Some((next_i,_)) = iter.peek() {
                        let ind0 = self.pos+next_i;
                        let (res,ind1) = self.next_str(&self.buf[ind0..]);
                        (res,1+ind1)
                    } else {
                        let ind0 = self.pos+i;
                        (Some(Err(LexError1::<'a>{ error: LexErrorType::UnterminatedString, source: &self.buf[ind0..] })), 0)
                    }
                },

                '-' | '+' => {
                    let ind0 = self.pos + i;
                    match iter.peek() {
                        Some((_,next_ch)) if next_ch.is_digit(10) => {
                            self.next_num(&self.buf[ind0..])
                        },
                        _ => {
                            self.next_ident(&self.buf[ind0..])
                        }
                    }
                },

                _ => {
                    let ind0 = self.pos+i;
                    self.next_ident(&self.buf[ind0..])
                }
            };

            // eprintln!("res = {:?}, i={}, ind={}, self.pos={}", res, i, ind, self.pos);
            if let Some(_) = res {
                self.pos += i + ind;
            }

            return res;
        }
        else {
            return None;
        }
    }
}

const MATH_PLUS  : u8 = 0;
const MATH_MINUS : u8 = 1;
const MATH_STAR  : u8 = 2;
const MATH_SLASH : u8 = 3;

#[derive(Debug)]
enum ForthError {
    StackUnderflow,
    ReturnStackUnderflow,

    InvalidOperation,
    InvalidArgument,
    DivisionByZero,

    NumberOutOfRange,

    InvalidEmptyString,
    StringTooLong,
    StringOffsetTooLarge,

    FunctionSpaceOverflow,
    CellSpaceOverflow,
    StringSpaceOverflow,

    Unimplemented,

    StringNotFound,
    WordNotFound(ST),

    InvalidCell(XT),
    InvalidExecutionToken(Word),
    InvalidString(ST),
    InvalidStringValue(u32),
    InvalidDelimiter(i32),
    InvalidFunction(u32),

    IOError(std::io::Error),
}

impl std::convert::From<std::io::Error> for ForthError {
    fn from(err: std::io::Error) -> Self {
        ForthError::IOError(err)
    }
}

impl<'tf> ToyForth<'tf> {
    pub fn new() -> ToyForth<'tf> {
        let mut tf = ToyForth{
            dstack:  std::vec::Vec::new(),
            rstack:  std::vec::Vec::new(),
            ufuncs:  std::vec::Vec::new(),

            dict:    std::vec::Vec::new(),
            data:    std::vec::Vec::new(),
            strings: std::vec::Vec::new(),
            code:    std::vec::Vec::new(),

            pad:     [0;256],
            word:    [0;256],

            input: std::string::String::new(),
            input_off: 0,

            in_stream: None,
            out_stream: None,
        };

        // First word in dict (addr 0) always holds BYE
        tf.push_cell(Instr::Prim(Primitive::Bye));

        // set up standard dictionary
        tf.add_prim("BYE", Primitive::Bye);
        tf.add_prim("DUP", Primitive::Dup);
        tf.add_prim("DROP", Primitive::Drop);
        tf.add_prim("SWAP", Primitive::Swap);

        tf.add_prim("+", Primitive::Math{op:MATH_PLUS});
        tf.add_prim("-", Primitive::Math{op:MATH_MINUS});
        tf.add_prim("*", Primitive::Math{op:MATH_STAR});
        tf.add_prim("/", Primitive::Math{op:MATH_SLASH});

        // words that may be replaced with Forth definitions at some point
        tf.add_prim("BL", Primitive::Push(Word::int(' ' as i32)));
        tf.add_prim("CR", Primitive::Push(Word::int('\n' as i32)));
        tf.add_func("CHAR", ToyForth::builtin_char);
        tf.add_func("WORD", ToyForth::builtin_word);
        tf.add_func(".", ToyForth::builtin_dot);
        tf.add_func(">NUMBER", ToyForth::builtin_to_number);


        // tf.add_prim("IMMEDIATE", Primitive::Immediate);

        eprintln!("Cell size is {}", std::mem::size_of::<Instr>());
        eprintln!("Prim size is {}", std::mem::size_of::<Primitive>());
        eprintln!("Word size is {}", std::mem::size_of::<Word>());

        return tf;
    }

    pub fn print_stacks(&self, msg: &str) {
        eprintln!(">>> {}: ",msg);
        for (i,w) in self.dstack.iter().enumerate() {
            eprintln!("[D {:3}] {:?}", i,w.kind());
        }
        for (i,w) in self.rstack.iter().enumerate() {
            eprintln!("[R {:3}] {:?}", i,w);
        }
        eprintln!("done\n");
    }

    pub fn interpret(&mut self, s: &str) -> Result<(), ForthError> {
        // initial interpret is dumb...

        self.input.clear();
        self.input_off = 0;
        self.input.push_str(s);

        self.builtin_interpret()
    }

    pub fn builtin_interpret(&mut self) -> Result<(), ForthError> {
        loop {
            self.push_int(' ' as i32)?;
            self.builtin_word()?;
            // self.print_stacks("after WORD");
            self.builtin_find()?;
            // self.print_stacks("after FIND");

            if self.pop_int()? == 0 {
                let st = self.pop_str()?;
                // eprintln!("st = {:?}", st);
                let len = st.len();

                if len == 0 {
                    break;
                }

                self.push_int(0)?;
                self.push(st.to_word())?;
                self.push_int(len as i32)?;

                self.builtin_to_number()?;

                let consumed = self.pop_int()?;

                if consumed < (len as i32) {
                    return Err(ForthError::WordNotFound(st));
                }

                self.drop()?;

                /*
                return Err(ForthError::WordNotFound(st));
                */
            } else {
                let xt = self.pop_xt()?;
                // self.print_stacks("after xt");
                self.ret_push_bye()?;
                self.exec(xt)?;
                // self.print_stacks("after exec");
            }
        }

        Ok(())
    }

    fn refill(r: &mut dyn std::io::BufRead, s: &mut String) -> Result<(), ForthError> {
        r.read_line(s)?;
        if let Some(ch) = s.pop() {
            if ch != '\n' {
                s.push(ch);
            }
        }

        Ok(())
    }

    pub fn builtin_refill(&mut self) -> Result<(), ForthError> {
        self.input_off = 0;
        self.input.clear();

        if let Some(inp) = &mut self.in_stream {
            return ToyForth::refill(inp, &mut self.input);
        }

        return Ok(());
    }

    pub fn write_prompt(&mut self, prompt: &str) -> Result<(), ForthError> {
        if let Some(w) = &mut self.out_stream {
            write!(w, "{}\n", prompt);
            w.flush()?;
        }

        Ok(())
    }

    pub fn std_repl() -> Result<(),ForthError> {
        let prompt = "ok";

        let stdin = std::io::stdin();
        let stdout = std::io::stdout();

        let mut in_handle = stdin.lock();
        let mut out_handle = stdout.lock();

        let mut forth = ToyForth::new();

        forth.repl(prompt, &mut in_handle, &mut out_handle)
    }

    pub fn repl(&mut self, prompt: &str, r: &'tf mut dyn std::io::BufRead, w: &'tf mut dyn std::io::Write) -> Result<(),ForthError> {
        // let mut line = String::new();

        let old_in  = std::mem::replace(&mut self.in_stream, Some(r));
        let old_out = std::mem::replace(&mut self.out_stream, Some(w));

        // TODO:
        //   1) Replace REPL loop with Forth code.  This should bootstrap the interpreter
        //      and call QUIT.
        //
        //   2) Integrate IO into ToyForth.
        //
        //   3) Allow different input sources (eg: files)
        //
        loop {
            self.write_prompt(prompt)?;
            self.builtin_refill()?;

            /*
            line.clear();
            r.read_line(&mut line)?;
            // println!("line is: {}", line);
            */

            if self.input.is_empty() {
                break
            }

            let ret = self.builtin_interpret();

            if let Err(err) = ret {
                println!("error: {:?}", err);
            }
        }

        self.in_stream  = old_in;
        self.out_stream = old_out;

        return Ok(());
    }

    pub fn here(&self) -> u32 {
        return self.code.len() as u32;
    }

    pub fn char_here(&self) -> u32 {
        return self.strings.len() as u32;
    }

    pub fn stack_depth(&self) -> usize {
        return self.dstack.len();
    }

    pub fn rstack_depth(&self) -> usize {
        return self.rstack.len();
    }

    pub fn code_size(&self) -> u32 {
        return self.code.len() as u32;
    }

    // should only be called internally during dictionary bootstrap
    fn add_prim(&mut self, word: &str, prim: Primitive) -> XT {
        self.add_primitive(word,prim).unwrap()
    }

    pub fn add_primitive(&mut self, word: &str, prim: Primitive) -> Result<XT,ForthError> {
        let st = self.push_string(word)?;

        let xt = self.mark_cell();
        self.push_cell(Instr::Prim(prim));
        self.push_cell(Instr::Unnest);

        self.dict.push(DictEntry{
            st: st,
            xt: xt,
            flags: DictEntry::PRIMITIVE,
        });

        Ok(xt)
    }

    fn add_func(&mut self, word: &str, func: fn (&mut ToyForth<'tf>) -> Result<(),ForthError>) -> XT {
        self.add_function(word,func).unwrap()
    }

    pub fn add_function(&mut self, word: &str, func: fn (&mut ToyForth<'tf>) -> Result<(),ForthError>) -> Result<XT,ForthError> {
        self.push_string(word)?;
        let func_ind = self.ufuncs.len();

        if func_ind > 0xffff_ffff {
            return Err(ForthError::FunctionSpaceOverflow);
        }

        self.ufuncs.push(ForthFunc(func));
        let xt = self.add_primitive(word, Primitive::Func(func_ind as u32))?;
        Ok(xt)
    }

    pub fn add_word(&mut self, word: &str, code: &[Instr]) -> Result<XT,ForthError> {
        let xt = self.mark_cell();
        for instr in code {
            self.push_cell(*instr);
        }

        self.define_word(word,xt)?;
        Ok(xt)
    }

    pub fn define_word(&mut self, word: &str, xt: XT) -> Result<ST,ForthError> {
        let st = self.push_string(word)?;

        self.dict.push(DictEntry{
            st: st,
            xt: xt,
            flags: 0,
        });

        return Ok(st);
    }

    pub fn lookup_word(&self, word: &str) -> Result<XT, ForthError> {
        for ent in self.dict.iter().rev() {
            let entry_word = self.maybe_string_at(ent.st)?;
            if word.eq_ignore_ascii_case(entry_word) {
                return Ok(ent.xt);
            }
        }

        return Err(ForthError::StringNotFound);
    }

    pub fn allocate_cells(&mut self, count: usize) -> (XT, &mut [Instr]) {
        let ind = self.code.len();

        if ind+count > XT::MAX as usize {
            // XXX: handle with panic?
            panic!("allocation exceeds forth maximum dictionary size");
        }

        let xt = XT(ind as u32);
        self.code.resize(ind + count, Instr::Empty);

        return (xt, &mut self.code[ind..]);
    }

    pub fn mark_cell(&self) -> XT {
        let ind = self.code.len();

        if ind >= XT::MAX as usize {
            // XXX: handle with panic?
            panic!("marker at maximum dictionary size");
        }

        return XT(ind as u32);
    }

    pub fn push_cell(&mut self, code: Instr) -> XT {
        let ind = self.code.len();

        if ind >= XT::MAX as usize {
            // XXX: handle with panic?
            panic!("cell at maximum dictionary size");
        }

        self.code.push(code);

        return XT(ind as u32);
    }

    pub fn add_code(&mut self, code: &[Instr]) -> XT {
        let (xt, cells) = self.allocate_cells(code.len());
        cells.copy_from_slice(code);
        return xt;
    }

    fn set_tmp_str(dest: &mut [u8;256], src: &str) -> Result<u8, ForthError> {
        let b = src.as_bytes();
        let blen = b.len();

        if blen > dest.len() {
            return Err(ForthError::StringTooLong);
        }

        &dest[..blen].copy_from_slice(b);

        return Ok(blen as u8);
    }

    fn pad_str(&mut self, s: &str) -> Result<ST,ForthError> {
        let len = ToyForth::set_tmp_str(&mut self.pad, s)?;
        return Ok(ST::pad_space(0, len));
    }

    fn word_str(&mut self, s: &str) -> Result<ST,ForthError> {
        let len = ToyForth::set_tmp_str(&mut self.word, s)?;
        return Ok(ST::word_space(0, len));
    }

    fn push_str(strings: &mut std::vec::Vec<u8>, s: &str) -> Result<ST,ForthError> {
        let b = s.as_bytes();

        if b.len() > MAX_STRING_LENGTH {
            return Err(ForthError::StringTooLong);
        }

        let blen = b.len() as u8;
        let off = strings.len();

        // FIXME: check string size!
        if off > ST::MAX as usize {
            // XXX: handle with panic?
            panic!("allocation exceeds forth maximum string pool size");
        }

        // strings.push(blen);
        strings.extend_from_slice(b);
        strings.push(0);

        return Ok(ST::allocated_space(off as u32, blen))
    }

    pub fn push_string(&mut self, s: &str) -> Result<ST,ForthError> {
        ToyForth::push_str(&mut self.strings, s)
    }

    pub fn bytes_at(&self, st: ST) -> &[u8] {
        match st {
            ST::Allocated(val) => {
                let len = (val&0xff) as usize;
                let off = (val >> 8) as usize;

                if off >= self.strings.len() {
                    panic!("invalid string token");
                }

                let ind0 = off;
                let ind1 = off + len;

                if ind1 > self.strings.len() {
                    panic!("invalid allocated string token");
                }

                &self.strings[ind0..ind1]
            },
            ST::PadSpace(loc) => {
                let i0 = loc.off as usize;
                let i1 = (loc.off + loc.len) as usize;

                if i0 >= self.pad.len() || i1 > self.pad.len() {
                    panic!("invalid PAD string token");
                }

                &self.pad[i0..i1]
            },
            ST::WordSpace(loc) => {
                let i0 = loc.off as usize;
                let i1 = (loc.off + loc.len) as usize;

                if i0 >= self.word.len() || i1 > self.word.len() {
                    panic!("invalid PAD string token");
                }

                &self.word[i0..i1]
            },
            ST::InputSpace(loc) => {
                let i0 = loc.off as usize;
                let i1 = (loc.off + loc.len) as usize;

                if i0 > self.input.len() || i1 > self.input.len() {
                    panic!("invalid input string token");
                }

                &self.input[i0..i1].as_bytes()
            },
        }
    }

    pub fn maybe_string_at(&self, st: ST) -> Result<&str, ForthError> {
        return std::str::from_utf8(self.bytes_at(st)).map_err(|_| ForthError::InvalidString(st));
    }

    pub fn string_at(&self, st: ST) -> &str {
        return std::str::from_utf8(self.bytes_at(st)).unwrap();
    }

    pub fn push(&mut self, w: Word) -> Result<(), ForthError> {
        self.dstack.push(w);
        Ok(())
    }

    pub fn push_int(&mut self, v: i32) -> Result<(), ForthError> {
        self.push(Word::int(v))
    }

    fn drop(&mut self) -> Result<(), ForthError> {
        if let Some(_) = self.dstack.pop() {
            Ok(())
        } else {
            Err(ForthError::StackUnderflow)
        }
    }

    fn dup(&mut self) -> Result<(), ForthError> {
        let w = self.peek().ok_or(ForthError::StackUnderflow)?;
        self.push(w)?;
        Ok(())
    }

    fn swap(&mut self) -> Result<(), ForthError> {
        let len = self.dstack.len();
        if len >= 2 {
            self.dstack[..].swap(len-2,len-1);
            Ok(())
        } else {
            Err(ForthError::StackUnderflow)
        }
    }

    fn math(&mut self, op: u8) -> Result<(),ForthError> {
        let op1 = self.pop_kind();
        let op2 = self.pop_kind();

        if let None = op1 {
            return Err(ForthError::StackUnderflow);
        }

        if let None = op2 {
            return Err(ForthError::StackUnderflow);
        }

        if let (Some(WordKind::Int(b)), Some(WordKind::Int(a))) = (op1,op2) {
            match op {
                MATH_PLUS  => { self.push(Word::int(a+b))?; },
                MATH_MINUS => { self.push(Word::int(a-b))?; },
                MATH_STAR  => { self.push(Word::int(a*b))?; },
                MATH_SLASH => {
                    if b != 0 {
                        self.push(Word::int(a/b))?;
                    } else {
                        return Err(ForthError::DivisionByZero);
                    }
                },
                _ => {
                    return Err(ForthError::InvalidOperation);
                }
            }

            return Ok(());
        } else {
            return Err(ForthError::InvalidArgument);
        }
    }

    fn input_eol(&mut self) -> Result<(), ForthError> {
        let ilen = self.input.len();
        if ilen > Word::INT_MAX as usize {
            return Err(ForthError::NumberOutOfRange);
        }

        self.push(Word::int(ilen as i32))?;
        Ok(())
    }

    fn builtin_find(&mut self) -> Result<(), ForthError> {
        let st = self.pop_str()?;
        let s = self.maybe_string_at(st)?;

        match self.lookup_word(s) {
            Ok(xt) => {
                self.push(Word::from_xt(xt))?;
                self.push(Word::int(1))?;
                Ok(())
            },
            Err(ForthError::StringNotFound) => {
                self.push(st.to_word())?;
                self.push(Word::int(0))?;
                Ok(())
            },
            Err(err) => {
                Err(err)
            }
        }
    }

    fn builtin_to_number(&mut self) -> Result<(), ForthError> {
        let base : u32 = 10; // FIXME!

        let arg_len = self.pop_int()?;
        // eprintln!("arg_len = {}",arg_len);

        if arg_len < 0 {
            return Err(ForthError::InvalidArgument);
        }

        let st  = self.pop_str()?;
        // eprintln!("st = {:?}",st);
        let v0 = self.pop_int()?;
        // eprintln!("v0 = {:?}",v0);

        if v0 < 0 {
            return Err(ForthError::InvalidArgument);
        }

        let bytes = self.bytes_at(st);
        let len = std::cmp::min(arg_len as usize, bytes.len());

        // eprintln!("bytes = {:?}, len = {}, arg_len = {}, bytes.len() = {}",
        //     bytes,len, arg_len, bytes.len());

        let mut val = v0 as u32;

        let mut consumed : u32 = 0;
        for (_i,dig) in bytes[..len].iter().enumerate() {
            // eprintln!("[{:3}] dig = {}", i, dig);
            let ch = (*dig as char).to_ascii_lowercase();

            let dig_val : i32 = 
                if ch >= '0' && ch <= '9' {
                    let delta = (ch as u8) - ('0' as u8);
                    delta as i32
                } else if ch >= 'a' && ch <= 'z' {
                    let delta = (ch as u8) - ('a' as u8);
                    (delta as i32) + 10
                } else {
                    -1
                };

            if dig_val < 0 || dig_val >= (base as i32) {
                break;
            }

            // TODO: check for u32 overflow!
            val = val * base + (dig_val as u32);
            consumed += 1;
        }

        if consumed > 0xff {
            return Err(ForthError::StringTooLong);
        }

        // eprintln!("val = {}, st = {:?}, consumed = {}", val, st.offset(consumed as u8), consumed);

        // TODO: check for word overflow!
        self.push_int(val as i32)?;
        self.push(st.offset(consumed as u8).to_word())?;
        self.push_int(consumed as i32)?;

        Ok(())
    }

    fn lookup_bye(&self) -> Result<XT,ForthError> {
        // BYE always at word 0.
        Ok(XT(0))
    }

    fn ret_push_bye(&mut self) -> Result<(),ForthError> {
        let bye_xt = self.lookup_bye()?;
        self.rstack.push(bye_xt.to_word());
        Ok(())
    }

    fn builtin_immediate(&mut self) -> Result<(),ForthError> {
        Err(ForthError::Unimplemented)
    }

    fn builtin_execute(&mut self) -> Result<(),ForthError> {
        let xt = self.pop_xt()?;
        self.ret_push_bye()?;
        self.exec(xt)
    }

    fn input_lookup(&mut self) -> Result<(), ForthError> {
        let i1 = self.pop_int()?;
        let i0 = self.pop_int()?;

        // TODO: bounds checks?
        let s = &self.input[i0 as usize..i1 as usize];
        match self.lookup_word(s) {
            Ok(xt) => {
                self.push(Word::from_xt(xt))?;
                Ok(())
            },
            Err(err) => {
                Err(err)
            }
        }
    }

    fn defstr(&mut self) -> Result<(), ForthError> {
        let i1 = self.pop_int()?;
        let i0 = self.pop_int()?;

        // TODO: bounds checks?
        let s = &self.input[i0 as usize..i1 as usize];
        match ToyForth::push_str(&mut self.strings, s) {
            Ok(st) => {
                self.push(Word::from_str(st))?;
                Ok(())
            },
            Err(err) => {
                Err(err)
            }
        }
    }

    fn defword(&mut self) -> Result<(), ForthError> {
        let xt = self.pop_xt()?;
        let st = self.pop_str()?;

        self.dict.push(DictEntry{
            st: st,
            xt: xt,
            flags: 0,
        });

        Ok(())
    }

    fn pop_delim(&mut self) -> Result<u8, ForthError> {
        match self.pop_kind() {
            Some(WordKind::Int(v)) => {
                if v > 0 && v < 256 {
                    return Ok(v as u8);
                }

                return Err(ForthError::InvalidDelimiter(v));
            },
            Some(_) => {
                return Err(ForthError::InvalidArgument);
            },
            None => {
                return Err(ForthError::StackUnderflow);
            }
        }
    }

    fn scan_delim(bytes: &[u8], delim: u8, expect: bool) -> usize {
        bytes.iter().enumerate().find(
            |(_loc,ch)| (**ch == delim) == expect
        ).map_or(bytes.len(), |(loc,_)| loc as usize)
    }

    fn scan_word(bytes: &[u8], delim: u8) -> (usize,usize) {
        let i0 = ToyForth::scan_delim(bytes, delim, false);
        let i1 = ToyForth::scan_delim(&bytes[i0..], delim, true);

        return (i0,i0+i1);
    }

    fn builtin_dot(&mut self) -> Result<(), ForthError> {
        let w = self.pop().ok_or(ForthError::StackUnderflow)?;

        if let Some(out) = &mut self.out_stream {
            use std::io::Write;
            write!(out, "{}\n", w)?;
            out.flush()?;
        }

        Ok(())
    }

    fn builtin_char(&mut self) -> Result<(), ForthError> {
        let (w0,w1) = ToyForth::scan_word(&self.input[self.input_off..].as_bytes(), ' ' as u8);

        let off = self.input_off+w0;
        let end = self.input_off+w1;

        // TODO: replace with u32::MAX when supported
        if end > 0xffff_ffff {
            return Err(ForthError::StringTooLong);
        }

        self.input_off = end;

        if end > off {
            self.push_int(self.input.as_bytes()[off] as i32)?;
            Ok(())
        } else {
            Err(ForthError::InvalidEmptyString)
        }
    }

    fn builtin_word(&mut self) -> Result<(), ForthError> {
        let delim = self.pop_delim()?;

        let (w0,w1) = ToyForth::scan_word(&self.input[self.input_off..].as_bytes(), delim);

        let word_off = self.input_off+w0;
        let word_end = self.input_off+w1;

        self.input_off = word_end;

        let len = word_end - word_off;
        let off = word_off;

        if len > 255 {
            return Err(ForthError::StringTooLong);
        }

        // TODO: Handle large offset by copying to word space?
        if off > 255 {
            return Err(ForthError::StringTooLong);
        }

        self.push(ST::input_space(off as u8,len as u8).to_word())?;
        Ok(())
    }

    // nb: pop is only called from rust, so it's not a forth primitive
    pub fn pop(&mut self) -> Option<Word> {
        self.dstack.pop()
    }

    // nb: pop is only called from rust, so it's not a forth primitive
    pub fn peek(&mut self) -> Option<Word> {
        self.dstack.last().map(|x| *x)
    }

    fn pop_int(&mut self) -> Result<i32, ForthError> {
        let v = self.pop_kind().ok_or(ForthError::StackUnderflow)?;
        if let WordKind::Int(x) = v {
            Ok(x)
        } else {
            Err(ForthError::InvalidArgument)
        }
    }

    fn pop_str(&mut self) -> Result<ST,ForthError> {
        let v = self.pop_kind().ok_or(ForthError::StackUnderflow)?;
        if let WordKind::Str(st) = v {
            Ok(st)
        } else {
            Err(ForthError::InvalidArgument)
        }
    }

    fn pop_xt(&mut self) -> Result<XT,ForthError> {
        let v = self.pop_kind().ok_or(ForthError::StackUnderflow)?;
        if let WordKind::XT(xt) = v {
            Ok(xt)
        } else {
            Err(ForthError::InvalidArgument)
        }
    }

    fn pop_kind(&mut self) -> Option<WordKind> {
        self.dstack.pop().map(Word::kind)
    }

    pub fn exec(&mut self, xt: XT) -> Result<(), ForthError> {
        // TODO: bounds check

        let mut pc = xt.0;

        loop {
            let op = self.code[pc as usize];
            // eprintln!("pc = {}, code[pc] = {:?}", pc, op);
            match op {
                // Instr::Empty | Instr::Special() | Instr::Char{..} | Instr::Data(_) => {
                Instr::Empty | Instr::Special() | Instr::Data(_) => {
                    return Err(ForthError::InvalidCell(XT(pc)));
                },
                Instr::Prim(Primitive::Bye) => {
                    return Ok(());
                },
                Instr::Prim(Primitive::Push(w)) => {
                    self.push(w)?;
                    pc += 1;
                },
                Instr::Prim(Primitive::Drop) => {
                    self.drop()?;
                    pc += 1;
                },
                Instr::Prim(Primitive::Dup) => {
                    self.dup()?;
                    pc += 1;
                },
                Instr::Prim(Primitive::Swap) => {
                    self.swap()?;
                    pc += 1;
                },
                Instr::Prim(Primitive::Math{op}) => {
                    self.math(op)?;
                    pc += 1;
                },
                Instr::Prim(Primitive::EOL) => {
                    self.input_eol()?;
                    pc += 1;
                },
                Instr::Prim(Primitive::Lookup) => {
                    self.input_lookup()?;
                    pc += 1;
                },
                Instr::Prim(Primitive::DefStr) => {
                    self.defstr()?;
                    pc += 1;
                },
                Instr::Prim(Primitive::DefWord) => {
                    self.defword()?;
                    pc += 1;
                },

                Instr::Prim(Primitive::Func(x)) => {
                    let ind = x as usize;
                    if ind >= self.ufuncs.len() {
                        return Err(ForthError::InvalidFunction(x));
                    }

                    let fxn = self.ufuncs[ind].0;

                    fxn(self)?;
                    pc += 1;
                },

                Instr::DoCol(new_pc) => {
                    self.rstack.push(Word::xt(pc+1));
                    pc = new_pc.0;
                },
                Instr::Execute => {
                    let xt = self.pop_xt()?;
                    self.rstack.push(Word::xt(pc+1));
                    pc = xt.0;
                },
                Instr::Unnest => {
                    let val = self.rstack.pop().ok_or(ForthError::ReturnStackUnderflow)?;
                    let ret = val.to_xt().ok_or_else(|| ForthError::InvalidExecutionToken(val))?;
                    pc = ret.0;
                },
            }
        }
    }

    fn process_token(&mut self, tok: LexToken) -> Result<(), String> {
        println!("token: {} source: {}", tok.token, tok.source);
        if let Token::Ident(_id) = tok.token {
            /*
            match self.lookup_ident(id) {
                Builtin(fxn) => {
            }
            */
        } else {
            let _data = Data::from_token(tok)?;
            // self.data_stack.push(data);
        }
        Ok(())
    }

    fn parse<'a>(&mut self, line: &'a str) -> Result<(), LexError1<'a>> {
        for tok_or_err in tokenize(line) {
            let tok = tok_or_err?;
            if let Err(s) = self.process_token(tok) {
                eprintln!("error: {}", s);
            }
        }

        return Ok(());
    }
}

/*
impl std::fmt::Debug for PrimFunc {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut name = 
            if self == &PRIM_PUSH { "push" }
            else if self == &PRIM_DROP { "drop" }
            else if self == &PRIM_SWAP { "swap" }
            else if self == &PRIM_STOP{ "stop" }
            else if self == &PRIM_MATH{ "math" }
            else if self == &PRIM_EOL{ "eol" }
            else if self == &PRIM_LOOKUP{ "lookup" }
            else if self == &PRIM_DEFSTR{ "defstr" }
            else if self == &PRIM_DEFWORD{ "defword" }
            else { "unknown" };

        fmt.write_fmt(format_args!("PrimFunc[{}]", name))
    }
}
*/

impl std::fmt::Display for Token {
    fn fmt(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Token::Str(s) => { formatter.write_fmt(format_args!("STR \"{}\"", s)) },
            Token::Integer(i) => { formatter.write_fmt(format_args!("INT \"{}\"", i)) },
            Token::Float(f) => { formatter.write_fmt(format_args!("FLT \"{}\"", f)) },
            Token::Ident(id) => { formatter.write_fmt(format_args!("ID \"{}\"", id)) },
        }
    }
}

fn repl(prompt: &str, r: &mut dyn std::io::BufRead, w: &mut dyn std::io::Write) -> std::io::Result<()> {
    let mut line = String::new();

    let mut forth = ToyForth::new();

    loop {
        write!(w, "{}", prompt)?;
        w.flush()?;

        line.clear();
        r.read_line(&mut line)?;
        // println!("line is: {}", line);

        if line.is_empty() {
            break
        }

        if let Err(_err) = forth.parse(&line) {
            println!("error");
        } else {
            // print top of stack
        }
    }

    return Ok(());
}

fn main() {
    let ret = ToyForth::std_repl();
    if let Err(err) = ret {
        // FIXME: replace {:?} with a proper formatter
        println!("Error encountered: {:?}", err);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn token_as_num() {
        let v1 = "123";
        assert_eq!(LexToken::parse_num(&v1), Ok(LexToken::int(123, v1)));
        assert_ne!(LexToken::parse_num(&v1), Ok(LexToken::int(456, v1)));

        let v2 = "123.45";
        assert_eq!(LexToken::parse_num(&v2), Ok(LexToken::flt(123.45, v2)));

        let v3 = "+999";
        assert_eq!(LexToken::parse_num(&v3), Ok(LexToken::int(999, v3)));
    }

    #[test]
    fn token_as_str() {
        let v1 = "foo";
        assert_eq!(LexToken::str("foo",&v1), LexToken{token:Token::Str(v1.to_string()), source:v1});
    }

    #[test]
    fn token_as_ident() {
        let v1 = "foo";
        assert_eq!(LexToken::ident(&v1), LexToken{token:Token::Ident(v1.to_string()), source:v1});
    }

    #[test]
    fn tokens() {
        let s = "foo \"bar\" 123";
        let toks: Vec<LexToken> = tokenize(s).map(|x| x.unwrap()).collect();
        assert_eq!(toks, vec![ LexToken::ident(&s[0..3]), LexToken::str("bar", &s[5..8]), LexToken::int(123,&s[10..]) ]);
    }

    #[test]
    fn num_tokens() {
        let s = "+123 -456 12.50";
        let toks: Vec<LexToken> = tokenize(s).map(|x| x.unwrap()).collect();
        assert_eq!(toks, vec![ LexToken::int(123,&s[0..4]), LexToken::int(-456,&s[5..9]), LexToken::flt(12.50,&s[10..]) ]);
    }

    #[test]
    fn esc_strings() {
        let s = "\"foo\\n\" \"bar\\\"baz\\\"quux\" \"X\\r\\nY\"";
        let toks: Vec<LexToken> = tokenize(s).map(|x| x.unwrap()).collect();
        assert_eq!(toks, vec![
           LexToken::str("foo\n", &s[1..6]),
           LexToken::str("bar\"baz\"quux", &s[9..23]),
           LexToken::str("X\r\nY", &s[26..32])
        ]);
    }

    #[test]
    fn invalid_tokens() {
        let s = "+123a \\foo foo\\bar 12.5.0 \"unending";
        let toks: Vec<Result<LexToken,LexError1>> = tokenize(s).collect();
        assert_eq!(toks, vec![ 
            Err(LexError1{ error: LexErrorType::InvalidNumber, source: &s[0..5] }),
            Err(LexError1{ error: LexErrorType::InvalidIdent, source: &s[6..10] }),
            Err(LexError1{ error: LexErrorType::InvalidIdent, source: &s[11..18] }),
            Err(LexError1{ error: LexErrorType::InvalidNumber, source: &s[19..25] }),
            Err(LexError1{ error: LexErrorType::UnterminatedString, source: &s[27..] }),
        ]);
    }

    #[test]
    fn words() {
        assert_eq!(Word::int(123).to_int().unwrap(), 123);
        assert_eq!(Word::int(-123).to_int().unwrap(), -123);

        assert_eq!(Word::xt(123).to_xt().unwrap(), XT(123));

        assert_eq!(Word::str(((123 as u32)<<8) | 10).to_str().unwrap(), ST::allocated_space(123, 10));

        assert_eq!(Word::xt(123).to_int(), None);
        assert_eq!(Word::xt(123).to_str(), None);

        assert_eq!(Word::str(123).to_int(), None);
        assert_eq!(Word::str(123).to_xt(), None);

        assert_eq!(Word::int(123).to_xt(), None);
        assert_eq!(Word::int(123).to_str(), None);

        assert_eq!(Word::int(-123).to_xt(), None);
        assert_eq!(Word::int(-123).to_str(), None);
    }

    #[test]
    fn stack_prims() {
        let mut forth = ToyForth::new();
        forth.push(Word::int( 123)).unwrap();
        forth.push(Word::int(-123)).unwrap();
        assert_eq!(forth.pop().unwrap(), Word::int(-123));
        assert_eq!(forth.pop().unwrap(), Word::int( 123));

        forth.push(Word::int( 123)).unwrap();
        forth.push(Word::int(-123)).unwrap();
        forth.swap().unwrap();
        assert_eq!(forth.pop().unwrap(), Word::int( 123));
        assert_eq!(forth.pop().unwrap(), Word::int(-123));

        forth.push(Word::int( 123)).unwrap();
        forth.dup().unwrap();
        assert_eq!(forth.pop().unwrap(), Word::int(123));
        assert_eq!(forth.pop().unwrap(), Word::int(123));
    }

    #[test]
    fn can_allocate_entries() {
        let mut forth = ToyForth::new();

        let (_xt,entries) = forth.allocate_cells(4);
        assert_eq!(entries.len(), 4);
    }

    #[test]
    fn can_add_string() {
        let mut forth = ToyForth::new();
        let base = forth.char_here();

        let st1 = forth.push_string("string1").unwrap();
        let st2 = forth.push_string("string2").unwrap();

        assert_eq!(forth.string_at(st1), "string1");
        assert_eq!(forth.string_at(st2), "string2");

        assert_eq!(ST::allocated_space(base+0, 7), st1);
        assert_eq!(ST::allocated_space(base+8, 7), st2);

        assert_eq!(st1.to_word().kind(), WordKind::Str(st1));
        assert_eq!(st2.to_word().kind(), WordKind::Str(st2));
    }

    #[test]
    fn run_stack_manip() {
        let mut forth = ToyForth::new();

        let code = vec![
            Instr::Prim(Primitive::Push(Word::int(4314))),
            Instr::Prim(Primitive::Push(Word::int(-132))),
            Instr::Prim(Primitive::Push(Word::int(-999))),
            Instr::Prim(Primitive::Swap),
            Instr::Prim(Primitive::Drop),
            Instr::Prim(Primitive::Bye),
        ];

        let xt = forth.add_code(&code);

        forth.exec(xt).unwrap();
        assert_eq!(forth.pop().unwrap(), Word::int(-999));
        assert_eq!(forth.pop().unwrap(), Word::int(4314));
        assert_eq!(forth.pop(), None);
    }

    #[test]
    fn run_arith() {
        let mut forth = ToyForth::new();

        let code = vec![
            Instr::Prim(Primitive::Push(Word::int(4314))),
            Instr::Prim(Primitive::Push(Word::int(-132))),
            Instr::Prim(Primitive::Math{op:MATH_PLUS}),
            Instr::Prim(Primitive::Push(Word::int(-10))),
            Instr::Prim(Primitive::Math{op:MATH_STAR}),
            Instr::Prim(Primitive::Bye),
        ];

        let xt = forth.add_code(&code);
        forth.exec(xt).unwrap();

        assert_eq!(forth.pop().unwrap(), Word::int(-41820));
        assert_eq!(forth.pop(), None);
    }

    #[test]
    fn run_dictionary_entry() {
        let mut forth = ToyForth::new();

        let (xt0,entries) = forth.allocate_cells(5);

        assert_eq!(entries.len(), 5);

        /* f(x) = 2*x + 1 */
        entries[0] = Instr::Prim(Primitive::Push(Word::int(2)));
        entries[1] = Instr::Prim(Primitive::Math{op:MATH_STAR});
        entries[2] = Instr::Prim(Primitive::Push(Word::int(1)));
        entries[3] = Instr::Prim(Primitive::Math{op:MATH_PLUS});
        entries[4] = Instr::Unnest;

        let xt1 = forth.add_code(&vec![
            Instr::Prim(Primitive::Push(Word::int(2))),
            Instr::DoCol(xt0),
            Instr::Prim(Primitive::Bye),
        ]);

        forth.exec(xt1).unwrap();
        assert_eq!(forth.pop().unwrap(), Word::int(5));
        assert_eq!(forth.pop(), None);
    }

    #[test]
    fn can_define() {
        let mut forth = ToyForth::new();

        let (xt,entries) = forth.allocate_cells(5);
        assert_eq!(entries.len(), 5);

        /* f(x) = 2*x + 1 */
        entries[0] = Instr::Prim(Primitive::Push(Word::int(2)));
        entries[1] = Instr::Prim(Primitive::Math{op:MATH_STAR});
        entries[2] = Instr::Prim(Primitive::Push(Word::int(1)));
        entries[3] = Instr::Prim(Primitive::Math{op:MATH_PLUS});
        entries[4] = Instr::Unnest;

        forth.define_word("my_func", xt).unwrap();

        let lookup_xt = forth.lookup_word("my_func").unwrap();
        assert_eq!(xt, lookup_xt);
    }

    #[test]
    fn can_define_incrementally() {
        let mut forth = ToyForth::new();

        let xt = forth.mark_cell();

        /* f(x) = 2*x + 1 */
        forth.push_cell(Instr::Prim(Primitive::Push(Word::int(2))));
        forth.push_cell(Instr::Prim(Primitive::Math{op:MATH_STAR}));
        forth.push_cell(Instr::Prim(Primitive::Push(Word::int(1))));
        forth.push_cell(Instr::Prim(Primitive::Math{op:MATH_PLUS}));
        forth.push_cell(Instr::Unnest);

        forth.define_word("my_func", xt).unwrap();

        let lookup_xt = forth.lookup_word("my_func").unwrap();
        assert_eq!(xt, lookup_xt);

        let immed = forth.mark_cell();

        forth.push_cell(Instr::Prim(Primitive::Push(Word::int(0))));
        forth.push_cell(Instr::Prim(Primitive::EOL));
        forth.push_cell(Instr::Prim(Primitive::Lookup));
        forth.push_cell(Instr::Prim(Primitive::Bye));

        forth.input.push_str("my_func");
        forth.exec(immed).unwrap();

        assert_eq!(forth.pop().unwrap(), Word::from_xt(xt));
        assert_eq!(forth.pop(), None);
    }

    #[test]
    fn can_define_word_from_input() {
        let mut forth = ToyForth::new();

        let xt = forth.mark_cell();

        /* f(x) = 2*x + 1 */
        forth.push_cell(Instr::Prim(Primitive::Push(Word::int(2))));
        forth.push_cell(Instr::Prim(Primitive::Math{op:MATH_STAR}));
        forth.push_cell(Instr::Prim(Primitive::Push(Word::int(1))));
        forth.push_cell(Instr::Prim(Primitive::Math{op:MATH_PLUS}));
        forth.push_cell(Instr::Unnest);

        forth.input.push_str("my_func");

        {
            let immed = forth.mark_cell();
            forth.push_cell(Instr::Prim(Primitive::Push(Word::int(0))));
            forth.push_cell(Instr::Prim(Primitive::EOL));
            forth.push_cell(Instr::Prim(Primitive::DefStr));
            forth.push_cell(Instr::Prim(Primitive::Push(Word::from_xt(xt))));
            forth.push_cell(Instr::Prim(Primitive::DefWord));
            forth.push_cell(Instr::Prim(Primitive::Bye));

            forth.exec(immed).unwrap();
        }

        {
            let immed = forth.mark_cell();

            forth.push_cell(Instr::Prim(Primitive::Push(Word::int(0))));
            forth.push_cell(Instr::Prim(Primitive::EOL));
            forth.push_cell(Instr::Prim(Primitive::Lookup));
            forth.push_cell(Instr::Prim(Primitive::Bye));

            forth.exec(immed).unwrap();
        }

        assert_eq!(forth.pop().unwrap(), Word::from_xt(xt));
        assert_eq!(forth.pop(), None);
    }

    #[test]
    fn builtin_word_scans_words() {
        let mut forth = ToyForth::new();

        forth.input.push_str("  x  test foo bar   ");
        forth.input_off = 0;

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 3);
        assert_eq!(forth.pop().unwrap(), Word::from_str(ST::input_space(2,1)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 9);
        assert_eq!(forth.pop().unwrap(), Word::from_str(ST::input_space(5,4)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 13);
        assert_eq!(forth.pop().unwrap(), Word::from_str(ST::input_space(10,3)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 17);
        assert_eq!(forth.pop().unwrap(), Word::from_str(ST::input_space(14,3)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 20);
        let pk = forth.peek().unwrap();
        eprintln!("last word is {:?} - {} - {:b}", pk, pk, pk.0);
        assert_eq!(forth.pop().unwrap(), ST::input_space(20,0).to_word());

        // make sure we can search again and it's well behaved...
        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 20);
        let pk = forth.peek().unwrap();
        eprintln!("last word is {:?} - {} - {:b}", pk, pk, pk.0);
        assert_eq!(forth.pop().unwrap(), ST::input_space(20,0).to_word());
    }

    #[test]
    fn builtin_char_scans_first_char_of_words() {
        let mut forth = ToyForth::new();

        forth.input.push_str("  x  test foo bar   ");
        forth.input_off = 0;

        forth.builtin_char().unwrap();
        assert_eq!(forth.input_off, 3);
        assert_eq!(forth.pop_int().unwrap(), 'x' as i32);

        forth.builtin_char().unwrap();
        assert_eq!(forth.input_off, 9);
        assert_eq!(forth.pop_int().unwrap(), 't' as i32);

        forth.builtin_char().unwrap();
        assert_eq!(forth.input_off, 13);
        assert_eq!(forth.pop_int().unwrap(), 'f' as i32);

        forth.builtin_char().unwrap();
        assert_eq!(forth.input_off, 17);
        assert_eq!(forth.pop_int().unwrap(), 'b' as i32);

        // out of words, make sure this is an error!
        assert!(matches!(forth.builtin_char().unwrap_err(), ForthError::InvalidEmptyString));
        assert_eq!(forth.input_off, 20);
        assert_eq!(forth.stack_depth(), 0);

        // make sure we can search again and it's well behaved...
        assert!(matches!(forth.builtin_char().unwrap_err(), ForthError::InvalidEmptyString));
        assert_eq!(forth.input_off, 20);
        assert_eq!(forth.stack_depth(), 0);
    }

    #[test]
    fn builtin_find_finds_words() {
        let mut forth = ToyForth::new();

        forth.input.push_str("  x  test foo bar   ");
        forth.input_off = 0;

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 3);
        assert_eq!(forth.pop().unwrap(), Word::from_str(ST::input_space(2,1)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 9);
        assert_eq!(forth.pop().unwrap(), Word::from_str(ST::input_space(5,4)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 13);
        assert_eq!(forth.pop().unwrap(), Word::from_str(ST::input_space(10,3)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 17);
        assert_eq!(forth.pop().unwrap(), Word::from_str(ST::input_space(14,3)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 20);
        let pk = forth.peek().unwrap();
        eprintln!("last word is {:?} - {} - {:b}", pk, pk, pk.0);
        assert_eq!(forth.pop().unwrap(), ST::input_space(20,0).to_word());

        // make sure we can search again and it's well behaved...
        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 20);
        let pk = forth.peek().unwrap();
        eprintln!("last word is {:?} - {} - {:b}", pk, pk, pk.0);
        assert_eq!(forth.pop().unwrap(), ST::input_space(20,0).to_word());
    }

    #[test]
    fn can_lookup_token() {
        let mut forth = ToyForth::new();

        let xt = forth.add_word("my_func", &vec![
           Instr::Prim(Primitive::Push(Word::int(2))),
           Instr::Prim(Primitive::Math{op:MATH_STAR}),
           Instr::Prim(Primitive::Push(Word::int(1))),
           Instr::Prim(Primitive::Math{op:MATH_PLUS}),
           Instr::Unnest,
        ]).unwrap();

        // look up various things
        let st = forth.pad_str("test").unwrap();
        forth.push(st.to_word()).unwrap();
        eprintln!("stack top: {:?}", forth.peek());
        forth.builtin_find().unwrap();

        assert_eq!(forth.pop_int().unwrap(), 0);
        assert_eq!(forth.pop_kind().unwrap(), WordKind::Str(st));

        let st = forth.pad_str("my_func").unwrap();
        forth.push(st.to_word()).unwrap();
        eprintln!("stack top: {:?}", forth.peek());
        forth.builtin_find().unwrap();

        assert_eq!(forth.pop_int().unwrap(), 1);
        assert_eq!(forth.pop_kind().unwrap(), WordKind::XT(xt));
    }

    #[test]
    fn can_execute_token() {
        let mut forth = ToyForth::new();

        forth.add_word("my_func", &vec![
           Instr::Prim(Primitive::Push(Word::int(2))),
           Instr::Prim(Primitive::Math{op:MATH_STAR}),
           Instr::Prim(Primitive::Push(Word::int(1))),
           Instr::Prim(Primitive::Math{op:MATH_PLUS}),
           Instr::Unnest,
        ]).unwrap();

        forth.push_int(1234).unwrap();

        let st = forth.pad_str("my_func").unwrap();
        forth.push(st.to_word()).unwrap();
        eprintln!("stack top: {:?}", forth.peek());
        forth.builtin_find().unwrap();

        assert_eq!(forth.pop_int().unwrap(), 1);
        forth.builtin_execute().unwrap();
        assert_eq!(forth.pop_int().unwrap(), 2469);
    }

    #[test]
    fn can_define_user_func() {
        let mut forth = ToyForth::new();

        forth.add_function("my_func", |forth: &mut ToyForth| -> Result<(),ForthError> {
            forth.push_int(123)?;
            Ok(())
        }).unwrap();

        forth.interpret("my_func").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 123);
    }

    #[test]
    fn can_interpret_two_words() {
        let mut forth = ToyForth::new();

        forth.add_primitive("ONE", Primitive::Push(Word::int(1))).unwrap();
        forth.add_primitive("TWO", Primitive::Push(Word::int(2))).unwrap();

        forth.interpret("ONE DUP").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), 1);
        assert_eq!(forth.pop_int().unwrap(), 1);
    }

    #[test]
    fn builtin_to_number() {
        let mut forth = ToyForth::new();

        forth.push_int(0).unwrap();
        let st = forth.push_string("123").unwrap();
        forth.push(Word::from_str(st)).unwrap();
        forth.push_int(3).unwrap();
        forth.builtin_to_number().unwrap();

        assert_eq!(forth.stack_depth(), 3);
        assert_eq!(forth.pop_int().unwrap(), 3);
        assert_eq!(forth.pop_str().unwrap(), st.offset(3));
        assert_eq!(forth.pop_int().unwrap(), 123);

        forth.push_int(0).unwrap();
        let st = forth.push_string("54a3").unwrap();
        forth.push(Word::from_str(st)).unwrap();
        forth.push_int(4).unwrap();
        forth.builtin_to_number().unwrap();

        assert_eq!(forth.stack_depth(), 3);
        assert_eq!(forth.pop_int().unwrap(), 2);
        assert_eq!(forth.pop_str().unwrap(), st.offset(2));
        assert_eq!(forth.pop_int().unwrap(), 54);
    }

    #[test]
    fn can_interpret_numbers() {
        let mut forth = ToyForth::new();

        forth.interpret("1 2").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), 2);
        assert_eq!(forth.pop_int().unwrap(), 1);

        forth.interpret("1 2 +").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 3);
    }

}

