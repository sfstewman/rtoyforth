enum Data {
    Int(i32),
    Flt(f32),
    Str(String),
    Ptr(usize),
}

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

#[derive(Debug,PartialEq,Eq,Clone,Copy)]
struct ST(u32);

#[derive(Debug,PartialEq,Eq,Clone,Copy)]
enum WordKind {
    Int(i32),
    XT(XT),
    Str(ST),
}

impl Word {
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

    fn kind(&self) -> WordKind {
        match self.0 {
            x if (x & WORD_HIGH_BIT) == 0 => { WordKind::Int((x | ((x & WORD_SIGN_BIT) << 1)) as i32) },
            x if (x & WORD_SIGN_BIT) == 0 => { WordKind::Str(ST(x & WORD_STR_MASK)) },
            x => { WordKind::XT(XT(x & WORD_XT_MASK)) },
        }
    }

    fn to_int(self) -> Option<i32> {
        if let WordKind::Int(x) = self.kind() { Some(x) } else { None }
    }

    fn to_xt(self) -> Option<XT> {
        if let WordKind::XT(x) = self.kind() { Some(x) } else { None }
    }

    fn to_str(self) -> Option<ST> {
        if let WordKind::Str(x) = self.kind() { Some(x) } else { None }
    }
}

impl std::fmt::Display for Word {
    fn fmt(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.kind() {
            WordKind::Int(x) => { formatter.write_fmt(format_args!("[int] {}", x)) },
            WordKind::XT(XT(x))  => { formatter.write_fmt(format_args!("[xt] {}", x)) },
            WordKind::Str(ST(x))  => { formatter.write_fmt(format_args!("[st] {}", x)) },
        }
    }
}

// type PrimFunc = fn(&mut ToyForth, Word);
struct PrimFunc(fn(&mut ToyForth, Word) -> Result<(),ForthError>);

impl PartialEq for PrimFunc {
    fn eq(&self, other: &PrimFunc) -> bool {
        return (self.0 as usize) == (other.0 as usize)
    }
}

impl Eq for PrimFunc { }



/*
const PRIM_PUSH : u8 = 0;
const PRIM_DROP : u8 = 1;
const PRIM_SWAP : u8 = 2;
const PRIM_STOP : u8 = 3;
*/

#[derive(Debug)]
enum Instr {
    Prim(PrimFunc, Word),
    DoCol(XT, Word),
}

struct ToyForth {
    dstack: Vec<Word>,
    code: Vec<Instr>,
    // rstack: Vec<Word>,
    // names: std::collections::HashMap<String,usize>,
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

const MATH_PLUS  : u32 = 0;
const MATH_MINUS : u32 = 1;
const MATH_STAR  : u32 = 2;
const MATH_SLASH : u32 = 3;

enum ForthError {
    Stop,
    StackUnderflow,
    InvalidOperation,
    InvalidArguments,
    DivisionByZero,
}

impl ToyForth {
    fn new() -> ToyForth {
        let mut tf = ToyForth{
            dstack: Vec::new(),
            code: Vec::new(),
        };

        return tf;
    }

    fn push(&mut self, w: Word) -> Result<(), ForthError> {
        self.dstack.push(w);
        Ok(())
    }

    fn drop(&mut self, _: Word) -> Result<(), ForthError> {
        if let Some(_) = self.dstack.pop() {
            Ok(())
        } else {
            Err(ForthError::StackUnderflow)
        }
    }

    fn swap(&mut self, _: Word) -> Result<(), ForthError> {
        let len = self.dstack.len();
        if len >= 2 {
            self.dstack[..].swap(len-2,len-1);
            Ok(())
        } else {
            Err(ForthError::StackUnderflow)
        }
    }

    fn math(&mut self, op: Word) -> Result<(),ForthError> {
        let op1 = self.popkind();
        let op2 = self.popkind();

        if let None = op1 {
            return Err(ForthError::StackUnderflow);
        }

        if let None = op2 {
            return Err(ForthError::StackUnderflow);
        }

        if let (Some(WordKind::Int(b)), Some(WordKind::Int(a))) = (op1,op2) {
            match op.0 {
                MATH_PLUS  => { self.push(Word::int(a+b)); },
                MATH_MINUS => { self.push(Word::int(a-b)); },
                MATH_STAR  => { self.push(Word::int(a*b)); },
                MATH_SLASH => {
                    if b != 0 {
                        self.push(Word::int(a/b));
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
            return Err(ForthError::InvalidArguments);
        }
    }

    fn stop(&mut self, _: Word) -> Result<(), ForthError> {
        Err(ForthError::Stop)
    }

    // nb: pop is only called from rust, so it's not a forth primitive
    fn pop(&mut self) -> Option<Word> {
        self.dstack.pop()
    }

    fn popkind(&mut self) -> Option<WordKind> {
        if let Some(x) = self.dstack.pop() {
            Some(x.kind())
        } else {
            None
        }
    }

    fn run(&mut self, code: &[Instr], off: u32) -> Result<(), ForthError> {
        // TODO: bounds check

        let mut pc = off;
        let mut stop = false;

        loop {
            eprintln!("pc = {}, code[pc] = {:?}", pc, &code[pc as usize]);
            match &code[pc as usize] {

                Instr::Prim(p,_) if p == &PRIM_STOP => {
                    return Ok(());
                },
                Instr::Prim(p,w) => {
                    let f = p.0;
                    f(self,*w)?;

                    pc += 1;
                },
                Instr::DoCol(ind, _) => {
                },
            }

            eprintln!("stop = {}", stop);
        }
    }

    fn process_token(&mut self, tok: LexToken) -> Result<(), String> {
        println!("token: {} source: {}", tok.token, tok.source);
        if let Token::Ident(id) = tok.token {
            /*
            match self.lookup_ident(id) {
                Builtin(fxn) => {
            }
            */
        } else {
            let data = Data::from_token(tok)?;
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

const PRIM_PUSH : PrimFunc = PrimFunc(ToyForth::push);
const PRIM_DROP : PrimFunc = PrimFunc(ToyForth::drop);
const PRIM_SWAP : PrimFunc = PrimFunc(ToyForth::swap);
const PRIM_MATH : PrimFunc = PrimFunc(ToyForth::math);
const PRIM_STOP : PrimFunc = PrimFunc(ToyForth::stop);

impl std::fmt::Debug for PrimFunc {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut name = 
            if self == &PRIM_PUSH { "push" }
            else if self == &PRIM_DROP { "drop" }
            else if self == &PRIM_SWAP { "swap" }
            else if self == &PRIM_STOP{ "stop" }
            else { "unknown" };

        fmt.write_fmt(format_args!("PrimFunc[{}]", name))
    }
}

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

fn repl(prompt: &str, r: &mut std::io::BufRead, w: &mut std::io::Write) -> std::io::Result<()> {
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
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();

    let mut in_handle = stdin.lock();
    let mut out_handle = stdout.lock();

    if let Err(err) = repl("ok\n", &mut in_handle, &mut out_handle) {
        println!("Error encountered: {}", err);
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

        assert_eq!(Word::str(123).to_str().unwrap(), ST(123));

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
        forth.push(Word::int( 123));
        forth.push(Word::int(-123));
        assert_eq!(forth.pop().unwrap(), Word::int(-123));
        assert_eq!(forth.pop().unwrap(), Word::int( 123));

        forth.push(Word::int( 123));
        forth.push(Word::int(-123));
        forth.swap(Word::int(0));
        assert_eq!(forth.pop().unwrap(), Word::int( 123));
        assert_eq!(forth.pop().unwrap(), Word::int(-123));
    }

    /*
    #[test]
    fn can_allocate_entries() {
        let mut forth = ToyForth::new();
        let xt = forth.allot(4);
        let mut entries = forth.get_entries_mut(xt);
    }
    */

    /*
    #[test]
    fn can_define() {
        let mut forth = ToyForth::new();

        let xt = forth.allot(4);
        let mut entries = forth.get_entries_mut(xt);

        entries[0] = Instr::Prim(PRIM_PUSH, Word::int(4314));
        entries[0] = Instr::Prim(PRIM_PUSH, Word::int(-132));
        entries[0] = Instr::Prim(PRIM_PUSH, Word::int(
    }
    */

    #[test]
    fn run_stack_manip() {
        let mut forth = ToyForth::new();

        let code = vec![
            Instr::Prim(PRIM_PUSH, Word::int(4314)),
            Instr::Prim(PRIM_PUSH, Word::int(-132)),
            Instr::Prim(PRIM_PUSH, Word::int(-999)),
            Instr::Prim(PRIM_SWAP, Word::int(0)),
            Instr::Prim(PRIM_DROP, Word::int(0)),
            Instr::Prim(PRIM_STOP, Word::int(0)),
        ];

        forth.run(&code, 0);
        assert_eq!(forth.pop().unwrap(), Word::int(-999));
        assert_eq!(forth.pop().unwrap(), Word::int(4314));
        assert_eq!(forth.pop(), None);
    }

    #[test]
    fn run_arith() {
        let mut forth = ToyForth::new();

        let code = vec![
            Instr::Prim(PRIM_PUSH, Word::int(4314)),
            Instr::Prim(PRIM_PUSH, Word::int(-132)),
            Instr::Prim(PRIM_MATH, Word(MATH_PLUS)),
            Instr::Prim(PRIM_PUSH, Word::int(-10)),
            Instr::Prim(PRIM_MATH, Word(MATH_STAR)),
            Instr::Prim(PRIM_STOP, Word::int(0)),
        ];

        forth.run(&code, 0);
        assert_eq!(forth.pop().unwrap(), Word::int(-41820));
        assert_eq!(forth.pop(), None);
    }

    #[test]
    fn add_colon_def() {
        let mut forth = ToyForth::new();

    }

    /*
    #[test]
    fn run_colon_def() {
        let mut forth = ToyForth::new();

        let code = vec![
            Instr::Prim(PRIM_PUSH, Word::int(4314)),
            Instr::Prim(PRIM_PUSH, Word::int(-132)),
            Instr::Prim(PRIM_MATH, Word(MATH_PLUS)),
            Instr::Prim(PRIM_PUSH, Word::int(-10)),
            Instr::Prim(PRIM_MATH, Word(MATH_STAR)),
            Instr::Prim(PRIM_STOP, Word::int(0)),
        ];

        forth.run(&code, 0);
        assert_eq!(forth.pop().unwrap(), Word::int(-41820));
        assert_eq!(forth.pop(), None);
    }
    */
}



