use std::rc::Rc;
use std::cell::RefCell;

#[derive(Debug,PartialEq,Eq,Clone,Copy)]
struct Word(u32);

#[derive(Debug,PartialEq,Eq,Clone,Copy)]
struct XT(u32);

impl XT {
    const MAX : u32 = 0x1fff_ffff;
    const MIN : u32 = 0;
    const MASK : u32 = 0x1fff_ffff;
    const BITS : u32 = Word::HIGH_BIT | Word::SIGN_BIT;

    fn to_word(self) -> Word {
        Word::xt(self.0)
    }
}

#[derive(Debug,PartialEq,Eq,Clone,Copy)]
struct Addr(u32);

impl Addr {
    const MAX : u32 = 0x1fff_ffff;
    const MIN : u32 = 0;
    const MASK : u32 = 0x1fff_ffff;
    const ADDR_BIT : u32 = 0x2000_0000;
    const BITS : u32 = Word::HIGH_BIT | Word::SIGN_BIT | Addr::ADDR_BIT;

    fn to_word(self) -> Word {
        // XXX: check mask
        Word(Addr::BITS | self.0)
    }
}

#[derive(Debug,PartialEq,Eq,Clone,Copy)]
struct ScratchLoc{len:u8, off:u8}

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
    const MAX_LENGTH : usize = 256;

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
    Addr(Addr),
}

impl Word {
    const HIGH_BIT : u32 = 0x8000_0000;
    const SIGN_BIT : u32 = 0x4000_0000;
    const INT_MASK : u32 = 0x7fff_ffff;

    const INT_MIN  : i32 = -1073741824;
    const INT_MAX  : i32 =  1073741823;

    const XT_MASK  : u32 = 0x1fff_ffff;
    const STR_MASK : u32 = 0x3fff_ffff;
    const XT_BITS  : u32 = Word::HIGH_BIT | Word::SIGN_BIT;
    const STR_BITS : u32 = Word::HIGH_BIT;

    fn true_value() -> Word {
        Word(Word::INT_MASK)
    }

    fn false_value() -> Word {
        Word(0)
    }

    fn int(x: i32) -> Word {
        // TODO: range check
        Word((x as u32) & Word::INT_MASK)
    }

    fn xt(x: u32) -> Word {
        // TODO: range check
        Word((x & Word::XT_MASK) | Word::XT_BITS)
    }

    fn str(x: u32) -> Word {
        // TODO: range check
        Word((x & Word::STR_MASK) | Word::STR_BITS)
    }

    fn addr(x: u32) -> Word {
        Addr(x).to_word()
    }

    pub fn from_xt(xt: XT) -> Word {
        Word::xt(xt.0)
    }

    pub fn from_str(st: ST) -> Word {
        st.to_word()
    }

    pub fn from_addr(addr: Addr) -> Word {
        addr.to_word()
    }

    pub fn kind(self) -> WordKind {
        match self.0 {
            x if (x & Word::HIGH_BIT) == 0 => { WordKind::Int((x | ((x & Word::SIGN_BIT) << 1)) as i32) },
            x if (x & Word::SIGN_BIT) == 0 => {
                // FIXME: unwrap!
                WordKind::Str(ST::from_u32(x).unwrap())
            },
            x if (x & Addr::ADDR_BIT) != 0 => {
                WordKind::Addr(Addr(x & Addr::MASK))
            }
            x => { WordKind::XT(XT(x & Word::XT_MASK)) },
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

    pub fn to_addr(self) -> Option<Addr> {
        if let WordKind::Addr(x) = self.kind() { Some(x) } else { None }
    }
}

impl std::fmt::Display for Word {
    fn fmt(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.kind() {
            WordKind::Int(x) => { formatter.write_fmt(format_args!("[int] {}", x)) },
            WordKind::XT(XT(x))  => { formatter.write_fmt(format_args!("[xt] {}", x)) },
            WordKind::Addr(Addr(x))  => { formatter.write_fmt(format_args!("[addr] {}", x)) },
            WordKind::Str(st) => {
                match st {
                    ST::Allocated(v) => {
                        formatter.write_fmt(format_args!("[str:alloc] @ {} len={},addr={}", v, st.len(), st.addr())) },
                    ST::PadSpace(loc)  => { formatter.write_fmt(format_args!("[str:pad] len={},off={}", loc.len, loc.off)) },
                    ST::WordSpace(loc) => { formatter.write_fmt(format_args!("[str:word] len={},off={}", loc.len, loc.off)) },
                    ST::InputSpace(loc) => { formatter.write_fmt(format_args!("[str:input] len={},off={}", loc.len, loc.off)) },
                }
            },
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
enum Instr {
    Empty,
    Bye,
    Push(Word),
    Drop,
    Dup,
    Swap,
    Over,
    BinaryOp(BinOp),
    UnaryOp(UnaryOp),
    Branch(i32),
    BranchOnZero(i32),  // branches if stack top is 0
    ControlIndexPush(u8),
    ControlIndexPop(u8),
    ControlIteration,
    ControlIndexPeek(u32),
    EOL,
    Lookup,
    DefStr,
    DefWord,
    Func(u32),
    DoCol(XT),
    Unnest,
}

#[derive(Debug,Clone,Copy,PartialEq,Eq)]
#[repr(u8)]
enum UnaryOp {
    Negate,
}

#[derive(Debug,Clone,Copy,PartialEq,Eq)]
#[repr(u8)]
enum BinOp {
    Plus,
    Minus,
    Star,
    Slash,
    Greater,
    Less,
    Equal,
    NotEqual,
}

#[derive(Debug,Clone,Copy,PartialEq,Eq)]
enum ControlEntry {
    /*
    IfAddr(XT),
    ElseAddr(XT),
    LoopAddr(XT),
    */
    Addr(XT),
    Index(i32),
}

#[derive(Debug,Clone,Copy)]
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
    cstack: Vec<ControlEntry>,
    ufuncs: Vec<ForthFunc<'tf>>,

    dict: Vec<DictEntry>,
    vars: Vec<Word>,
    strings: std::vec::Vec<u8>,
    code: Vec<Instr>,

    pad:  [u8;256],
    word: [u8;256],

    input: String,
    input_off: usize,

    // in_stream: Option<Rc<RefCell<(dyn std::io::BufRead)>>>,
    in_stream: Option<Rc<RefCell<(dyn LineReader)>>>,
    out_stream: Option<Rc<RefCell<(dyn std::io::Write)>>>,
}

#[derive(Debug)]
enum ForthError {
    StackUnderflow,
    ControlStackUnderflow,
    ReturnStackUnderflow,

    InvalidOperation,
    InvalidArgument,
    DivisionByZero,

    NumberOutOfRange,

    InvalidEmptyString,
    StringTooLong,
    StringOffsetTooLarge,

    FunctionSpaceOverflow,
    DictSpaceOverflow,
    VarSpaceOverflow,
    StringSpaceOverflow,

    InvalidCompilerWord,
    InvalidInterpreterWord,
    UnfinishedColonDefinition,
    DictEmpty,

    NotImplemented,

    StringNotFound,
    WordNotFound(ST),

    InvalidCell(XT),
    InvalidControlEntry(ControlEntry),
    InvalidIndex(Word),
    InvalidControlInstruction(XT),
    InvalidExecutionToken(Word),
    InvalidString(ST),
    InvalidChar(i32),
    InvalidAddress(Addr),
    InvalidCountedString(ST),
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

pub trait LineReader {
    fn read_line(&self, buf: &mut String) -> std::io::Result<usize>;
}

impl LineReader for std::io::Stdin {
    fn read_line(&self, buf: &mut String) -> std::io::Result<usize> {
        std::io::Stdin::read_line(self,buf)
    }
}

impl<'tf> ToyForth<'tf> {
    const ADDR_STATE:      Addr = Addr(0);
    const ADDR_SLASH_CDEF: Addr = Addr(1);
    const ADDR_SLASH_CXT:  Addr = Addr(2);

    pub fn new() -> ToyForth<'tf> {
        let mut tf = ToyForth{
            dstack:  std::vec::Vec::new(),
            rstack:  std::vec::Vec::new(),
            cstack:  std::vec::Vec::new(),
            ufuncs:  std::vec::Vec::new(),

            dict:    std::vec::Vec::new(),
            vars:    std::vec::Vec::new(),
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
        tf.add_instr(Instr::Bye);

        // set up standard dictionary
        tf.add_prim("BYE", Instr::Bye);
        tf.add_prim("DUP", Instr::Dup);
        tf.add_prim("DROP", Instr::Drop);
        tf.add_prim("SWAP", Instr::Swap);
        tf.add_prim("OVER", Instr::Over);

        tf.add_prim("+", Instr::BinaryOp(BinOp::Plus));
        tf.add_prim("-", Instr::BinaryOp(BinOp::Minus));
        tf.add_prim("*", Instr::BinaryOp(BinOp::Star));
        tf.add_prim("/", Instr::BinaryOp(BinOp::Slash));

        tf.add_prim("NEGATE", Instr::UnaryOp(UnaryOp::Negate));

        tf.add_prim(">", Instr::BinaryOp(BinOp::Greater));
        tf.add_prim("<", Instr::BinaryOp(BinOp::Less));
        tf.add_prim("=", Instr::BinaryOp(BinOp::Equal));
        tf.add_prim("<>", Instr::BinaryOp(BinOp::NotEqual));

        let (emit,_) = tf.add_func("EMIT", ToyForth::builtin_emit);

        // words that may be replaced with Forth definitions at some point
        tf.add_prim("BL", Instr::Push(Word::int(' ' as i32)));
        tf.add_func("CHAR", ToyForth::builtin_char);
        tf.add_func("WORD", ToyForth::builtin_word);
        tf.add_func("C@", ToyForth::builtin_char_at);
        tf.add_func("CHAR+", ToyForth::builtin_char_plus);
        tf.add_func("PARSE", ToyForth::builtin_parse);

        tf.add_func(".", ToyForth::builtin_dot);
        tf.add_func(":", ToyForth::builtin_colon);
        tf.add_immed(";", ToyForth::builtin_semi);

        tf.add_immed("[CHAR]", ToyForth::builtin_brak_char);

        tf.add_immed("IF", ToyForth::builtin_if);
        tf.add_immed("ELSE", ToyForth::builtin_else);
        tf.add_immed("THEN", ToyForth::builtin_then);

        tf.add_immed("DO", ToyForth::builtin_do);
        tf.add_immed("LOOP", ToyForth::builtin_loop);
        tf.add_immed("I", ToyForth::builtin_loop_ind0);
        tf.add_immed("J", ToyForth::builtin_loop_ind1);

        tf.add_func("IMMEDIATE", ToyForth::builtin_immediate);

        tf.add_func("FIND", ToyForth::builtin_find);

        tf.add_func(">NUMBER", ToyForth::builtin_to_number);

        // should these be prims?
        tf.add_func(">R", ToyForth::builtin_data_to_ret);
        tf.add_func("R>", ToyForth::builtin_ret_to_data);

        tf.add_func("CONSTANT", ToyForth::builtin_constant);
        tf.add_func("VARIABLE", ToyForth::builtin_variable);

        tf.add_func("!", ToyForth::builtin_var_set);
        tf.add_func("@", ToyForth::builtin_var_get);

        // define state variables
        let state_vars = vec![ "STATE", "/CDEF", "/CXT" ];
        for v in &state_vars {
            let addr = tf.new_var(Word(0)).unwrap();
            tf.add_prim(v, Instr::Push(addr.to_word()));
        }

        // define standard words that are not primitives
        tf.add_word("CR", &[
            Instr::Push(Word::int('\n' as i32)),
            Instr::Func(emit as u32),
            Instr::Unnest,
        ]).unwrap();

        // tf.add_func("PARSE-NAME", ToyForth::builtin_parse);

        eprintln!("Code cell size is {}", std::mem::size_of::<Instr>());
        eprintln!("Data cell size is {}", std::mem::size_of::<Word>());

        return tf;
    }

    fn cpush_addr(&mut self, xt: XT) {
        self.cstack.push(ControlEntry::Addr(xt));
    }

    fn cpush_index(&mut self, idx: i32) {
        self.cstack.push(ControlEntry::Index(idx));
    }

    fn cpop_addr(&mut self) -> Result<XT,ForthError> {
        let ctl = self.cstack.pop().ok_or(ForthError::ControlStackUnderflow)?;
        if let ControlEntry::Addr(xt) = ctl {
            Ok(xt)
        } else {
            Err(ForthError::InvalidControlEntry(ctl))
        }
    }

    fn cpop_index(&mut self) -> Result<i32,ForthError> {
        let ctl = self.cstack.pop().ok_or(ForthError::ControlStackUnderflow)?;
        if let ControlEntry::Index(idx) = ctl {
            Ok(idx)
        } else {
            Err(ForthError::InvalidControlEntry(ctl))
        }
    }

    fn cpeek_index(&mut self) -> Result<i32,ForthError> {
        let ctl = self.cstack.pop().ok_or(ForthError::ControlStackUnderflow)?;
        if let ControlEntry::Index(idx) = ctl {
            Ok(idx)
        } else {
            Err(ForthError::InvalidControlEntry(ctl))
        }
    }

    pub fn print_code(&self, xt: XT) {
        for (i,instr) in self.code[xt.0 as usize..].iter().enumerate() {
            eprintln!("[{:3}] {:?}", i, instr);
            if let Instr::Unnest = *instr {
                break
            }
        }
    }

    pub fn print_word_code(&self, word: &str) {
        let xt = self.lookup_word(word).unwrap();
        eprintln!("word: {}\ncode:", word);
        self.print_code(xt);
        eprintln!(".\n");
    }

    pub fn print_stacks(&self, msg: &str) {
        eprintln!(">>> {}: ",msg);
        for (i,w) in self.dstack.iter().enumerate() {
            let k = w.kind();
            if let WordKind::Str(st) = k {
                let s0 = self.maybe_string_at(st);
                if let Ok(s) = s0 {
                    eprintln!("[D {:3}] {:?} \"{}\"", i,w.kind(), s);
                } else {
                    let b = self.bytes_at(st);
                    eprintln!("[D {:3}] {:?} {:?}", i,w.kind(), b);
                }
            } else {
                eprintln!("[D {:3}] {:?}", i,w.kind());
            }
        }
        for (i,w) in self.rstack.iter().enumerate() {
            eprintln!("[R {:3}] {:?}", i,w);
        }
        for (i,itm) in self.cstack.iter().enumerate() {
            eprintln!("[C {:3}] {:?}", i, itm);
        }
        eprintln!("done\n");
    }

    pub fn capture_interpret(&mut self, s: &str, w: Rc<RefCell<dyn std::io::Write>>) -> Result<(),ForthError> {
        // w: &'tf mut dyn std::io::Write) 
        let old_out = std::mem::replace(&mut self.out_stream, Some(w));
        let ret = self.interpret(s);
        self.out_stream = old_out;

        return ret;
    }

    pub fn interpret(&mut self, s: &str) -> Result<(), ForthError> {
        // initial interpret is dumb...

        self.set_input(s);
        self.builtin_interpret()
    }

    pub fn compiling(&self) -> bool {
        return self.vars[0].to_int().unwrap_or(0) != 0;
    }

    pub fn check_compiling(&self) -> Result<(), ForthError> {
        if self.compiling() {
            Ok(())
        } else {
            Err(ForthError::InvalidCompilerWord)
        }
    }

    pub fn builtin_interpret(&mut self) -> Result<(), ForthError> {
        loop {
            self.push_int(' ' as i32)?;
            self.builtin_parse()?;
            self.builtin_find_name()?;

            let is_compiling = self.compiling();
            let wh = self.pop_int()?;

            if wh == 0 {                        // ( caddr u 0 -- caddr u )
                self.dup()?;                    // ( caddr u -- caddr u u )
                let mut len = self.pop_int()?;      // ( caddr u u -- caddr u )

                if len == 0 {
                    self.drop()?;               // ( caddr u -- caddr )
                    self.drop()?;               // ( caddr -- )
                    break;
                }

                self.builtin_data_to_ret()?;    // ( caddr u -- caddr )           r: ( -- u )
                self.dup()?;                    // ( caddr -- caddr caddr )       r: ( u -- u )
                self.builtin_char_at()?;        // ( caddr caddr -- caddr ch )    r: ( u -- u )
                self.push_int('-' as i32)?;     // ( caddr ch -- caddr ch '-' )   r: ( u -- u )
                self.binary_op(BinOp::Equal)?;      // ( caddr ch '-' -- caddr neg? ) r: ( u -- u )
                self.swap()?;                   // ( caddr neg? -- neg? caddr )   r: ( u -- u )
                self.over()?;                   // ( neg? caddr -- neg? caddr neg? ) r: ( u -- u )

                // self.print_stacks("-1-");

                if self.pop_int()? != 0 {       // ( neg? caddr neg? -- neg? caddr ) r: ( u -- u )
                    self.builtin_char_plus()?;  // ( neg? caddr -- neg? caddr2 )
                    self.builtin_ret_to_data()?; // ( neg? caddr2 -- neg? caddr2 u ) r: ( u -- )
                    let u = self.pop_int()?;    // ( neg? caddr2 u -- neg? caddr2 ) r: ( -- )
                    self.push_int(u - 1)?;      // ( neg? caddr2 -- neg? caddr2 u2 ) r: ( -- )

                    len -= 1;

                    self.builtin_data_to_ret()?;    // ( neg? caddr2 u2 -- neg? caddr2 )  r: ( -- u2 )
                    // self.print_stacks("-2-");
                }

                self.push_int(0)?;              // ( neg? caddr -- neg? caddr 0 ) r: ( u -- u )
                self.swap()?;                   // ( neg? caddr 0 -- neg? 0 caddr ) r: ( u -- u )

                self.builtin_ret_to_data()?;    // ( neg? 0 caddr -- neg? 0 caddr u ) r: ( u -- )

                // self.print_stacks("-3-");
                self.builtin_to_number()?;      // ( neg? 0 caddr u1 -- neg? ud caddr u2 )
                // self.print_stacks("-4-");

                let consumed = self.pop_int()?; // ( neg? ud caddr u2 -- neg? ud caddr )

                if consumed < (len as i32) {
                    let st = self.pop_str()?;   // ( neg? ud caddr -- neg? ud )
                    self.drop()?;               // ( neg? ud -- neg? )
                    self.drop()?;               // ( neg? -- )
                    return Err(ForthError::WordNotFound(st));
                }

                self.drop()?;                   // ( neg? ud caddr -- neg? ud )

                self.swap()?;                   // ( neg? ud -- ud neg? )
                if self.pop_int()? != 0 {       // ( ud neg? -- ud )
                    self.unary_op(UnaryOp::Negate)?;    // ( ud -- ud1 )
                }

                if is_compiling {
                    let num = self.pop_int()?;
                    self.add_instr(Instr::Push(Word::int(num)));
                }
            } else {
                let xt = self.pop_xt()?;
                if wh == 1 || !is_compiling {
                    self.ret_push_bye()?;
                    self.exec(xt)?;
                } else {
                    self.add_instr(Instr::DoCol(xt));
                }
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
            let mut r = inp.borrow_mut();
            let s = &mut self.input;
            r.read_line(s)?;
            if let Some(ch) = s.pop() {
                if ch != '\n' {
                    s.push(ch);
                }
            }

        }

        // return ToyForth::refill(rdr.deref_mut(), &mut self.input);
        Ok(())
    }

    pub fn builtin_emit(&mut self) -> Result<(), ForthError> {
        let ch = self.pop_int()?;
        if ch < 0 || ch > 255 {
            return Err(ForthError::InvalidChar(ch));
        }

        if let Some(out) = &mut self.out_stream {
            let mut w = out.borrow_mut();
            // let buf : [u8;1] = [ ch as u8 ];
            // w.write(&buf)?;
            w.write(&[ ch as u8 ]);
        }
        Ok(())
    }

    pub fn write_prompt(&mut self, prompt: &str) -> Result<(), ForthError> {
        if let Some(out) = &mut self.out_stream {
            let mut w = out.borrow_mut();
            write!(w, "{}\n", prompt)?;
            w.flush()?;
        }

        Ok(())
    }

    pub fn std_repl() -> Result<(),ForthError> {
        let prompt = "ok";

        let stdin = std::io::stdin();
        let stdout = std::io::stdout();

        let mut forth = ToyForth::new();

        // forth.repl(prompt, &mut in_handle, &mut out_handle)
        let r = Rc::new(RefCell::new(stdin));
        let w = Rc::new(RefCell::new(stdout));
        forth.repl(prompt, r, w)
    }

    // pub fn repl(&mut self, prompt: &str, r: &'tf mut dyn std::io::BufRead, w: &'tf mut dyn std::io::Write) -> Result<(),ForthError> {
    pub fn repl(&mut self, prompt: &str, r: Rc<RefCell<(dyn LineReader + 'static)>>, w: Rc<RefCell<(dyn std::io::Write + 'static)>>) -> Result<(),ForthError> {
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
            if !self.compiling() {
                self.write_prompt(prompt)?;
            }
            self.builtin_refill()?;

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

    pub fn addr_here(&self) -> u32 {
        return self.vars.len() as u32;
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
    fn add_prim(&mut self, word: &str, prim: Instr) -> XT {
        self.add_primitive(word,prim).unwrap()
    }

    pub fn add_primitive(&mut self, word: &str, prim: Instr) -> Result<XT,ForthError> {
        let st = self.add_string(word)?;

        let xt = self.mark_code();
        self.add_instr(prim);
        self.add_instr(Instr::Unnest);

        self.dict.push(DictEntry{
            st: st,
            xt: xt,
            flags: DictEntry::PRIMITIVE,
        });

        Ok(xt)
    }

    fn add_func(&mut self, word: &str, func: fn (&mut ToyForth<'tf>) -> Result<(),ForthError>) -> (usize,XT) {
        self.add_function(word,func).unwrap()
    }

    fn add_immed(&mut self, word: &str, func: fn (&mut ToyForth<'tf>) -> Result<(),ForthError>) -> (usize,XT) {
        let (ind,xt) = self.add_function(word,func).unwrap();
        self.builtin_immediate().unwrap();

        return (ind,xt);
    }

    pub fn add_function(&mut self, word: &str, func: fn (&mut ToyForth<'tf>) -> Result<(),ForthError>) -> Result<(usize,XT),ForthError> {
        self.add_string(word)?;
        let func_ind = self.ufuncs.len();

        if func_ind > 0xffff_ffff {
            return Err(ForthError::FunctionSpaceOverflow);
        }

        self.ufuncs.push(ForthFunc(func));
        let xt = self.add_primitive(word, Instr::Func(func_ind as u32))?;
        Ok((func_ind,xt))
    }

    pub fn add_word(&mut self, word: &str, code: &[Instr]) -> Result<XT,ForthError> {
        let xt = self.mark_code();
        for instr in code {
            self.add_instr(*instr);
        }

        self.define_word(word,xt)?;
        Ok(xt)
    }

    pub fn allocate_string(&mut self, st: ST) -> Result<ST,ForthError> {
        // FIXME: completely unnecessary copy here...
        let s = self.maybe_string_at(st)?.to_string();

        self.add_string(&s)
    }

    pub fn define_word(&mut self, word: &str, xt: XT) -> Result<ST,ForthError> {
        let st = self.add_string(word)?;

        self.dict.push(DictEntry{
            st: st,
            xt: xt,
            flags: 0,
        });

        return Ok(st);
    }

    pub fn lookup_dict_entry(&self, word: &str) -> Result<DictEntry, ForthError> {
        for ent in self.dict.iter().rev() {
            let entry_word = self.maybe_string_at(ent.st)?;
            if word.eq_ignore_ascii_case(entry_word) {
                return Ok(*ent);
            }
        }

        return Err(ForthError::StringNotFound);
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

    pub fn mark_code(&self) -> XT {
        let ind = self.code.len();

        if ind >= XT::MAX as usize {
            // XXX: handle with panic?
            panic!("marker at maximum dictionary size");
        }

        return XT(ind as u32);
    }

    pub fn add_instr(&mut self, code: Instr) -> XT {
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

    fn set_input(&mut self, s: &str) {
        self.input.clear();
        self.input.push_str(s);
        self.input_off = 0;
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

    fn add_string_to_pool(strings: &mut std::vec::Vec<u8>, s: &str) -> Result<ST,ForthError> {
        let b = s.as_bytes();

        if b.len() > ST::MAX_LENGTH {
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

    pub fn add_string(&mut self, s: &str) -> Result<ST,ForthError> {
        ToyForth::add_string_to_pool(&mut self.strings, s)
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

    pub fn maybe_counted_string_at(&self, st: ST) -> Result<&str, ForthError> {
        let b = self.bytes_at(st);

        // eprintln!("bytes = {:?}", b);
        // eprintln!("word_space = {:?}", self.word);

        let len = b[0] as usize;
        if len >= b.len() {
            return Err(ForthError::InvalidCountedString(st));
        }

        return std::str::from_utf8(&b[1..(len+1)]).map_err(|_| ForthError::InvalidCountedString(st));
    }

    pub fn counted_string_at(&self, st: ST) -> &str {
        self.maybe_counted_string_at(st).unwrap()
    }

    pub fn maybe_string_at(&self, st: ST) -> Result<&str, ForthError> {
        return std::str::from_utf8(self.bytes_at(st)).map_err(|_| ForthError::InvalidString(st));
    }

    pub fn string_at(&self, st: ST) -> &str {
        self.maybe_string_at(st).unwrap()
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

    fn over(&mut self) -> Result<(), ForthError> {
        let len = self.dstack.len();
        if len >= 2 {
            self.dstack.push(self.dstack[len-2]);
            Ok(())
        } else {
            Err(ForthError::StackUnderflow)
        }
    }

    fn builtin_data_to_ret(&mut self) -> Result<(), ForthError> {
        let w = self.dstack.pop().ok_or(ForthError::StackUnderflow)?;
        self.rstack.push(w);
        Ok(())
    }

    fn builtin_ret_to_data(&mut self) -> Result<(), ForthError> {
        let w = self.rstack.pop().ok_or(ForthError::StackUnderflow)?;
        self.dstack.push(w);
        Ok(())
    }

    fn new_var(&mut self, initial_value: Word) -> Result<Addr, ForthError> {
        let addr = self.vars.len();

        if addr > (Addr::MAX as usize) {
            return Err(ForthError::VarSpaceOverflow);
        }

        self.vars.push(initial_value);
        Ok(Addr(addr as u32))
    }

    fn get_var_at(&mut self, addr: Addr) -> Result<Word, ForthError> {
        let ind = addr.0 as usize;

        if ind >= self.vars.len() {
            return Err(ForthError::InvalidAddress(addr));
        }

        Ok(self.vars[ind])
    }

    fn set_var_at(&mut self, addr: Addr, value: Word) -> Result<(), ForthError> {
        let ind = addr.0 as usize;

        if ind >= self.vars.len() {
            return Err(ForthError::InvalidAddress(addr));
        }

        self.vars[ind] = value;

        Ok(())
    }

    fn builtin_var_get(&mut self) -> Result<(), ForthError> {
        let addr = self.pop_addr()?;
        let w = self.get_var_at(addr)?;
        self.push(w)?;
        Ok(())
    }

    fn builtin_var_set(&mut self) -> Result<(), ForthError> {
        let addr = self.pop_addr()?;
        let val = self.pop().ok_or(ForthError::StackUnderflow)?;
        self.set_var_at(addr, val)?;
        Ok(())
    }

    fn unary_op(&mut self, op: UnaryOp) -> Result<(),ForthError> {
        let a = self.pop_int()?;
        match op {
            UnaryOp::Negate => { self.push_int(-a)?; Ok(()) },
        }
    }

    fn binary_op(&mut self, op: BinOp) -> Result<(),ForthError> {
        let b = self.pop_int()?;
        let a = self.pop_int()?;

        // eprintln!("op = {:?}, a={}, b={}", op, a,b);
        match op {
            BinOp::Plus  => { self.push(Word::int(a+b))?; },
            BinOp::Minus => { self.push(Word::int(a-b))?; },
            BinOp::Star  => { self.push(Word::int(a*b))?; },
            BinOp::Slash => {
                if b != 0 {
                    self.push(Word::int(a/b))?;
                } else {
                    return Err(ForthError::DivisionByZero);
                }
            },
            BinOp::Greater  => { self.push(Word::int(if a>b { 1 } else { 0 }))?; },
            BinOp::Less     => { self.push(Word::int(if a<b { 1 } else { 0 }))?; },
            BinOp::Equal    => { self.push(Word::int(if a==b { 1 } else { 0 }))?; },
            BinOp::NotEqual => { self.push(Word::int(if a != b { 1 } else { 0 }))?; },
        }

        return Ok(());
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
        let s = self.maybe_counted_string_at(st)?;

        match self.lookup_dict_entry(s) {
            Ok(entry) => {
                self.push(Word::from_xt(entry.xt))?;
                let wh = if (entry.flags & DictEntry::IMMEDIATE) != 0 { 1 } else { -1 };
                self.push(Word::int(wh))?;
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

    // (caddr u -- xt 1 | xt -1 | caddr u 0)
    fn builtin_find_name(&mut self) -> Result<(), ForthError> {
        let len = self.pop_int()?;
        if len < 0 {
            return Err(ForthError::NumberOutOfRange);
        }

        let st = self.pop_str()?;
        let s = {
            let s0 = self.maybe_string_at(st)?;
            let l = len as usize;
            if s0.len() <= l { &s0 } else { &s0[..l] }
        };

        match self.lookup_dict_entry(s) {
            Ok(entry) => {
                self.push(Word::from_xt(entry.xt))?;
                let wh = if (entry.flags & DictEntry::IMMEDIATE) != 0 { 1 } else { -1 };
                self.push(Word::int(wh))?;
                Ok(())
            },
            Err(ForthError::StringNotFound) => {
                self.push(st.to_word())?;
                self.push_int(len)?;
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
        let entry = self.dict.last_mut().ok_or(ForthError::DictEmpty)?;
        entry.flags |= DictEntry::IMMEDIATE;

        Ok(())
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
        match ToyForth::add_string_to_pool(&mut self.strings, s) {
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
            let mut wr = out.borrow_mut();

            if let WordKind::Int(n) = w.kind() {
                write!(wr, "{}", n)?;
            } else {
                write!(wr, "{}", w)?;
            }
            wr.flush()?;
        }

        Ok(())
    }

    fn builtin_constant(&mut self) -> Result<(), ForthError> {
        let w = self.pop().ok_or(ForthError::StackUnderflow)?;

        self.push_int(' ' as i32)?;
        self.builtin_parse()?;

        let len = self.pop_int()?;
        let st = self.pop_str()?;
        if len == 0 {
            return Err(ForthError::InvalidEmptyString);
        }

        // FIXME: completely unnecessary copy here...
        let s = self.maybe_string_at(st)?.to_string();
        self.add_word(&s, &[ Instr::Push(w), Instr::Unnest ])?;

        Ok(())
    }

    fn builtin_variable(&mut self) -> Result<(), ForthError> {
        self.push_int(' ' as i32)?;
        self.builtin_parse()?;

        let len = self.pop_int()?;
        let st = self.pop_str()?;
        if len == 0 {
            return Err(ForthError::InvalidEmptyString);
        }

        let addr = self.new_var(Word(0))?;

        // FIXME: completely unnecessary copy here...
        let s = self.maybe_string_at(st)?.to_string();
        self.add_word(&s, &[ Instr::Push(addr.to_word()), Instr::Unnest ])?;

        Ok(())
    }

    fn builtin_colon(&mut self) -> Result<(), ForthError> {
        self.push_int(' ' as i32)?;
        self.builtin_parse()?;

        let len = self.pop_int()?;
        let st = self.pop_str()?;
        if len == 0 {
            return Err(ForthError::InvalidEmptyString);
        }

        // FIXME: completely unnecessary copy here...
        let s = self.maybe_string_at(st)?.to_string();
        let st = self.add_string(&s)?;

        // XXX: check that STATE==0, /CDEF and /CXT are not set
        self.set_var_at(ToyForth::ADDR_SLASH_CDEF, st.to_word())?;

        let xt = self.mark_code();
        self.set_var_at(ToyForth::ADDR_SLASH_CXT, xt.to_word())?;
        self.set_var_at(ToyForth::ADDR_STATE, Word::int(1))?;

        Ok(())
    }

    fn builtin_semi(&mut self) -> Result<(), ForthError> {
        if !self.compiling() {
            return Err(ForthError::InvalidInterpreterWord);
        }

        eprintln!("SEMI: COMPILING");

        self.add_instr(Instr::Unnest);
        let st = self.get_var_at(ToyForth::ADDR_SLASH_CDEF)?.to_str().ok_or(ForthError::InvalidArgument)?; // XXX: need better error
        let xt = self.get_var_at(ToyForth::ADDR_SLASH_CXT)?.to_xt().ok_or(ForthError::InvalidArgument)?; // XXX: need better error

        eprintln!("SEMI: st = {:?} \"{}\", xt = {:?}",
              st, self.string_at(st), xt);

        self.dict.push(DictEntry{
            st: st,
            xt: xt,
            flags: 0,
        });

        self.set_var_at(ToyForth::ADDR_SLASH_CDEF, Word(0))?;
        self.set_var_at(ToyForth::ADDR_SLASH_CXT, Word(0))?;
        self.set_var_at(ToyForth::ADDR_STATE, Word::int(0))?;

        Ok(())
    }

    fn builtin_if(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        // add branch, fixup cstack reference later
        let xt = self.add_instr(Instr::BranchOnZero(0));
        self.cpush_addr(xt);

        Ok(())
    }

    fn builtin_then(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        let xt = self.mark_code();
        let if_else_xt = self.cpop_addr()?;

        // XXX: check for overflow
        let delta : i32 = ((xt.0 as i64) - (if_else_xt.0 as i64)) as i32;

        match self.code[if_else_xt.0 as usize] {
            Instr::Branch(_) => {
                self.code[if_else_xt.0 as usize] = Instr::Branch(delta);
            },
            Instr::BranchOnZero(_) => {
                self.code[if_else_xt.0 as usize] = Instr::BranchOnZero(delta);
            },
            _ => {
                return Err(ForthError::InvalidControlInstruction(if_else_xt));
            }
        }

        Ok(())
    }

    fn builtin_else(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        let if_xt = self.cpop_addr()?;
        let else_xt = self.add_instr(Instr::Branch(0));

        let xt = self.mark_code();
        self.cpush_addr(else_xt);

        let delta : i32 = ((xt.0 as i64) - (if_xt.0 as i64)) as i32;
        match self.code[if_xt.0 as usize] {
            Instr::BranchOnZero(_) => {
                self.code[if_xt.0 as usize] = Instr::BranchOnZero(delta);
            },
            _ => {
                return Err(ForthError::InvalidControlInstruction(if_xt));
            }
        }

        Ok(())
    }

    fn builtin_do(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        // loop header
        self.add_code(&[
            Instr::ControlIndexPush(2),
        ]);

        let xt = self.mark_code();
        self.cpush_addr(xt);
        Ok(())
    }

    fn builtin_loop(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        let do_xt = self.cpop_addr()?;

        // ControlIteration: ( -- 0 | 1 ) (C: n1 n2 -- n1 n3 | )
        // if n2<n1, pushes n1 and n3=n2-1 onto the control stack, pushes 0 onto the data stack
        // if n2>=1, pops n1,n2 from the control stack, pushes 1 onto the data stack
        self.add_instr(Instr::ControlIteration);

        // branch back to DO (after loop header)
        let xt = self.mark_code();
        let delta : i32 = ((do_xt.0 as i64) - (xt.0 as i64)) as i32;
        self.add_instr(Instr::BranchOnZero(delta));

        Ok(())
    }

    fn builtin_loop_ind0(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        // TODO: check that we're in a loop
        self.add_instr(Instr::ControlIndexPeek(0));

        Ok(())
    }

    fn builtin_loop_ind1(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        // TODO: check that we're in a loop
        self.add_instr(Instr::ControlIndexPeek(2));

        Ok(())
    }

    // [CHAR]
    fn builtin_brak_char(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        let (w0,w1) = ToyForth::scan_word(&self.input[self.input_off..].as_bytes(), ' ' as u8);

        let off = self.input_off+w0;
        let end = self.input_off+w1;

        // TODO: replace with u32::MAX when supported
        if end > 0xffff_ffff {
            return Err(ForthError::StringTooLong);
        }

        self.input_off = end;

        if off >= end {
            return Err(ForthError::InvalidEmptyString);
        }

        let w = Word::int(self.input.as_bytes()[off] as i32);
        self.add_instr(Instr::Push(w));
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

    fn builtin_char_at(&mut self) -> Result<(), ForthError> {
        let st = self.pop_str()?;
        let b = *self.bytes_at(st).first().ok_or(ForthError::InvalidEmptyString)?;
        self.push_int(b as i32)?;
        Ok(())
    }

    fn builtin_char_plus(&mut self) -> Result<(), ForthError> {
        let st = self.pop_str()?;
        self.push(st.offset(1).to_word())?;
        Ok(())
    }

    fn builtin_word(&mut self) -> Result<(), ForthError> {
        let delim = self.pop_delim()?;

        let (w0,w1) = ToyForth::scan_word(&self.input[self.input_off..].as_bytes(), delim);

        let word_off = self.input_off+w0;
        let word_end = self.input_off+w1;

        let len = word_end - word_off;
        if len >= 255 {
            return Err(ForthError::StringTooLong);
        }

        self.input_off = word_end;

        let wstr : &mut [u8] = &mut self.word[..];
        wstr[0] = len as u8;
        wstr[1..(len+1)].copy_from_slice(&self.input.as_bytes()[word_off..word_end]);

        // self.push(ST::input_space(off as u8,len as u8).to_word())?;
        self.push(ST::word_space(0, (len+1) as u8).to_word())?;
        Ok(())
    }

    fn builtin_parse(&mut self) -> Result<(), ForthError> {
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
        self.push_int(len as i32)?;
        Ok(())
    }

    // nb: pop is only called from rust, so it's not a forth primitive
    pub fn pop(&mut self) -> Option<Word> {
        self.dstack.pop()
    }

    // nb: pop is only called from rust, so it's not a forth primitive
    pub fn peek(&self) -> Option<Word> {
        self.dstack.last().map(|x| *x)
    }

    pub fn peek_kind(&self) -> Option<WordKind> {
        self.peek().map(Word::kind)
    }

    // nb: pop is only called from rust, so it's not a forth primitive
    pub fn peek_str(&self) -> Result<ST, ForthError> {
        match self.peek_kind() {
            Some(WordKind::Str(st)) => {
                Ok(st)
            },
            Some(_) => {
                Err(ForthError::InvalidArgument)
            },
            None => {
                Err(ForthError::StackUnderflow)
            }
        }
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

    fn pop_addr(&mut self) -> Result<Addr,ForthError> {
        let v = self.pop_kind().ok_or(ForthError::StackUnderflow)?;
        if let WordKind::Addr(addr) = v {
            Ok(addr)
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
                Instr::Empty => {
                    return Err(ForthError::InvalidCell(XT(pc)));
                },
                Instr::Bye => {
                    return Ok(());
                },
                Instr::Push(w) => {
                    self.push(w)?;
                    pc += 1;
                },
                Instr::Drop => {
                    self.drop()?;
                    pc += 1;
                },
                Instr::Dup => {
                    self.dup()?;
                    pc += 1;
                },
                Instr::Swap => {
                    self.swap()?;
                    pc += 1;
                },
                Instr::Over => {
                    self.over()?;
                    pc += 1;
                },
                Instr::Branch(delta) => {
                    if delta == 0 {
                        return Err(ForthError::InvalidControlInstruction(xt));
                    }

                    let new_pc = (pc as i64) + (delta as i64);
                    // FIXME: check range
                    pc = new_pc as u32;
                },
                Instr::BranchOnZero(delta) => {
                    if delta == 0 {
                        return Err(ForthError::InvalidControlInstruction(xt));
                    }

                    let arg = self.pop_int()?;
                    if arg == 0 {
                        let new_pc = (pc as i64) + (delta as i64);
                        // FIXME: check range
                        pc = new_pc as u32;
                    } else {
                        pc += 1;
                    }
                },
                Instr::ControlIndexPush(count) => {
                    if count > 0 {
                        let dlen = self.dstack.len();
                        if dlen < count as usize {
                            return Err(ForthError::StackUnderflow);
                        }

                        let i0 = dlen-(count as usize);
                        for itm in self.dstack.drain(i0..) {
                            if let WordKind::Int(index) = itm.kind() {
                                self.cstack.push(ControlEntry::Index(index));
                            } else {
                                return Err(ForthError::InvalidIndex(itm));
                            }
                        }
                    }

                    pc += 1;
                },
                Instr::ControlIndexPop(count) => {
                    if count > 0 {
                        let clen = self.cstack.len();
                        if clen < count as usize {
                            return Err(ForthError::ControlStackUnderflow);
                        }

                        let i0 = clen-(count as usize);
                        for itm in self.cstack.drain(i0..) {
                            if let ControlEntry::Index(index) = itm {
                                self.dstack.push(Word::int(index));
                            } else {
                                return Err(ForthError::InvalidControlEntry(itm));
                            }
                        }
                    }

                    pc += 1;
                },
                Instr::ControlIndexPeek(ind) => {
                    let clen = self.cstack.len();
                    if clen <= ind as usize {
                        return Err(ForthError::ControlStackUnderflow);
                    }

                    let entry = self.cstack[(clen-1-(ind as usize))];
                    if let ControlEntry::Index(index) = entry {
                        self.push_int(index)?;
                    } else {
                        return Err(ForthError::InvalidControlEntry(entry));
                    }

                    pc += 1;
                },
                Instr::ControlIteration => {
                    let clen = self.cstack.len();
                    if clen < 2 {
                        return Err(ForthError::ControlStackUnderflow);
                    }

                    let top = if let ControlEntry::Index(idx) = self.cstack[clen-2] {
                        idx
                    } else {
                        return Err(ForthError::InvalidControlEntry(self.cstack[clen-2]));
                    };

                    let ind = if let ControlEntry::Index(idx) = self.cstack[clen-1] {
                        idx
                    } else {
                        return Err(ForthError::InvalidControlEntry(self.cstack[clen-1]));
                    };

                    if ind < top {
                        self.cstack[clen-1] = ControlEntry::Index(ind+1);
                        self.push_int(0)?;
                    } else {
                        self.cstack.truncate(clen-2);
                        self.push_int(1)?;
                    }

                    pc += 1;
                },
                Instr::UnaryOp(op) => {
                    self.unary_op(op)?;
                    pc += 1;
                },
                Instr::BinaryOp(op) => {
                    self.binary_op(op)?;
                    pc += 1;
                },
                Instr::EOL => {
                    self.input_eol()?;
                    pc += 1;
                },
                Instr::Lookup => {
                    self.input_lookup()?;
                    pc += 1;
                },
                Instr::DefStr => {
                    self.defstr()?;
                    pc += 1;
                },
                Instr::DefWord => {
                    self.defword()?;
                    pc += 1;
                },

                Instr::Func(x) => {
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
                Instr::Unnest => {
                    let val = self.rstack.pop().ok_or(ForthError::ReturnStackUnderflow)?;
                    let ret = val.to_xt().ok_or_else(|| ForthError::InvalidExecutionToken(val))?;
                    pc = ret.0;
                },
            }
        }
    }
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
    fn words() {
        assert_eq!(Word::int(123).to_int().unwrap(), 123);
        assert_eq!(Word::int(-123).to_int().unwrap(), -123);

        assert_eq!(Word::xt(123).to_xt().unwrap(), XT(123));

        assert_eq!(Word::str(((123 as u32)<<8) | 10).to_str().unwrap(), ST::allocated_space(123, 10));

        assert_eq!(Word::xt(123).to_int(), None);
        assert_eq!(Word::xt(123).to_str(), None);
        assert_eq!(Word::xt(123).to_addr(), None);

        assert_eq!(Word::str(123).to_int(), None);
        assert_eq!(Word::str(123).to_xt(), None);
        assert_eq!(Word::str(123).to_addr(), None);

        assert_eq!(Word::int(123).to_xt(), None);
        assert_eq!(Word::int(123).to_str(), None);
        assert_eq!(Word::int(123).to_addr(), None);

        assert_eq!(Word::int(-123).to_xt(), None);
        assert_eq!(Word::int(-123).to_str(), None);
        assert_eq!(Word::int(-123).to_addr(), None);

        assert_eq!(Word::addr(123), Word(Word::HIGH_BIT | Word::SIGN_BIT | Addr::ADDR_BIT | 123));
        assert_eq!(Word::addr(123), Addr(123).to_word());
        assert_eq!(Word::addr(123).to_addr().unwrap(), Addr(123));
        assert_eq!(Word::addr(123).to_xt(), None);
        assert_eq!(Word::addr(123).to_str(), None);
    }

    #[test]
    #[ignore]
    fn all_xt_values() {
        for x in 0 .. (XT::MAX+1) {
            let w = Word::xt(x);
            assert_eq!(w.to_xt().unwrap(), XT(x), "word {:?} does not convert to XT({}) ", w, x);
            assert_eq!(w.to_int(),  None, "XT({}) incorrectly shares a representation with int", x);
            assert_eq!(w.to_str(),  None, "XT({}) incorrectly shares a representation with ST", x);
            assert_eq!(w.to_addr(), None, "XT({}) incorrectly shares a representation with Addr", x);
        }
    }

    #[test]
    #[ignore]
    fn all_addr_values() {
        for x in 0 .. (Addr::MAX+1) {
            let w = Word::addr(x);
            assert_eq!(w.to_addr().unwrap(), Addr(x), "word {:?} does not convert to Addr({}) ", w, x);
            assert_eq!(w.to_int(), None, "Addr({}) incorrectly shares a representation with int", x);
            assert_eq!(w.to_str(), None, "Addr({}) incorrectly shares a representation with ST", x);
            assert_eq!(w.to_xt(),  None, "Addr({}) incorrectly shares a representation with XT", x);
        }
    }

    #[test]
    #[ignore]
    fn all_int_values() {
        for x in Word::INT_MIN .. (Word::INT_MAX+1) {
            let w = Word::int(x);
            assert_eq!(w.to_int().unwrap(), x, "word {:?} does not convert to integer {} ", w, x);
            assert_eq!(w.to_xt(),  None, "int({}) incorrectly shares a representation with XT", x);
            assert_eq!(w.to_str(), None, "int({}) incorrectly shares a representation with ST", x);
            assert_eq!(w.to_addr(), None, "int({}) incorrectly shares a representation with Addr", x);
        }
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

        let st1 = forth.add_string("string1").unwrap();
        let st2 = forth.add_string("string2").unwrap();

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
            Instr::Push(Word::int(4314)),
            Instr::Push(Word::int(-132)),
            Instr::Push(Word::int(-999)),
            Instr::Swap,
            Instr::Drop,
            Instr::Bye,
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
            Instr::Push(Word::int(4314)),
            Instr::Push(Word::int(-132)),
            Instr::BinaryOp(BinOp::Plus),
            Instr::Push(Word::int(-10)),
            Instr::BinaryOp(BinOp::Star),
            Instr::Bye,
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
        entries[0] = Instr::Push(Word::int(2));
        entries[1] = Instr::BinaryOp(BinOp::Star);
        entries[2] = Instr::Push(Word::int(1));
        entries[3] = Instr::BinaryOp(BinOp::Plus);
        entries[4] = Instr::Unnest;

        let xt1 = forth.add_code(&vec![
            Instr::Push(Word::int(2)),
            Instr::DoCol(xt0),
            Instr::Bye,
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
        entries[0] = Instr::Push(Word::int(2));
        entries[1] = Instr::BinaryOp(BinOp::Star);
        entries[2] = Instr::Push(Word::int(1));
        entries[3] = Instr::BinaryOp(BinOp::Plus);
        entries[4] = Instr::Unnest;

        forth.define_word("my_func", xt).unwrap();

        let lookup_xt = forth.lookup_word("my_func").unwrap();
        assert_eq!(xt, lookup_xt);
    }

    #[test]
    fn can_define_incrementally() {
        let mut forth = ToyForth::new();

        let xt = forth.mark_code();

        /* f(x) = 2*x + 1 */
        forth.add_instr(Instr::Push(Word::int(2)));
        forth.add_instr(Instr::BinaryOp(BinOp::Star));
        forth.add_instr(Instr::Push(Word::int(1)));
        forth.add_instr(Instr::BinaryOp(BinOp::Plus));
        forth.add_instr(Instr::Unnest);

        forth.define_word("my_func", xt).unwrap();

        let lookup_xt = forth.lookup_word("my_func").unwrap();
        assert_eq!(xt, lookup_xt);

        let immed = forth.mark_code();

        forth.add_instr(Instr::Push(Word::int(0)));
        forth.add_instr(Instr::EOL);
        forth.add_instr(Instr::Lookup);
        forth.add_instr(Instr::Bye);

        forth.set_input("my_func");
        forth.exec(immed).unwrap();

        assert_eq!(forth.pop().unwrap(), Word::from_xt(xt));
        assert_eq!(forth.pop(), None);
    }

    #[test]
    fn can_define_word_from_input() {
        let mut forth = ToyForth::new();

        let xt = forth.mark_code();

        /* f(x) = 2*x + 1 */
        forth.add_instr(Instr::Push(Word::int(2)));
        forth.add_instr(Instr::BinaryOp(BinOp::Star));
        forth.add_instr(Instr::Push(Word::int(1)));
        forth.add_instr(Instr::BinaryOp(BinOp::Plus));
        forth.add_instr(Instr::Unnest);

        forth.set_input("my_func");

        {
            let immed = forth.mark_code();
            forth.add_instr(Instr::Push(Word::int(0)));
            forth.add_instr(Instr::EOL);
            forth.add_instr(Instr::DefStr);
            forth.add_instr(Instr::Push(Word::from_xt(xt)));
            forth.add_instr(Instr::DefWord);
            forth.add_instr(Instr::Bye);

            forth.exec(immed).unwrap();
        }

        {
            let immed = forth.mark_code();

            forth.add_instr(Instr::Push(Word::int(0)));
            forth.add_instr(Instr::EOL);
            forth.add_instr(Instr::Lookup);
            forth.add_instr(Instr::Bye);

            forth.exec(immed).unwrap();
        }

        assert_eq!(forth.pop().unwrap(), Word::from_xt(xt));
        assert_eq!(forth.pop(), None);
    }

    #[test]
    fn builtin_word_scans_words() {
        let mut forth = ToyForth::new();

        forth.set_input("  x  test foo bar   ");

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 3);
        assert_eq!(forth.counted_string_at(forth.peek_str().unwrap()), "x");
        assert_eq!(forth.pop().unwrap(), Word::from_str(ST::word_space(0,2)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 9);
        assert_eq!(forth.counted_string_at(forth.peek_str().unwrap()), "test");
        assert_eq!(forth.pop().unwrap(), Word::from_str(ST::word_space(0,5)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 13);
        assert_eq!(forth.counted_string_at(forth.peek_str().unwrap()), "foo");
        assert_eq!(forth.pop().unwrap(), Word::from_str(ST::word_space(0,4)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 17);
        assert_eq!(forth.counted_string_at(forth.peek_str().unwrap()), "bar");
        assert_eq!(forth.pop().unwrap(), Word::from_str(ST::word_space(0,4)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 20);
        let pk = forth.peek().unwrap();
        eprintln!("last word is {:?} - {} - {:b}", pk, pk, pk.0);
        assert_eq!(forth.counted_string_at(forth.peek_str().unwrap()), "");
        assert_eq!(forth.pop().unwrap(), ST::word_space(0,1).to_word());

        // make sure we can search again and it's well behaved...
        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 20);
        let pk = forth.peek().unwrap();
        eprintln!("last word is {:?} - {} - {:b}", pk, pk, pk.0);
        assert_eq!(forth.counted_string_at(forth.peek_str().unwrap()), "");
        assert_eq!(forth.pop().unwrap(), ST::word_space(0,1).to_word());
    }

    #[test]
    fn builtin_char_at_and_char_plus() {
        let mut forth = ToyForth::new();

        forth.set_input("  xtest  ");

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 7);
        assert_eq!(forth.bytes_at(forth.peek_str().unwrap()), &vec![5 as u8, 'x' as u8, 't' as u8, 'e' as u8, 's' as u8, 't' as u8]);
        assert_eq!(forth.counted_string_at(forth.peek_str().unwrap()), "xtest");

        forth.dup().unwrap();
        forth.builtin_char_at().unwrap();
        assert_eq!(forth.pop_int().unwrap(), 5 as i32);

        forth.builtin_char_plus().unwrap();
        assert_eq!(forth.bytes_at(forth.peek_str().unwrap()), &vec!['x' as u8, 't' as u8, 'e' as u8, 's' as u8, 't' as u8]);
        forth.builtin_char_at().unwrap();
        assert_eq!(forth.pop_int().unwrap(), 'x' as i32);

        assert_eq!(forth.stack_depth(), 0);
    }

    #[test]
    fn builtin_parse_scans_words() {
        let mut forth = ToyForth::new();

        forth.set_input("  x  test foo bar   ");

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_parse().unwrap();
        assert_eq!(forth.input_off, 3);
        assert_eq!(forth.pop_int().unwrap(), 1);
        assert_eq!(forth.pop().unwrap(), Word::from_str(ST::input_space(2,1)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_parse().unwrap();
        assert_eq!(forth.input_off, 9);
        assert_eq!(forth.pop_int().unwrap(), 4);
        assert_eq!(forth.pop().unwrap(), Word::from_str(ST::input_space(5,4)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_parse().unwrap();
        assert_eq!(forth.input_off, 13);
        assert_eq!(forth.pop_int().unwrap(), 3);
        assert_eq!(forth.pop().unwrap(), Word::from_str(ST::input_space(10,3)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_parse().unwrap();
        assert_eq!(forth.input_off, 17);
        assert_eq!(forth.pop_int().unwrap(), 3);
        assert_eq!(forth.pop().unwrap(), Word::from_str(ST::input_space(14,3)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_parse().unwrap();
        assert_eq!(forth.input_off, 20);
        assert_eq!(forth.pop_int().unwrap(), 0);
        assert_eq!(forth.pop().unwrap(), ST::input_space(20,0).to_word());

        // make sure we can search again and it's well behaved...
        forth.push_int(' ' as i32).unwrap();
        forth.builtin_parse().unwrap();
        assert_eq!(forth.input_off, 20);
        assert_eq!(forth.pop_int().unwrap(), 0);
        assert_eq!(forth.pop().unwrap(), ST::input_space(20,0).to_word());
    }

    #[test]
    fn builtin_char_scans_first_char_of_words() {
        let mut forth = ToyForth::new();

        forth.set_input("  x  test foo bar   ");

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
    fn can_lookup_token() {
        let mut forth = ToyForth::new();

        let xt = forth.add_word("my_func", &vec![
           Instr::Push(Word::int(2)),
           Instr::BinaryOp(BinOp::Star),
           Instr::Push(Word::int(1)),
           Instr::BinaryOp(BinOp::Plus),
           Instr::Unnest,
        ]).unwrap();

        // look up various things
        forth.set_input("test");
        {
            forth.push_int(' ' as i32).unwrap();
            forth.builtin_word().unwrap();
            let st = forth.peek_str().unwrap();

            forth.builtin_find().unwrap();

            assert_eq!(forth.pop_int().unwrap(), 0);
            assert_eq!(forth.pop_kind().unwrap(), WordKind::Str(st));
        }

        forth.set_input("my_func");
        {
            forth.push_int(' ' as i32).unwrap();
            forth.builtin_word().unwrap();
            forth.builtin_find().unwrap();

            assert_eq!(forth.pop_int().unwrap(), -1);
            assert_eq!(forth.pop_kind().unwrap(), WordKind::XT(xt));
        }
    }

    #[test]
    fn builtin_over() {
        let mut forth = ToyForth::new();

        forth.push_int(1).unwrap();
        forth.push_int(2).unwrap();
        forth.over().unwrap();
        assert_eq!(forth.pop_int().unwrap(), 1);
        assert_eq!(forth.pop_int().unwrap(), 2);
        assert_eq!(forth.pop_int().unwrap(), 1);
    }

    #[test]
    fn builtin_find_name_looks_up_token() {
        let mut forth = ToyForth::new();

        let xt = forth.add_word("my_func", &vec![
           Instr::Push(Word::int(2)),
           Instr::BinaryOp(BinOp::Star),
           Instr::Push(Word::int(1)),
           Instr::BinaryOp(BinOp::Plus),
           Instr::Unnest,
        ]).unwrap();

        // look up various things
        forth.set_input("test");
        {
            forth.push_int(' ' as i32).unwrap();
            forth.builtin_parse().unwrap();

            let len = forth.pop_int().unwrap();
            let st  = forth.pop_str().unwrap();

            forth.push(st.to_word()).unwrap();
            forth.push_int(len).unwrap();

            assert_eq!(len, 4);
            assert_eq!(forth.string_at(st), "test");

            forth.over().unwrap();
            let st = forth.pop_str().unwrap();

            forth.print_stacks("after parse");

            forth.builtin_find_name().unwrap();

            assert_eq!(forth.pop_int().unwrap(), 0);
            assert_eq!(forth.pop_int().unwrap(), len);
            assert_eq!(forth.pop_str().unwrap(), st);
            assert_eq!(forth.stack_depth(), 0);
        }

        forth.set_input("my_func");
        {
            forth.push_int(' ' as i32).unwrap();
            forth.builtin_parse().unwrap();
            forth.builtin_find_name().unwrap();

            assert_eq!(forth.pop_int().unwrap(), -1);
            assert_eq!(forth.pop_kind().unwrap(), WordKind::XT(xt));
        }
    }

    #[test]
    fn can_execute_token() {
        let mut forth = ToyForth::new();

        forth.add_word("my_func", &vec![
           Instr::Push(Word::int(2)),
           Instr::BinaryOp(BinOp::Star),
           Instr::Push(Word::int(1)),
           Instr::BinaryOp(BinOp::Plus),
           Instr::Unnest,
        ]).unwrap();

        forth.push_int(1234).unwrap();

        forth.set_input("my_func");
        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        forth.builtin_find().unwrap();

        assert_eq!(forth.pop_int().unwrap(), -1);
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

        forth.add_primitive("ONE", Instr::Push(Word::int(1))).unwrap();
        forth.add_primitive("TWO", Instr::Push(Word::int(2))).unwrap();

        forth.interpret("ONE DUP").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), 1);
        assert_eq!(forth.pop_int().unwrap(), 1);
    }

    #[test]
    fn builtin_to_number() {
        let mut forth = ToyForth::new();

        forth.push_int(0).unwrap();
        let st = forth.add_string("123").unwrap();
        forth.push(Word::from_str(st)).unwrap();
        forth.push_int(3).unwrap();
        forth.builtin_to_number().unwrap();

        assert_eq!(forth.stack_depth(), 3);
        assert_eq!(forth.pop_int().unwrap(), 3);
        assert_eq!(forth.pop_str().unwrap(), st.offset(3));
        assert_eq!(forth.pop_int().unwrap(), 123);

        forth.push_int(0).unwrap();
        let st = forth.add_string("54a3").unwrap();
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

        forth.interpret("-1 2 +").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 1);
    }

    #[test]
    fn use_return_stack() {
        let mut forth = ToyForth::new();

        // handle underflow
        assert!(matches!(forth.builtin_data_to_ret().unwrap_err(), ForthError::StackUnderflow));
        assert!(matches!(forth.builtin_ret_to_data().unwrap_err(), ForthError::StackUnderflow));

        forth.push_int(1).unwrap();
        forth.push_int(2).unwrap();

        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.rstack_depth(), 0);

        forth.builtin_data_to_ret().unwrap();

        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.rstack_depth(), 1);

        assert_eq!(forth.dstack.last().map(|x| *x).unwrap(), Word::int(1));
        assert_eq!(forth.rstack.last().map(|x| *x).unwrap(), Word::int(2));

        forth.push_int(3).unwrap();
        forth.builtin_ret_to_data().unwrap();

        assert_eq!(forth.stack_depth(), 3);
        assert_eq!(forth.rstack_depth(), 0);

        assert_eq!(forth.pop_int().unwrap(), 2);
        assert_eq!(forth.pop_int().unwrap(), 3);
        assert_eq!(forth.pop_int().unwrap(), 1);
    }

    #[test]
    fn builtin_constant() {
        let mut forth = ToyForth::new();
        forth.interpret("123 CONSTANT X123").unwrap();
        assert_eq!(forth.stack_depth(), 0);

        forth.interpret("X123").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 123);
    }

    #[test]
    fn can_colon_define_word() {
        let mut forth = ToyForth::new();

        forth.interpret(": my_word 2 * 1 + ;").unwrap();
        assert_eq!(forth.stack_depth(), 0);

        forth.interpret("13 my_word").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 27);
    }

    #[test]
    fn can_allocate_and_use_vars() {
        let mut forth = ToyForth::new();

        let addr = forth.new_var(Word::int(0)).unwrap();
        assert_eq!(forth.get_var_at(addr).unwrap(), Word::int(0));

        forth.set_var_at(addr, Word::int(123)).unwrap();
        assert_eq!(forth.get_var_at(addr).unwrap(), Word::int(123));
    }

    #[test]
    fn forth_can_allocate_and_use_vars() {
        let mut forth = ToyForth::new();

        let base = Addr(forth.addr_here());

        forth.interpret("VARIABLE V1").unwrap();
        assert_eq!(forth.stack_depth(), 0);

        forth.interpret("V1").unwrap();
        assert_eq!(forth.stack_depth(), 1);

        assert_eq!(forth.pop_addr().unwrap(), base);
        assert_eq!(forth.stack_depth(), 0);

        forth.interpret("999 V1 !").unwrap();
        assert_eq!(forth.stack_depth(), 0);

        forth.interpret("V1 @").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 999);
    }

    #[test]
    fn can_query_special_vars() {
        let mut forth = ToyForth::new();

        forth.interpret("STATE").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_addr().unwrap(), ToyForth::ADDR_STATE);

        forth.interpret("STATE @").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 0);
    }

    #[test]
    fn comparisons() {
        let mut forth = ToyForth::new();

        // 5,3
        forth.interpret("5 3 >").unwrap();
        assert_eq!(forth.pop_int().unwrap(), 1);

        forth.interpret("5 3 <").unwrap();
        assert_eq!(forth.pop_int().unwrap(), 0);

        forth.interpret("5 3 =").unwrap();
        assert_eq!(forth.pop_int().unwrap(), 0);

        forth.interpret("5 3 <>").unwrap();
        assert_eq!(forth.pop_int().unwrap(), 1);

        // 3,5
        forth.interpret("3 5 >").unwrap();
        assert_eq!(forth.pop_int().unwrap(), 0);

        forth.interpret("3 5 <").unwrap();
        assert_eq!(forth.pop_int().unwrap(), 1);

        forth.interpret("3 5 =").unwrap();
        assert_eq!(forth.pop_int().unwrap(), 0);

        forth.interpret("3 5 <>").unwrap();
        assert_eq!(forth.pop_int().unwrap(), 1);

        // 3,3
        forth.interpret("3 3 =").unwrap();
        assert_eq!(forth.pop_int().unwrap(), 1);

        forth.interpret("3 3 >").unwrap();
        assert_eq!(forth.pop_int().unwrap(), 0);

        forth.interpret("3 3 <").unwrap();
        assert_eq!(forth.pop_int().unwrap(), 0);

        forth.interpret("3 3 <>").unwrap();
        assert_eq!(forth.pop_int().unwrap(), 0);
    }

    #[test]
    fn if_else_then() {
        let mut forth = ToyForth::new();

        forth.interpret(": foo dup 5 > if . 123 else . 456 then ;").unwrap();
        forth.print_word_code("foo");

        forth.interpret("7 foo").unwrap();
        assert_eq!(forth.pop_int().unwrap(), 123);

        forth.interpret("1 foo").unwrap();
        assert_eq!(forth.pop_int().unwrap(), 456);
    }

    #[test]
    fn single_loop() {
        let mut forth = ToyForth::new();

        forth.interpret(": foo 3 1 do dup . 5 + loop ;").unwrap();

        let foo_xt = forth.lookup_word("foo").unwrap();
        for (i,instr) in forth.code[foo_xt.0 as usize..].iter().enumerate() {
            eprintln!("[{:3}] {:?}", i, instr);
            if let Instr::Unnest = *instr {
                break
            }
        }

        forth.interpret("10 foo").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 25);

        forth.interpret("1 foo").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 16);
    }

    #[test]
    fn double_loop() {
        let mut forth = ToyForth::new();
        let outv = Rc::new(RefCell::new(Vec::<u8>::new()));

        forth.capture_interpret(
            ": foo \
    3 1 do \
        3 1 do \
            [CHAR] I EMIT \
            BL EMIT \
            J . \
            BL EMIT \
            BL EMIT \
            [CHAR] J EMIT \
            BL EMIT \
            I . \
            CR \
        LOOP \
    LOOP \
    ; \
    foo",
            outv.clone()
        ).unwrap();

        assert_eq!(forth.stack_depth(), 0);

        if let Ok(s) = std::str::from_utf8(&outv.borrow()) {
            eprintln!("output is\n{}", s);
            assert_eq!(s, "I 1  J 1
I 1  J 2
I 1  J 3
I 2  J 1
I 2  J 2
I 2  J 3
I 3  J 1
I 3  J 2
I 3  J 3
");
        };
    }

    #[test]
    fn bracket_char() {
        let mut forth = ToyForth::new();
        let outv = Rc::new(RefCell::new(Vec::<u8>::new()));

        forth.capture_interpret(
            ": XX [CHAR] X EMIT CR ; XX",
            outv.clone()
        ).unwrap();

        assert_eq!(forth.stack_depth(), 0);

        if let Ok(s) = std::str::from_utf8(&outv.borrow()) {
            eprintln!("output is\n{}", s);
            assert_eq!(s, "X\n");
        };
    }
}

