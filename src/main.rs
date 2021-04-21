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
    const BUILTIN : u32 = 0x1000_0000;

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

    fn bool(b: bool) -> Word {
        if b { Word::true_value() } else { Word::false_value() }
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
    ControlIndexDrop(u8),
    ControlIteration,
    ControlIndexPeek(u32),
    ReturnPush,
    ReturnPop,
    ReturnCopy,
    Execute,
    EOL,
    Lookup,
    DefStr,
    DefWord,
    Func(u32),
    DoCol(XT),
    Exit,               // redundant with Unnest... but Unnest currently marks the end of a function
    Unnest,
}

#[derive(Debug,Clone,Copy,PartialEq,Eq)]
#[repr(u8)]
enum UnaryOp {
    Negate,
    Invert,
}

#[derive(Debug,Clone,Copy,PartialEq,Eq)]
#[repr(u8)]
enum BinOp {
    Plus,
    Minus,
    Star,
    Slash,

    And,
    Or,
    Xor,

    Greater,
    Less,
    Equal,
    NotEqual,

    UnsignedGreater,
    UnsignedLess,
}

#[derive(Debug,Clone,Copy,PartialEq,Eq)]
enum ControlEntry {
    IfAddr(XT),
    ElseAddr(XT),

    DoAddr(XT),
    BeginAddr(XT),
    WhileAddr{ head: XT, cond: XT },
    LeaveAddr{ head: XT, leave: XT },

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

    InvalidNumberBase,
    NumberOutOfRange,

    InvalidEmptyString,
    StringTooLong,
    StringOffsetTooLarge,
    StringNotFound,

    FunctionSpaceOverflow,
    DictSpaceOverflow,
    VarSpaceOverflow,
    StringSpaceOverflow,

    WordInvalidWhileCompiling,
    WordInvalidWhileInterpreting,
    DefiningWordInvalid,
    UnfinishedColonDefinition,
    DictEmpty,

    NoMatchingLoopHead,

    NotImplemented,

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
    const ADDR_BASE:       Addr = Addr(1);
    const ADDR_SLASH_CDEF: Addr = Addr(2);
    const ADDR_SLASH_CXT:  Addr = Addr(3);
    const ADDR_SLASH_BRACKET:  Addr = Addr(4);

    // special variables
    const ADDR_HERE   : Addr = Addr(Addr::BUILTIN | 0);
    const ADDR_UNUSED : Addr = Addr(Addr::BUILTIN | 1);
    const ADDR_IN     : Addr = Addr(Addr::BUILTIN | 2);

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

        tf.add_prim("EXECUTE", Instr::Execute);

        tf.add_prim("+", Instr::BinaryOp(BinOp::Plus));
        tf.add_prim("-", Instr::BinaryOp(BinOp::Minus));
        tf.add_prim("*", Instr::BinaryOp(BinOp::Star));
        tf.add_prim("/", Instr::BinaryOp(BinOp::Slash));

        tf.add_prim("AND", Instr::BinaryOp(BinOp::And));
        tf.add_prim("OR", Instr::BinaryOp(BinOp::Or));
        tf.add_prim("XOR", Instr::BinaryOp(BinOp::Xor));

        tf.add_prim("NEGATE", Instr::UnaryOp(UnaryOp::Negate));
        tf.add_prim("INVERT", Instr::UnaryOp(UnaryOp::Invert));

        tf.add_prim(">", Instr::BinaryOp(BinOp::Greater));
        tf.add_prim("<", Instr::BinaryOp(BinOp::Less));
        tf.add_prim("=", Instr::BinaryOp(BinOp::Equal));
        tf.add_prim("<>", Instr::BinaryOp(BinOp::NotEqual));

        tf.add_prim("U>", Instr::BinaryOp(BinOp::UnsignedGreater));
        tf.add_prim("U<", Instr::BinaryOp(BinOp::UnsignedLess));

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

        tf.add_immed("EXIT", ToyForth::builtin_exit);

        tf.add_immed("[CHAR]", ToyForth::builtin_brak_char);

        tf.add_immed("IF", ToyForth::builtin_if);
        tf.add_immed("ELSE", ToyForth::builtin_else);
        tf.add_immed("THEN", ToyForth::builtin_then);

        tf.add_immed("DO", ToyForth::builtin_do);
        tf.add_immed("LOOP", ToyForth::builtin_loop);
        tf.add_immed("I", ToyForth::builtin_loop_ind0);
        tf.add_immed("J", ToyForth::builtin_loop_ind1);

        tf.add_immed("LEAVE", ToyForth::builtin_leave);

        tf.add_immed("BEGIN", ToyForth::builtin_begin);
        tf.add_immed("AGAIN", ToyForth::builtin_again);
        tf.add_immed("UNTIL", ToyForth::builtin_until);
        tf.add_immed("WHILE", ToyForth::builtin_while);
        tf.add_immed("REPEAT", ToyForth::builtin_repeat);

        tf.add_immed("RECURSE", ToyForth::builtin_recurse);

        tf.add_func("IMMEDIATE", ToyForth::builtin_immediate);

        tf.add_func("FIND", ToyForth::builtin_find);

        tf.add_func(">NUMBER", ToyForth::builtin_to_number);

        // should these be prims?
        tf.add_immed(">R", ToyForth::builtin_data_to_ret);
        tf.add_immed("R>", ToyForth::builtin_ret_to_data);
        tf.add_immed("R@", ToyForth::builtin_ret_copy_to_data);

        tf.add_func("CONSTANT", ToyForth::builtin_constant);
        tf.add_func("VARIABLE", ToyForth::builtin_variable);

        tf.add_func("!", ToyForth::builtin_var_set);
        tf.add_func("@", ToyForth::builtin_var_get);

        tf.add_func("TYPE", ToyForth::builtin_type);
        tf.add_immed("S\"", ToyForth::builtin_s_quote);
        tf.add_immed(".\"", ToyForth::builtin_dot_quote);

        tf.add_immed(".(", ToyForth::builtin_dot_oparen);
        tf.add_immed("(", ToyForth::builtin_oparen);
        tf.add_immed("\\", ToyForth::builtin_backslash);

        tf.add_func("/ETYPE", ToyForth::builtin_err_type);
        tf.add_immed("E\"", ToyForth::builtin_err_quote);

        tf.add_immed("[", ToyForth::builtin_obracket);
        tf.add_immed("]", ToyForth::builtin_cbracket);
        tf.add_immed("LITERAL", ToyForth::builtin_literal);

        tf.add_func("'", ToyForth::builtin_tick);
        tf.add_immed("[']", ToyForth::builtin_brak_tick);

        // debugging
        tf.add_func("/STACKS", ToyForth::builtin_at_stacks);
        tf.add_func("/CODE", ToyForth::builtin_at_code);

        // define state variables
        //
        // FIXME: instead of /CDEF and /CXT, we should store the nest-sys
        // on the return stack.
        //
        let state_vars = vec![ "STATE", "BASE", "/CDEF", "/CXT", "/BRACKET" ];
        for v in &state_vars {
            let addr = tf.new_var(Word(0)).unwrap();
            tf.add_prim(v, Instr::Push(addr.to_word()));
        }

        tf.set_var_at(ToyForth::ADDR_BASE, Word::int(10)).unwrap();

        // Add builtins
        tf.add_prim(">IN",    Instr::Push(ToyForth::ADDR_IN.to_word()));

        tf.add_func("HERE",   ToyForth::builtin_here);
        tf.add_func("UNUSED", ToyForth::builtin_unused);

        // define standard words that are not primitives
        tf.add_word("CR", &[
            Instr::Push(Word::int('\n' as i32)),
            Instr::Func(emit as u32),
            Instr::Unnest,
        ]).unwrap();

        tf.interpret("\
: 0<  0 < ;
: 0>  0 > ;
: 0=  0 = ;
: 0<> 0 <> ;
: 1- 1 - ;
: 1+ 1 + ;

0    CONSTANT FALSE
0 0= CONSTANT TRUE

: DECIMAL 10 BASE ! ;
: HEX     16 BASE ! ;

: ABS DUP 0< IF NEGATE THEN ;

: +! SWAP OVER @ + SWAP ! ;

: NIP  SWAP DROP ;
: TUCK SWAP OVER ;

: PARSE-NAME BL PARSE ;

: SPACE BL EMIT ;
: SPACES DUP 0> IF 1 DO SPACE LOOP THEN ; 

: 2DUP ( n1 n2 -- n1 n2 n1 n2 ) OVER OVER ;

: MIN ( n1 n1 -- n3 ) 2DUP > IF SWAP THEN DROP ;
: MAX ( n1 n1 -- n3 ) 2DUP < IF SWAP THEN DROP ;

").unwrap();

        // tf.add_func("PARSE-NAME", ToyForth::builtin_parse);

        eprintln!("Code cell size is {}", std::mem::size_of::<Instr>());
        eprintln!("Data cell size is {}", std::mem::size_of::<Word>());

        return tf;
    }

    fn cpush_if_addr(&mut self, xt: XT) {
        self.cstack.push(ControlEntry::IfAddr(xt));
    }

    fn cpush_else_addr(&mut self, xt: XT) {
        self.cstack.push(ControlEntry::ElseAddr(xt));
    }

    fn cpush_do_addr(&mut self, xt: XT) {
        self.cstack.push(ControlEntry::DoAddr(xt));
    }

    fn cpush_begin_addr(&mut self, xt: XT) {
        self.cstack.push(ControlEntry::BeginAddr(xt));
    }

    fn cpush_while(&mut self, head_xt: XT, cond_xt: XT) {
        self.cstack.push(ControlEntry::WhileAddr{ head: head_xt, cond: cond_xt });
    }

    fn cpush_index(&mut self, idx: i32) {
        self.cstack.push(ControlEntry::Index(idx));
    }

    fn cpop_entry(&mut self) -> Result<ControlEntry,ForthError> {
        self.cstack.pop().ok_or(ForthError::ControlStackUnderflow)
    }

    fn cpop_loop_addr(&mut self) -> Result<XT, ForthError> {
        let ctl = self.cpop_entry()?;
        if let ControlEntry::DoAddr(xt) = ctl {
            Ok(xt)
        } else {
            Err(ForthError::InvalidControlEntry(ctl))
        }
    }

    fn cpop_begin_addr(&mut self) -> Result<XT, ForthError> {
        let ctl = self.cpop_entry()?;
        if let ControlEntry::BeginAddr(xt) = ctl {
            Ok(xt)
        } else {
            Err(ForthError::InvalidControlEntry(ctl))
        }
    }

    fn cpop_while_entry(&mut self) -> Result<(XT,XT), ForthError> {
        let ctl = self.cpop_entry()?;
        if let ControlEntry::WhileAddr{head, cond} = ctl {
            Ok((head,cond))
        } else {
            Err(ForthError::InvalidControlEntry(ctl))
        }
    }

    fn cpop_index(&mut self) -> Result<i32,ForthError> {
        let ctl = self.cpop_entry()?;
        if let ControlEntry::Index(idx) = ctl {
            Ok(idx)
        } else {
            Err(ForthError::InvalidControlEntry(ctl))
        }
    }

    fn cpeek_index(&mut self) -> Result<i32,ForthError> {
        let ctl = self.cstack.last().ok_or(ForthError::ControlStackUnderflow)?;
        if let ControlEntry::Index(idx) = ctl {
            Ok(*idx)
        } else {
            Err(ForthError::InvalidControlEntry(*ctl))
        }
    }

    pub fn print_code(&self, xt: XT) {
        use std::collections::HashMap;

        let mut xt_map = HashMap::<u32,&str>::with_capacity(self.dict.len());
        for ent in &self.dict {
            let w = self.string_at(ent.st);
            xt_map.insert(ent.xt.0, w);
        };

        for (i,instr) in self.code[xt.0 as usize..].iter().enumerate() {
            let istr = format!("{:?}", instr);
            match instr {
                Instr::DoCol(xt) => {
                    let name = xt_map[&xt.0];
                    eprintln!("[{:3}] {:40}  | {}", i, istr, name);
                },
                _ => {
                    eprintln!("[{:3}] {:40}", i, istr);
                }
            };

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

    pub fn builtin_at_code(&mut self) -> Result<(),ForthError> {
        self.push_int(' ' as i32)?;
        self.builtin_parse()?;

        let _len = self.pop_int()?;
        let st = self.pop_str()?;

        let w = self.maybe_string_at(st)?;

        self.print_word_code(w);
        Ok(())
    }

    pub fn builtin_at_stacks(&mut self) -> Result<(),ForthError> {
        self.print_stacks("[ /STACKS ]");
        Ok(())
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

        for l in s.lines() {
            self.set_input(l);
            self.builtin_interpret()?;
        }

        Ok(())
    }

    pub fn compiling(&self) -> bool {
        let ind = ToyForth::ADDR_STATE.0 as usize;
        return self.vars[ind].to_int().unwrap_or(0) != 0;
    }

    pub fn check_compiling(&self) -> Result<(), ForthError> {
        if self.compiling() {
            Ok(())
        } else {
            Err(ForthError::WordInvalidWhileInterpreting)
        }
    }

    pub fn check_interpreting(&self) -> Result<(), ForthError> {
        if !self.compiling() {
            Ok(())
        } else {
            Err(ForthError::WordInvalidWhileCompiling)
        }
    }

    pub fn check_not_in_bracket(&self) -> Result<(), ForthError> {
        // this should always exist... there's an error in the forth system if
        // it doesn't...
        let w = self.get_var_at(ToyForth::ADDR_SLASH_BRACKET).unwrap();

        if w == Word(0) {
            Ok(())
        } else {
            Err(ForthError::DefiningWordInvalid)
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

                self.data_to_ret()?;    // ( caddr u -- caddr )           r: ( -- u )
                self.dup()?;                    // ( caddr -- caddr caddr )       r: ( u -- u )
                self.builtin_char_at()?;        // ( caddr caddr -- caddr ch )    r: ( u -- u )
                self.push_int('-' as i32)?;     // ( caddr ch -- caddr ch '-' )   r: ( u -- u )
                self.binary_op(BinOp::Equal)?;      // ( caddr ch '-' -- caddr neg? ) r: ( u -- u )
                self.swap()?;                   // ( caddr neg? -- neg? caddr )   r: ( u -- u )
                self.over()?;                   // ( neg? caddr -- neg? caddr neg? ) r: ( u -- u )

                // self.print_stacks("-1-");

                if self.pop_int()? != 0 {       // ( neg? caddr neg? -- neg? caddr ) r: ( u -- u )
                    self.builtin_char_plus()?;  // ( neg? caddr -- neg? caddr2 )
                    self.ret_to_data()?; // ( neg? caddr2 -- neg? caddr2 u ) r: ( u -- )
                    let u = self.pop_int()?;    // ( neg? caddr2 u -- neg? caddr2 ) r: ( -- )
                    self.push_int(u - 1)?;      // ( neg? caddr2 -- neg? caddr2 u2 ) r: ( -- )

                    len -= 1;

                    self.data_to_ret()?;    // ( neg? caddr2 u2 -- neg? caddr2 )  r: ( -- u2 )
                    // self.print_stacks("-2-");
                }

                self.push_int(0)?;              // ( neg? caddr -- neg? caddr 0 ) r: ( u -- u )
                self.swap()?;                   // ( neg? caddr 0 -- neg? 0 caddr ) r: ( u -- u )

                self.ret_to_data()?;    // ( neg? 0 caddr -- neg? 0 caddr u ) r: ( u -- )

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
            let r = inp.borrow();
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

        if let Some(out) = &self.out_stream {
            let mut w = out.borrow_mut();
            // let buf : [u8;1] = [ ch as u8 ];
            // w.write(&buf)?;
            w.write(&[ ch as u8 ])?;
        }
        Ok(())
    }

    pub fn write_prompt(&mut self, prompt: &str) -> Result<(), ForthError> {
        if let Some(out) = &self.out_stream {
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

    pub fn cstack_depth(&self) -> usize {
        return self.cstack.len();
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

    fn data_to_ret(&mut self) -> Result<(), ForthError> {
        let w = self.dstack.pop().ok_or(ForthError::StackUnderflow)?;
        self.rstack.push(w);
        Ok(())
    }

    fn ret_to_data(&mut self) -> Result<(), ForthError> {
        let w = self.rstack.pop().ok_or(ForthError::StackUnderflow)?;
        self.dstack.push(w);
        Ok(())
    }

    fn ret_copy_to_data(&mut self) -> Result<(), ForthError> {
        let w = self.rstack.last().ok_or(ForthError::StackUnderflow)?;
        self.dstack.push(*w);
        Ok(())
    }

    fn builtin_data_to_ret(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;
        self.add_instr(Instr::ReturnPush);
        Ok(())
    }

    fn builtin_ret_to_data(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;
        self.add_instr(Instr::ReturnPop);
        Ok(())
    }

    fn builtin_ret_copy_to_data(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;
        self.add_instr(Instr::ReturnCopy);
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

    fn get_var_at(&self, addr: Addr) -> Result<Word, ForthError> {
        if (addr.0 & Addr::BUILTIN) != 0 {
            match addr {
                ToyForth::ADDR_IN => { return Ok(Word::int(self.input_off as i32)) },
                _ => { return Err(ForthError::InvalidAddress(addr)) }
            }
        } else {
            let ind = addr.0 as usize;
            if ind < self.vars.len() {
                Ok(self.vars[ind])
            } else {
                Err(ForthError::InvalidAddress(addr))
            }
        }
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
            UnaryOp::Invert => {
                let inverted = !(a as u32);
                self.push(Word(inverted & Word::INT_MASK))?;
                Ok(())
            },
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

            BinOp::And      => { self.push(Word::int(((a as u32) & (b as u32)) as i32))?; },
            BinOp::Or       => { self.push(Word::int(((a as u32) | (b as u32)) as i32))?; },
            BinOp::Xor      => { self.push(Word::int(((a as u32) ^ (b as u32)) as i32))?; },

            BinOp::Greater  => { self.push(Word::bool(a > b ))?; },
            BinOp::Less     => { self.push(Word::bool(a < b ))?; },
            BinOp::Equal    => { self.push(Word::bool(a == b))?; },
            BinOp::NotEqual => { self.push(Word::bool(a != b))?; },

            BinOp::UnsignedGreater => { self.push(Word::bool( (a as u32) > (b as u32) ))?; },
            BinOp::UnsignedLess    => { self.push(Word::bool( (a as u32) < (b as u32) ))?; },
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
        let base_var = self.get_var_at(ToyForth::ADDR_BASE)?;
        let base_signed = base_var.to_int().ok_or(ForthError::InvalidNumberBase)?;

        if base_signed < 0 || base_signed > 36 {
            return Err(ForthError::InvalidNumberBase);
        }

        let base : u32 = base_signed as u32; // 10; // FIXME!

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

    fn builtin_recurse(&mut self) -> Result<(),ForthError> {
        self.check_compiling()?;

        let xt = self.get_var_at(ToyForth::ADDR_SLASH_CXT)?.to_xt().ok_or(ForthError::InvalidArgument)?; // XXX: need better error
        self.add_instr(Instr::DoCol(xt));
        Ok(())
    }

    fn builtin_immediate(&mut self) -> Result<(),ForthError> {
        let entry = self.dict.last_mut().ok_or(ForthError::DictEmpty)?;
        entry.flags |= DictEntry::IMMEDIATE;

        Ok(())
    }

    fn builtin_tick(&mut self) -> Result<(),ForthError> {
        let st = self.next_word(' ' as u8, u8::MAX as usize)?;

        let s = self.maybe_string_at(st)?;
        let xt = self.lookup_word(s)?;

        self.push(xt.to_word())?;
        Ok(())
    }

    fn builtin_brak_tick(&mut self) -> Result<(),ForthError> {
        self.check_compiling()?;

        let st = self.next_word(' ' as u8, u8::MAX as usize)?;

        let s = self.maybe_string_at(st)?;
        let xt = self.lookup_word(s)?;

        self.add_instr(Instr::Push(xt.to_word()));
        Ok(())
    }

    fn builtin_execute(&mut self) -> Result<(),ForthError> {
        if self.compiling() {
            self.add_instr(Instr::Execute);
        } else {
            let xt = self.pop_xt()?;
            self.ret_push_bye()?;
            self.exec(xt)?;
        }

        Ok(())
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

    fn scan_word(bytes: &[u8], delim: u8) -> (usize, usize, usize) {
        let n = bytes.len();

        // skip any leading delimiters
        let mut w0 = 0;
        while w0 < n && bytes[w0] == delim {
            w0 += 1;
        }

        // search for next delimiter
        let mut w1 = w0;
        while w1 < n && bytes[w1] != delim {
            w1 += 1;
        }

        // skip any trailing delimiters
        let mut w2 = w1;
        while w2 < n && bytes[w2] == delim {
            w2 += 1;
        }

        (w0,w1,w2)
    }

    fn builtin_dot(&mut self) -> Result<(), ForthError> {
        let w = self.pop().ok_or(ForthError::StackUnderflow)?;

        if let Some(out) = &mut self.out_stream {
            let mut wr = out.borrow_mut();

            if let WordKind::Int(n) = w.kind() {
                write!(wr, "{} ", n)?;
            } else {
                write!(wr, "{} ", w)?;
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
        self.check_not_in_bracket()?;

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
        self.check_compiling()?;

        self.add_instr(Instr::Unnest);
        let st = self.get_var_at(ToyForth::ADDR_SLASH_CDEF)?.to_str().ok_or(ForthError::InvalidArgument)?; // XXX: need better error
        let xt = self.get_var_at(ToyForth::ADDR_SLASH_CXT)?.to_xt().ok_or(ForthError::InvalidArgument)?; // XXX: need better error

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

    fn builtin_exit(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        // TODO: add checks for loops that need to be UNLOOP'd
        //
        // TODO: automatically UNLOOP the loops?
        self.add_instr(Instr::Exit);

        Ok(())
    }

    fn builtin_unloop(&mut self) -> Result<(), ForthError> {
        Err(ForthError::NotImplemented)
    }

    fn builtin_obracket(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;
        self.set_var_at(ToyForth::ADDR_SLASH_BRACKET, Word::int(1))?;
        self.set_var_at(ToyForth::ADDR_STATE, Word::int(0))?;
        Ok(())
    }

    fn builtin_cbracket(&mut self) -> Result<(), ForthError> {
        self.check_interpreting()?;
        self.set_var_at(ToyForth::ADDR_SLASH_BRACKET, Word::int(0))?;
        self.set_var_at(ToyForth::ADDR_STATE, Word::int(1))?;
        Ok(())
    }

    fn builtin_literal(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        let w = self.pop().ok_or(ForthError::StackUnderflow)?;
        self.add_instr(Instr::Push(w));

        Ok(())
    }

    fn builtin_if(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        // add branch, fixup cstack reference later
        let xt = self.add_instr(Instr::BranchOnZero(0));
        self.cpush_if_addr(xt);

        Ok(())
    }

    fn builtin_then(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        let xt = self.mark_code();

        let ctl = self.cpop_entry()?;
        match ctl {
            ControlEntry::IfAddr(if_xt) => {
                // XXX: check for overflow
                let delta : i32 = ((xt.0 as i64) - (if_xt.0 as i64)) as i32;
                self.code[if_xt.0 as usize] = Instr::BranchOnZero(delta);
            },
            ControlEntry::ElseAddr(else_xt) => {
                let delta : i32 = ((xt.0 as i64) - (else_xt.0 as i64)) as i32;
                self.code[else_xt.0 as usize] = Instr::Branch(delta);
            },
            _ => {
                return Err(ForthError::InvalidControlEntry(ctl));
            },
        };

        Ok(())
    }

    fn builtin_else(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        let ctl = self.cpop_entry()?;
        if let ControlEntry::IfAddr(if_xt) = ctl {
            let else_xt = self.add_instr(Instr::Branch(0));
            let xt = self.mark_code();

            let delta : i32 = ((xt.0 as i64) - (if_xt.0 as i64)) as i32;
            self.code[if_xt.0 as usize] = Instr::BranchOnZero(delta);

            self.cpush_else_addr(else_xt);
        } else {
            return Err(ForthError::InvalidControlEntry(ctl));
        }

        Ok(())
    }

    fn builtin_begin(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        let xt = self.mark_code();
        self.cpush_begin_addr(xt);
        Ok(())
    }

    fn builtin_again(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        let begin_xt = self.cpop_begin_addr()?;

        // branch back to BEGIN
        let xt = self.mark_code();
        let delta : i32 = ((begin_xt.0 as i64) - (xt.0 as i64)) as i32;
        self.add_instr(Instr::Branch(delta));

        Ok(())
    }

    fn builtin_until(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        let begin_xt = self.cpop_begin_addr()?;

        // branch back to BEGIN
        let xt = self.mark_code();
        let delta : i32 = ((begin_xt.0 as i64) - (xt.0 as i64)) as i32;
        self.add_instr(Instr::BranchOnZero(delta));

        Ok(())
    }

    fn builtin_while(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        let begin_xt = self.cpop_begin_addr()?;

        // branch back to BEGIN
        let xt = self.mark_code();
        self.add_instr(Instr::BranchOnZero(0));

        self.cpush_while(begin_xt, xt);

        Ok(())
    }

    fn builtin_repeat(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        let (head_xt,cond_xt) : (XT,XT) = self.cpop_while_entry()?;

        // branch back to BEGIN
        let xt = self.mark_code();
        let loop_delta : i32 = ((head_xt.0 as i64) - (xt.0 as i64)) as i32;
        self.add_instr(Instr::Branch(loop_delta));

        // update WHILE branch
        let post_loop_xt = self.mark_code();
        let while_delta : i32 = ((post_loop_xt.0 as i64) - (cond_xt.0 as i64)) as i32;

        self.code[cond_xt.0 as usize] = Instr::BranchOnZero(while_delta);

        Ok(())
    }

    fn builtin_leave(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        /* search the control stack for the last loop entry
         *
         * XXX: important when allowing colon-within-colon
         *      that we protect the control stack across
         *      colon-defs.
         */

        let (i,do_xt) = self.cstack.iter().copied().enumerate().rev().find_map(
            |(i,itm)| if let ControlEntry::DoAddr(xt) = itm { Some((i,xt)) } else { None }).ok_or(ForthError::NoMatchingLoopHead)?;

        self.add_instr(Instr::ControlIndexDrop(2));
        let leave_xt = self.add_instr(Instr::Branch(0));
        self.cstack[i] = ControlEntry::LeaveAddr{ head: do_xt, leave: leave_xt };
        Ok(())
    }

    fn builtin_do(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        // loop header
        self.add_code(&[
            Instr::ControlIndexPush(2),
        ]);

        let xt = self.mark_code();
        self.cpush_do_addr(xt);
        Ok(())
    }

    fn builtin_loop(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        let do_xt : XT;
        let mut leave_xts : Vec<XT> = Vec::new();

        let entry = self.cpop_entry()?;
        match entry {
            ControlEntry::DoAddr(xt) => {
                do_xt = xt;
            },

            ControlEntry::LeaveAddr{head:xt, leave: leave_xt} => {
                do_xt = xt;
                leave_xts.push(leave_xt);
            },

            _ => {
                return Err(ForthError::InvalidControlEntry(entry));
            },
        };

        // ControlIteration: ( -- 0 | 1 ) (C: n1 n2 -- n1 n3 | )
        // if n2<n1, pushes n1 and n3=n2-1 onto the control stack, pushes 0 onto the data stack
        // if n2>=1, pops n1,n2 from the control stack, pushes 1 onto the data stack
        self.add_instr(Instr::ControlIteration);

        // branch back to DO (after loop header)
        {
            let xt = self.mark_code();
            let delta : i32 = ((do_xt.0 as i64) - (xt.0 as i64)) as i32;
            self.add_instr(Instr::BranchOnZero(delta));
        }

        {
            let after_xt = self.mark_code();
            for xt in leave_xts {
                let delta = ((after_xt.0 as i64) - (xt.0 as i64)) as i32;
                self.code[xt.0 as usize] = Instr::Branch(delta);
            }
        }

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

    fn next_word(&mut self, delim: u8, max_len: usize) -> Result<ST, ForthError> {
        let off0 = self.input_off;
        let bytes = self.input.as_bytes();
        let (w0,w1,w2) = ToyForth::scan_word(&bytes[off0..], delim);

        let word_off = off0 + w0;
        let word_end = off0 + w1;
        self.input_off = off0 + w2;

        let len = word_end - word_off;
        if len >= max_len {
            return Err(ForthError::StringTooLong);
        }

        // TODO: Handle large offset by copying to word space?
        if word_off > 255 {
            return Err(ForthError::StringTooLong);
        }

        Ok(ST::input_space(word_off as u8,len as u8))
    }

    // [CHAR]
    fn builtin_brak_char(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        let st = self.next_word(' ' as u8, u8::MAX as usize)?;

        let b = self.bytes_at(st);
        if b.len() == 0 {
            return Err(ForthError::InvalidEmptyString);
        }

        let ch = b[0];
        let w = Word::int(ch as i32);
        self.add_instr(Instr::Push(w));
        Ok(())
    }

    fn builtin_char(&mut self) -> Result<(), ForthError> {
        let st = self.next_word(' ' as u8, u8::MAX as usize)?;

        let b = self.bytes_at(st);
        if b.len() == 0 {
            return Err(ForthError::InvalidEmptyString);
        }

        let ch = b[0];
        self.push_int(ch as i32)?;
        Ok(())
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

        let max_len = self.word.len();
        let st = self.next_word(delim, std::cmp::min(u8::MAX as usize,max_len-1))?;

        let len = st.len() as usize;

        // if only there was some way to avoid making this copy...
        let tmp = self.bytes_at(st).to_vec();

        let wstr : &mut [u8] = &mut self.word[..];
        if len+1 >= wstr.len() {
            return Err(ForthError::StringTooLong);
        }

        wstr[0] = len as u8;
        wstr[1..(len+1)].copy_from_slice(&tmp);

        // self.push(ST::input_space(off as u8,len as u8).to_word())?;
        self.push(ST::word_space(0, (len+1) as u8).to_word())?;
        Ok(())
    }

    fn builtin_parse(&mut self) -> Result<(), ForthError> {
        let delim = self.pop_delim()?;

        let st = self.next_word(delim, u8::MAX as usize)?;
        let len = st.len();

        self.push(st.to_word())?;
        self.push_int(len as i32)?;
        Ok(())
    }

    fn add_string_to_quote(&mut self) -> Result<(ST,usize),ForthError> {
        let off0 = self.input_off;
        let bytes = self.input.as_bytes();

        let (w0,w1,w2) = ToyForth::scan_word(&bytes[off0..], '"' as u8);

        let word_off = off0 + w0;
        let word_end = off0 + w1;
        self.input_off = off0 + w2;

        let len = word_end - word_off;
        if len > 255 {
            return Err(ForthError::StringTooLong);
        }

        let st = if word_off < word_end {
            // allocate string
            let off = self.strings.len();

            self.strings.extend_from_slice(&bytes[word_off..word_end]);
            self.strings.push(0);
            ST::allocated_space(off as u32,len as u8)
        } else {
            // empty string
            ST::allocated_space(0,0)
        };

        Ok((st,len))
    }

    pub fn builtin_s_quote(&mut self) -> Result<(),ForthError> {
        self.check_compiling()?;

        let (st,len) = self.add_string_to_quote()?;

        self.add_instr(Instr::Push(st.to_word()));
        self.add_instr(Instr::Push(Word::int(len as i32)));
        Ok(())
    }

    pub fn builtin_type(&mut self) -> Result<(),ForthError> {
        let len = self.pop_int()?;
        let st = self.pop_str()?;

        let s = self.maybe_string_at(st)?;

        if let Some(out) = &self.out_stream {
            let mut w = out.borrow_mut();
            let b = s.as_bytes();
            w.write(&b[.. std::cmp::min(b.len(), len as usize)])?;
        }

        Ok(())
    }

    pub fn builtin_err_type(&mut self) -> Result<(),ForthError> {
        let _len = self.pop_int()?;
        let st = self.pop_str()?;

        let s = self.maybe_string_at(st)?;

        eprintln!("{}", s);
        Ok(())
    }

    pub fn builtin_dot_quote(&mut self) -> Result<(),ForthError> {
        self.check_compiling()?;

        // something that bypasses the dictionary and uses a Func instr directly?
        let type_xt = self.lookup_word("TYPE")?;

        self.builtin_s_quote()?;
        self.add_instr(Instr::DoCol(type_xt));
        Ok(())
    }

    pub fn builtin_dot_oparen(&mut self) -> Result<(),ForthError> {
        self.check_compiling()?;

        self.push_int(')' as i32)?;
        self.builtin_parse()?;
        self.builtin_type()?;
        Ok(())
    }

    pub fn builtin_oparen(&mut self) -> Result<(),ForthError> {
        self.check_compiling()?;

        self.push_int(')' as i32)?;
        self.builtin_parse()?;
        self.drop()?;
        self.drop()?;

        Ok(())
    }

    pub fn builtin_backslash(&mut self) -> Result<(),ForthError> {
        self.check_compiling()?;

        self.input_off = self.input.len();

        Ok(())
    }

    pub fn builtin_err_quote(&mut self) -> Result<(),ForthError> {
        self.check_compiling()?;

        // something that bypasses the dictionary and uses a Func instr directly?
        let type_xt = self.lookup_word("/ETYPE")?;

        self.builtin_s_quote()?;
        self.add_instr(Instr::DoCol(type_xt));
        Ok(())
    }

    pub fn builtin_here(&mut self) -> Result<(),ForthError> {
        let here = self.vars.len();
        // TODO: check for overflow!
        self.push(Addr(here as u32).to_word())?;
        Ok(())
    }

    pub fn builtin_unused(&mut self) -> Result<(),ForthError> {
        let here = self.vars.len();
        let unused = Word::INT_MAX - (here as i32);

        // TODO: check for overflow!
        self.push_int(unused)?;
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
                Instr::ControlIndexDrop(count) => {
                    if count > 0 {
                        let clen = self.cstack.len();
                        let ccnt = count as usize;
                        if clen < ccnt {
                            return Err(ForthError::ControlStackUnderflow);
                        }

                        self.cstack.truncate(clen-ccnt);
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
                Instr::ReturnPush => {
                    self.data_to_ret()?;
                    pc += 1;
                },
                Instr::ReturnPop => {
                    self.ret_to_data()?;
                    pc += 1;
                },
                Instr::ReturnCopy => {
                    self.ret_copy_to_data()?;
                    pc += 1;
                },
                Instr::Execute => {
                    let xt = self.pop_xt()?;
                    self.rstack.push(Word::xt(pc+1));
                    pc = xt.0;
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
                Instr::Exit|Instr::Unnest => {
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
        assert_eq!(forth.input_off, 5);
        assert_eq!(forth.counted_string_at(forth.peek_str().unwrap()), "x");
        assert_eq!(forth.pop().unwrap(), Word::from_str(ST::word_space(0,2)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 10);
        assert_eq!(forth.counted_string_at(forth.peek_str().unwrap()), "test");
        assert_eq!(forth.pop().unwrap(), Word::from_str(ST::word_space(0,5)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 14);
        assert_eq!(forth.counted_string_at(forth.peek_str().unwrap()), "foo");
        assert_eq!(forth.pop().unwrap(), Word::from_str(ST::word_space(0,4)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 20);
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
        assert_eq!(forth.input_off, 9);
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
        assert_eq!(forth.input_off, 5);
        assert_eq!(forth.pop_int().unwrap(), 1);
        assert_eq!(forth.pop().unwrap(), Word::from_str(ST::input_space(2,1)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_parse().unwrap();
        assert_eq!(forth.input_off, 10);
        assert_eq!(forth.pop_int().unwrap(), 4);
        assert_eq!(forth.pop().unwrap(), Word::from_str(ST::input_space(5,4)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_parse().unwrap();
        assert_eq!(forth.input_off, 14);
        assert_eq!(forth.pop_int().unwrap(), 3);
        assert_eq!(forth.pop().unwrap(), Word::from_str(ST::input_space(10,3)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_parse().unwrap();
        assert_eq!(forth.input_off, 20);
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
        assert_eq!(forth.input_off, 5);
        assert_eq!(forth.pop_int().unwrap(), 'x' as i32);

        forth.builtin_char().unwrap();
        assert_eq!(forth.input_off, 10);
        assert_eq!(forth.pop_int().unwrap(), 't' as i32);

        forth.builtin_char().unwrap();
        assert_eq!(forth.input_off, 14);
        assert_eq!(forth.pop_int().unwrap(), 'f' as i32);

        forth.builtin_char().unwrap();
        assert_eq!(forth.input_off, 20);
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
        assert!(matches!(forth.data_to_ret().unwrap_err(), ForthError::StackUnderflow));
        assert!(matches!(forth.ret_to_data().unwrap_err(), ForthError::StackUnderflow));

        forth.push_int(1).unwrap();
        forth.push_int(2).unwrap();

        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.rstack_depth(), 0);

        forth.data_to_ret().unwrap();

        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.rstack_depth(), 1);

        assert_eq!(forth.dstack.last().map(|x| *x).unwrap(), Word::int(1));
        assert_eq!(forth.rstack.last().map(|x| *x).unwrap(), Word::int(2));

        forth.push_int(3).unwrap();
        forth.ret_to_data().unwrap();

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
        assert_eq!(forth.pop().unwrap(), Word::true_value());

        forth.interpret("5 3 <").unwrap();
        assert_eq!(forth.pop().unwrap(), Word::false_value());

        forth.interpret("5 3 =").unwrap();
        assert_eq!(forth.pop().unwrap(), Word::false_value());

        forth.interpret("5 3 <>").unwrap();
        assert_eq!(forth.pop().unwrap(), Word::true_value());

        // 3,5
        forth.interpret("3 5 >").unwrap();
        assert_eq!(forth.pop().unwrap(), Word::false_value());

        forth.interpret("3 5 <").unwrap();
        assert_eq!(forth.pop().unwrap(), Word::true_value());

        forth.interpret("3 5 =").unwrap();
        assert_eq!(forth.pop().unwrap(), Word::false_value());

        forth.interpret("3 5 <>").unwrap();
        assert_eq!(forth.pop().unwrap(), Word::true_value());

        // 3,3
        forth.interpret("3 3 =").unwrap();
        assert_eq!(forth.pop().unwrap(), Word::true_value());

        forth.interpret("3 3 >").unwrap();
        assert_eq!(forth.pop().unwrap(), Word::false_value());

        forth.interpret("3 3 <").unwrap();
        assert_eq!(forth.pop().unwrap(), Word::false_value());

        forth.interpret("3 3 <>").unwrap();
        assert_eq!(forth.pop().unwrap(), Word::false_value());
    }

    #[test]
    fn if_then() {
        let mut forth = ToyForth::new();

        forth.interpret(": foo dup . 5 > if 123 then ;").unwrap();
        forth.print_word_code("foo");

        forth.interpret("7 foo").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 123);

        forth.interpret("1 foo").unwrap();
        assert_eq!(forth.stack_depth(), 0);
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

        let outb = &outv.borrow();
        let s = std::str::from_utf8(outb).unwrap();
        eprintln!("output is\n{}", s);
        assert_eq!(s, "\
I 1   J 1 
I 1   J 2 
I 1   J 3 
I 2   J 1 
I 2   J 2 
I 2   J 3 
I 3   J 1 
I 3   J 2 
I 3   J 3 
");
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

    #[test]
    fn s_quote_strings() {
        let mut forth = ToyForth::new();

        {
            forth.interpret(": test S\" foo bar \" ; test").unwrap();
            forth.print_word_code("test");
            assert_eq!(forth.stack_depth(), 2);

            let count = forth.pop_int().unwrap();
            let st = forth.pop_str().unwrap();
            assert_eq!(count, 8);
            assert_eq!(forth.string_at(st), "foo bar ");
        }
    }

    #[test]
    fn dot_quote_strings() {
        let mut forth = ToyForth::new();
        let outv = Rc::new(RefCell::new(Vec::<u8>::new()));

        {
            forth.capture_interpret(": test .\" foo bar \" ; test", outv.clone()).unwrap();
            forth.print_word_code("test");
            assert_eq!(forth.stack_depth(), 0);

            let outb = &outv.borrow();
            let s = std::str::from_utf8(outb).unwrap();
            eprintln!("output is\n{}", s);
            assert_eq!(s, "foo bar ");
        }
    }

    #[test]
    fn can_use_brackets() {
        let mut forth = ToyForth::new();

        forth.interpret(": test [ 3 5 + ] literal ;").unwrap();
        forth.print_word_code("test");
        assert_eq!(forth.stack_depth(), 0);

        forth.interpret("test");
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 8);
    }

    #[test]
    fn bracket_errors_1() {
        let mut forth = ToyForth::new();
        assert!(matches!(forth.interpret("[").unwrap_err(), ForthError::WordInvalidWhileInterpreting));
    }

    #[test]
    fn bracket_errors_2() {
        let mut forth = ToyForth::new();
        assert!(matches!(forth.interpret(": test ]").unwrap_err(), ForthError::WordInvalidWhileCompiling));
    }

    #[test]
    fn bracket_errors_3() {
        let mut forth = ToyForth::new();
        assert!(matches!(forth.interpret(": test2 [ 5 3 + : test3 2 ] literal ;").unwrap_err(),
            ForthError::DefiningWordInvalid));
    }

    #[test]
    fn can_interpret_tick_and_bracket_tick() {
        let mut forth = ToyForth::new();

        forth.interpret(": test 3 + ;").unwrap();
        let xt = forth.lookup_word("test").unwrap();

        forth.interpret("' test").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_xt().unwrap(), xt);

        forth.interpret("5 ' test EXECUTE").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 8);

        forth.interpret(": test2 5 ['] test EXECUTE ; test2 test").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 11);

        forth.interpret("\
: test3 5 ' EXECUTE ;
: test4 5 * 1 + ;
test3 test
test3 test4").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), 26);
        assert_eq!(forth.pop_int().unwrap(), 8);
    }

    #[test]
    fn bitwise_ops() {
        let mut forth = ToyForth::new();

        forth.push_int(-1).unwrap();
        forth.unary_op(UnaryOp::Invert).unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 0);

        forth.push_int(0x7ff).unwrap();
        forth.unary_op(UnaryOp::Invert).unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), -2048);

        forth.push_int(0).unwrap();
        forth.unary_op(UnaryOp::Invert).unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), -1);

        forth.push_int(-2048).unwrap();
        forth.unary_op(UnaryOp::Invert).unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 0x7ff);


        forth.push_int(-1).unwrap();
        forth.push_int(0x7ff).unwrap();
        forth.binary_op(BinOp::And).unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 0x7ff);

        forth.push_int(-1).unwrap();
        forth.push_int(0x7ff).unwrap();
        forth.binary_op(BinOp::Or).unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), -1);

        forth.push_int(-1).unwrap();
        forth.push_int(0x7ff).unwrap();
        forth.binary_op(BinOp::Xor).unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), -2048);

        forth.push_int(0xf3f).unwrap();
        forth.push_int(0x7ff).unwrap();
        forth.binary_op(BinOp::And).unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 0x73f);

        forth.push_int(0xf3f).unwrap();
        forth.push_int(0x7ff).unwrap();
        forth.binary_op(BinOp::Or).unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 0xfff);

        forth.push_int(0xf3f).unwrap();
        forth.push_int(0x7ff).unwrap();
        forth.binary_op(BinOp::Xor).unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 0x8c0);
    }

    #[test]
    fn error_mixing_if_and_loop() {
        let mut forth = ToyForth::new();

        let err = forth.interpret("\
: test do 5 then ;").unwrap_err();

        assert!(matches!(err, ForthError::InvalidControlEntry(ControlEntry::DoAddr(_))));
    }

    #[test]
    fn can_exit_function() {
        let mut forth = ToyForth::new();
        let outv = Rc::new(RefCell::new(Vec::<u8>::new()));

        forth.interpret("\
: FOO
    DUP . CR
    1- DUP . CR
    1- DUP 0> IF
            DUP . CR
        ELSE
            . .\" is less than or equal to zero\" CR EXIT 
        THEN
    1- DUP . CR
    1- . CR
;").unwrap();

        forth.capture_interpret("7 FOO", outv.clone()).unwrap();
        {
            let mut outb = outv.borrow_mut();
            let s = std::str::from_utf8(&outb).unwrap();
            eprintln!("output is\n{}", s);
            assert_eq!(s, "\
7 
6 
5 
4 
3 
");
            outb.clear();
    }

        forth.capture_interpret("2 FOO", outv.clone()).unwrap();
        {
            let mut outb = outv.borrow_mut();
            let s = std::str::from_utf8(&outb).unwrap();
            eprintln!("output is\n{}", s);
            assert_eq!(s, "\
2 
1 
0 is less than or equal to zero
");

            outb.clear();
        }
    }

    #[test]
    fn begin_again_loop() {
        let mut forth = ToyForth::new();

        forth.interpret("\
: BAR 3
    BEGIN
        5 +
        DUP . CR
        DUP /STACKS 28 > IF /STACKS EXIT THEN 
    AGAIN
;

BAR
").unwrap();

        forth.print_word_code("bar");

        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.cstack_depth(), 0);
        assert_eq!(forth.rstack_depth(), 0);

        assert_eq!(forth.pop_int().unwrap(), 33);
    }

    #[test]
    fn begin_until_loop() {
        let mut forth = ToyForth::new();

        forth.interpret("\
: BAR 3
    BEGIN
        5 +
        DUP . CR
    DUP 28 > UNTIL
;

BAR
").unwrap();

        forth.print_word_code("bar");

        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.cstack_depth(), 0);
        assert_eq!(forth.rstack_depth(), 0);

        assert_eq!(forth.pop_int().unwrap(), 33);
    }

    #[test]
    fn begin_while_loop() {
        let mut forth = ToyForth::new();

        forth.interpret("\
: BAR
    3
    BEGIN
        2 +
        DUP 28 > INVERT WHILE
        3 +
        DUP . CR
    REPEAT
    .\" Final: \" DUP . CR
;

BAR
").unwrap();

        forth.print_word_code("bar");

        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.cstack_depth(), 0);
        assert_eq!(forth.rstack_depth(), 0);

        assert_eq!(forth.pop_int().unwrap(), 30);
    }

    #[test]
    fn do_loop_with_leave() {
        let mut forth = ToyForth::new();

        forth.interpret("\
: BAR
    1
    10 0 DO
        OVER *
        DUP 100 > IF LEAVE THEN
        .\" Iteration \" I .  .\" Value \" DUP . CR
        /STACKS
    LOOP
    SWAP DROP
    /STACKS
    .\" Final: \" DUP . CR
;
").unwrap();

        forth.print_word_code("BAR");

        forth.interpret("5 BAR");
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.cstack_depth(), 0);
        assert_eq!(forth.rstack_depth(), 0);

        assert_eq!(forth.pop_int().unwrap(), 125);

        forth.interpret("2 BAR");
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.cstack_depth(), 0);
        assert_eq!(forth.rstack_depth(), 0);

        assert_eq!(forth.pop_int().unwrap(), 128);
    }

    #[test]
    fn plus_bang() {
        let mut forth = ToyForth::new();

        forth.interpret("\
VARIABLE FOO
3 FOO !
5 FOO +!
FOO @
").unwrap();

        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.cstack_depth(), 0);
        assert_eq!(forth.rstack_depth(), 0);

        assert_eq!(forth.pop_int().unwrap(), 8);
    }

    #[test]
    fn recurse() {
        let mut forth = ToyForth::new();

        forth.interpret("\
: FACTORIAL 
    DUP 1 > IF
        DUP 1- RECURSE *
    THEN
;
").unwrap();

        forth.interpret("5 FACTORIAL");

        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.cstack_depth(), 0);
        assert_eq!(forth.rstack_depth(), 0);

        assert_eq!(forth.pop_int().unwrap(), 120);
    }

    #[test]
    fn comments() {
        let mut forth = ToyForth::new();
        let outv = Rc::new(RefCell::new(Vec::<u8>::new()));

        forth.capture_interpret("\
: FACTORIAL  .( Computes factorial )
    ( n1 -- n2 )
    DUP 1 > IF              \\ if n > 1, recurse, otherwise return 1
        DUP 1- RECURSE *    \\ return n * (n-1)!
    THEN
;
", outv.clone()).unwrap();

        forth.capture_interpret("5 FACTORIAL", outv.clone());

        forth.print_word_code("FACTORIAL");

        {
            let outb = outv.borrow();
            let s = std::str::from_utf8(&outb).unwrap();
            assert_eq!(s, "Computes factorial ");
        }

        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.cstack_depth(), 0);
        assert_eq!(forth.rstack_depth(), 0);

        assert_eq!(forth.pop_int().unwrap(), 120);
    }

    #[test]
    fn base_values() {
        let mut forth = ToyForth::new();

        forth.interpret("2 BASE ! 101 110 10000").unwrap();
        assert_eq!(forth.stack_depth(), 3);
        assert_eq!(forth.pop_int().unwrap(), 16);
        assert_eq!(forth.pop_int().unwrap(), 6);
        assert_eq!(forth.pop_int().unwrap(), 5);

        forth.interpret("DECIMAL 123 321").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), 321);
        assert_eq!(forth.pop_int().unwrap(), 123);

        forth.interpret("HEX F A3 0B 7F 123").unwrap();
        assert_eq!(forth.stack_depth(), 5);
        assert_eq!(forth.pop_int().unwrap(), 256 + 32 + 3);
        assert_eq!(forth.pop_int().unwrap(), 127);
        assert_eq!(forth.pop_int().unwrap(), 11);
        assert_eq!(forth.pop_int().unwrap(), 163);
        assert_eq!(forth.pop_int().unwrap(), 15);
    }

    #[test]
    fn min_max_are_correct() {
        let mut forth = ToyForth::new();
        forth.interpret("\
 3  2 MIN   3  2 MAX
-9  5 MIN  -9  5 MAX
 9 -5 MIN   9 -5 MAX
 0  0 MIN   0  0 MAX
 1  0 MIN   1  0 MAX
").unwrap();

        assert_eq!(forth.stack_depth(), 10);

        assert_eq!(forth.pop_int().unwrap(),  1);  //  1  0 MAX
        assert_eq!(forth.pop_int().unwrap(),  0);  //  1  0 MIN

        assert_eq!(forth.pop_int().unwrap(),  0);  //  0  0 MAX
        assert_eq!(forth.pop_int().unwrap(),  0);  //  0  0 MIN

        assert_eq!(forth.pop_int().unwrap(),  9);  //  9 -5 MAX
        assert_eq!(forth.pop_int().unwrap(), -5);  //  9 -5 MIN

        assert_eq!(forth.pop_int().unwrap(),  5);  // -9  5 MAX
        assert_eq!(forth.pop_int().unwrap(), -9);  // -9  5 MIN

        assert_eq!(forth.pop_int().unwrap(),  3);  //  3  2 MAX
        assert_eq!(forth.pop_int().unwrap(),  2);  //  3  2 MIN
    }

    #[test]
    fn unsigned_comparisons() {
        let mut forth = ToyForth::new();
        forth.interpret("\
  5  10 U<     5  10 U>
 10   5 U<    10   5 U>
 -5  10 U<    -5  10 U>
 -1  -5 U<    -1  -5 U>
  0   0 U<     0   0 U>
 -1  -1 U<    -1  -1 U>
").unwrap();

        assert_eq!(forth.stack_depth(), 12);

        assert_eq!(forth.pop_int().unwrap(), 0); //   -1    -1 U>
        assert_eq!(forth.pop_int().unwrap(), 0); //   -1    -1 U<

        assert_eq!(forth.pop_int().unwrap(), 0); //    0     0 U>
        assert_eq!(forth.pop_int().unwrap(), 0); //    0     0 U<

        assert_eq!(forth.pop_int().unwrap(),-1); //   -1    -5 U>
        assert_eq!(forth.pop_int().unwrap(), 0); //   -1    -5 U<

        assert_eq!(forth.pop_int().unwrap(),-1); //   -5    10 U>
        assert_eq!(forth.pop_int().unwrap(), 0); //   -5    10 U<

        assert_eq!(forth.pop_int().unwrap(),-1); //   10     5 U>
        assert_eq!(forth.pop_int().unwrap(), 0); //   10     5 U<

        assert_eq!(forth.pop_int().unwrap(), 0); //    5    10 U>
        assert_eq!(forth.pop_int().unwrap(),-1); //    5    10 U<
    }

    #[test]
    fn return_stack_words() {
        let mut forth = ToyForth::new();
        forth.interpret("\
: MYOVER ( n1 n2 -- n1 n2 n1 ) >R DUP R> SWAP ;
1 2 3 MYOVER \\ ( 1 2 3 -- 1 2 3 2 )
").unwrap();

        assert_eq!(forth.stack_depth(), 4);
        assert_eq!(forth.pop_int().unwrap(), 2);
        assert_eq!(forth.pop_int().unwrap(), 3);
        assert_eq!(forth.pop_int().unwrap(), 2);
        assert_eq!(forth.pop_int().unwrap(), 1);

        forth.interpret(": TESTR@ ( a b c -- b a-c c ) >R SWAP R@ - R> ;").unwrap();
        forth.print_word_code("TESTR@");
        forth.interpret("1 2 3 TESTR@").unwrap();

        assert_eq!(forth.stack_depth(), 3);
        assert_eq!(forth.pop_int().unwrap(),  3);
        assert_eq!(forth.pop_int().unwrap(), -2);
        assert_eq!(forth.pop_int().unwrap(),  2);
    }
}

