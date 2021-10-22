use std::rc::Rc;
use std::cell::RefCell;

// Basic rtoyforth value: the 32-bit cell.
//
// Cell values can hold integer values, execution tokens, string tokens, or variable addresses.
//
//   - Single cell integers are 31-bit signed values.
//   - Execution tokens point to a location in the code dictionary
//   - String tokens hold an offset/length, either in allocated string
//     space or in one of several scratch spaces
//   - Variable addresses are an offset into the variable address space
//
// Internal structure:
//
//
//                              1         2          3
// bit                01234567890123456789012345678901
// integer            IIIIIIIIIIIIIIIIIIIIIIIIIIIIIII0
// string token       SSSSSSSSSSSSSSSSSSSSSSSSSSSSSS01
// executable token   XXXXXXXXXXXXXXXXXXXXXXXXXXXXX011
// variable address   AAAAAAAAAAAAAAAAAAAAAAAAAAAAA111
//
// Notes:
// - The three MSBs indicate the type.
// - If bit 31 is 0, the remaining bits are interpreted as a signed integer.
// - If bit 31 is 1:
//   - If bit 30 is 0, then the remaining bits are interpreted as a string token.
//   - If bit 30 is 1:
//     - If bit 29 is 0, the remaining bits are intreprted as an executable token (XT)
//     - If bit 29 is 1, the remaining bits are intreprted as a variable address
//
#[derive(Debug,PartialEq,Eq,Clone,Copy)]
struct Cell(u32);

// eXecution Token, points to an execution point in the code dictionary
#[derive(Debug,PartialEq,Eq,Clone,Copy)]
struct XT(u32);

impl XT {
    const MAX : u32 = 0x1fff_ffff;
    const MIN : u32 = 0;
    const MASK : u32 = 0x1fff_ffff;
    const BITS : u32 = Cell::HIGH_BIT | Cell::SIGN_BIT;

    fn to_cell(self) -> Cell {
        Cell::xt(self.0)
    }
}

#[derive(Debug,PartialEq,Eq,Clone,Copy)]
struct VarAddr(u32);

impl VarAddr {
    const BUILTIN : u32 = 0x1000_0000;

    const MAX : u32 = 0x1fff_ffff;
    const MIN : u32 = 0;
    const MASK : u32 = 0x1fff_ffff;
    const ADDR_BIT : u32 = 0x2000_0000;
    const BITS : u32 = Cell::HIGH_BIT | Cell::SIGN_BIT | VarAddr::ADDR_BIT;

    fn to_cell(self) -> Cell {
        // XXX: check mask
        Cell(VarAddr::BITS | self.0)
    }
}

// Length/offset pair for scratch space string tokens
#[derive(Debug,PartialEq,Eq,Clone,Copy)]
struct ScratchLoc{len:u8, off:u8}

// String token.  Offset and length into one of several spaces.
//
// Allocated   offset/length into the allocated strings space.
//             offset is 24-bit, length is 8-bit
//
// The remaining spaces are the usual 256-byte scratch spaces availabe in
// various Forth systems:
//
// PadSpace    offset/length in pad space (accessed with PAD)
// WordSpace   offset/length in word space
// InputSpace  offset/length in input space
// PicSpace    offset/length in picture space
//
#[derive(Debug,PartialEq,Eq,Clone,Copy)]
enum ST {
    // TODO: Check size.  This needs to fit in 32 bits.

    Allocated(u32),
    PadSpace(ScratchLoc),
    WordSpace(ScratchLoc),
    InputSpace(ScratchLoc),
    PicSpace(ScratchLoc),
}

impl ST {
    const MAX : u32 = 0x3fff_ffff;
    const MIN : u32 = 0;
    const MASK : u32 = 0x3fff_ffff;
    const BITS : u32 = Cell::HIGH_BIT;

    // Indicates string scratch space
    const SCRATCH_BIT : u32 = 0x2000_0000;
    const ALLOC_MASK  : u32 = 0x1fff_ffff;

    const LOC_MASK : u32 = 0x0007_0000;
    const LEN_MASK : u32 = 0x0000_ff00;
    const OFF_MASK : u32 = 0x0000_00ff;

    const ST_BITS : u32 = Cell::HIGH_BIT;

    const MAX_LENGTH : usize = 255;
    const MAX_OFFSET : usize = ST::ALLOC_MASK as usize;

    fn from_u32(val: u32) -> Result<ST,ForthError> {
        // check for valid string encoding

        // All string tokens must have bit 31 set and bit 30 cleared.
        if (val & Cell::HIGH_BIT) == 0 || (val & Cell::SIGN_BIT) == 1 {
            return Err(ForthError::InvalidStringValue(val));
        }

        // Bit 29 is the SCRATCH_BIT.  If it is cleared, then this is
        // an allocated string.
        if (val & ST::SCRATCH_BIT) == 0 {
            return Ok(ST::Allocated(val & ST::MASK));
        }

        // Bit 29 is set, so it's a scratch string:
        //
        //                 1         2          3
        // bits  01234567890123456789012345678 901
        //       OOOOOOOOLLLLLLLLWWWWWWWWWWWWW 101
        //
        // O - offset into scratch space (8 bits)
        // L - length in scratch space (8 bits)
        // W - which scratch space
        //
        // Only four scratch spaces are supported right now: PAD, WORD, INPUT, and PIC.
        //
        match (val & ST::LOC_MASK) >> 16 {
            0 => Ok(ST::pad_space((val & ST::OFF_MASK) as u8, ((val & ST::LEN_MASK) >> 8) as u8)),
            1 => Ok(ST::word_space((val & ST::OFF_MASK) as u8, ((val & ST::LEN_MASK) >> 8) as u8)),
            2 => Ok(ST::input_space((val & ST::OFF_MASK) as u8, ((val & ST::LEN_MASK) >> 8) as u8)),
            3 => Ok(ST::pic_space((val & ST::OFF_MASK) as u8, ((val & ST::LEN_MASK) >> 8) as u8)),
            _ => Err(ForthError::InvalidStringValue(val)),
        }
    }

    // Offset of the string token in its address space
    fn addr(self) -> u32 {
        match self {
            ST::Allocated(val) => {
                val >> 8
            },
            ST::PadSpace(loc) | ST::WordSpace(loc) | ST::InputSpace(loc) | ST::PicSpace(loc) => {
                loc.off as u32
            },
        }
    }

    // Length of string represented by the string token
    fn len(self) -> u32 {
        match self {
            ST::Allocated(val) => {
                val & 0xff
            },
            ST::PadSpace(loc) | ST::WordSpace(loc) | ST::InputSpace(loc) | ST::PicSpace(loc) => {
                loc.len as u32
            },
        }
    }

    // Advances the string token forward by `by` bytes
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
            ST::PicSpace(_) => {
                ST::pic_space(new_addr as u8, new_len)
            },
        }
    }

    fn substr(self, off: u8, len: u8) -> ST {
        let st = self.offset(off);

        let addr = st.addr();
        let new_len  = std::cmp::min(st.len(), len as u32) as u8;

        match self {
            ST::Allocated(_) => {
                ST::allocated_space(addr, new_len)
            },
            ST::PadSpace(_) => {
                ST::pad_space(addr as u8, new_len)
            },
            ST::WordSpace(_) => {
                ST::word_space(addr as u8, new_len)
            },
            ST::InputSpace(_) => {
                ST::input_space(addr as u8, new_len)
            },
            ST::PicSpace(_) => {
                ST::pic_space(addr as u8, new_len)
            },
        }
    }

    fn null() -> ST {
        // offset == 0, length == 0
        ST::Allocated(0)
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

    fn pic_space(off: u8, len: u8) -> ST {
        ST::PicSpace(ScratchLoc{off:off, len:len})
    }

    fn to_cell(self) -> Cell {
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
            ST::PicSpace(loc) => {
                ST::SCRATCH_BIT | ((3 as u32) << 16) | ((loc.len as u32) << 8) | (loc.off as u32)
            },
        };

        Cell(v | ST::ST_BITS)
    }

    // Description of the string token, for debugging
    fn descr(self) -> std::string::String {
        let w = self.to_cell();
        match self {
            ST::Allocated(_) => {
                format!("[st {}] allocated[addr={}, len={}]", w.0, self.addr(), self.len())
            },
            ST::PadSpace(loc) => {
                format!("[st {}] pad[off={}, len={}]", w.0, loc.off, loc.len)
            },
            ST::WordSpace(loc) => {
                format!("[st {}] word[off={}, len={}]", w.0, loc.off, loc.len)
            },
            ST::InputSpace(loc) => {
                format!("[st {}] input[off={}, len={}]", w.0, loc.off, loc.len)
            },
            ST::PicSpace(loc) => {
                format!("[st {}] pic[off={}, len={}]", w.0, loc.off, loc.len)
            },
        }
    }
}

// General address type: either a variable address or a character address (string token).
// Attempt at a reasonable abstraction over ANS Forth a-addr / c-addr definitions.
//
#[derive(Debug,PartialEq,Eq,Clone,Copy)]
enum Addr {
    Var(VarAddr),
    Char(ST),
}

impl Addr {
    fn c_addr(&self) -> Option<ST> {
        if let Addr::Char(ch) = self { Some(*ch) } else { None }
    }

    fn a_addr(&self) -> Option<VarAddr> {
        if let Addr::Var(v) = self { Some(*v) } else { None }
    }

    fn to_cell(&self) -> Cell {
        match self {
            Addr::Char(caddr) => { caddr.to_cell() },
            Addr::Var(vaddr)  => { vaddr.to_cell() },
        }
    }
}

// Enum for the type of data in the cell.  Includes value to make it easy
// to decode and use in a match or if-let
#[derive(Debug,PartialEq,Eq,Clone,Copy)]
enum CellKind {
    Int(i32),
    XT(XT),
    Str(ST),
    VarAddr(VarAddr),
}

impl Cell {
    const HIGH_BIT : u32 = 0x8000_0000;
    const SIGN_BIT : u32 = 0x4000_0000;
    const INT_MASK : u32 = 0x7fff_ffff;

    const INT_BITS : u32 = 31;

    const INT_MIN  : i32 = -1073741824;
    const INT_MAX  : i32 =  1073741823;

    const UINT_MAX : u32 =  Cell::INT_MASK;

    const XT_MASK  : u32 = 0x1fff_ffff;
    const STR_MASK : u32 = 0x3fff_ffff;
    const XT_BITS  : u32 = Cell::HIGH_BIT | Cell::SIGN_BIT;
    const STR_BITS : u32 = Cell::HIGH_BIT;

    fn true_value() -> Cell {
        Cell(Cell::INT_MASK)
    }

    fn false_value() -> Cell {
        Cell(0)
    }

    fn bool(b: bool) -> Cell {
        if b { Cell::true_value() } else { Cell::false_value() }
    }

    fn int(x: i32) -> Cell {
        // TODO: range check
        Cell((x as u32) & Cell::INT_MASK)
    }

    fn xt(x: u32) -> Cell {
        // TODO: range check
        Cell((x & Cell::XT_MASK) | Cell::XT_BITS)
    }

    fn str(x: u32) -> Cell {
        // TODO: range check
        Cell((x & Cell::STR_MASK) | Cell::STR_BITS)
    }

    fn addr(x: u32) -> Cell {
        VarAddr(x).to_cell()
    }

    pub fn from_xt(xt: XT) -> Cell {
        Cell::xt(xt.0)
    }

    pub fn from_str(st: ST) -> Cell {
        st.to_cell()
    }

    pub fn from_addr(addr: VarAddr) -> Cell {
        addr.to_cell()
    }

    pub fn kind(self) -> CellKind {
        match self.0 {
            x if (x & Cell::HIGH_BIT) == 0 => { CellKind::Int((x | ((x & Cell::SIGN_BIT) << 1)) as i32) },
            x if (x & Cell::SIGN_BIT) == 0 => {
                // FIXME: unwrap!
                CellKind::Str(ST::from_u32(x).unwrap())
            },
            x if (x & VarAddr::ADDR_BIT) != 0 => {
                CellKind::VarAddr(VarAddr(x & VarAddr::MASK))
            }
            x => { CellKind::XT(XT(x & Cell::XT_MASK)) },
        }
    }

    pub fn to_int(self) -> Option<i32> {
        if let CellKind::Int(x) = self.kind() { Some(x) } else { None }
    }

    pub fn to_xt(self) -> Option<XT> {
        if let CellKind::XT(x) = self.kind() { Some(x) } else { None }
    }

    pub fn to_str(self) -> Option<ST> {
        if let CellKind::Str(x) = self.kind() { Some(x) } else { None }
    }

    pub fn to_addr(self) -> Option<VarAddr> {
        if let CellKind::VarAddr(x) = self.kind() { Some(x) } else { None }
    }

    pub fn to_char(self) -> Result<u8, ForthError> {
        if let CellKind::Int(x) = self.kind() {
            if x < 0 && x > (u8::MAX as i32) {
                return Err(ForthError::InvalidChar(x));
            }

            return Ok(x as u8);
        }

        return Err(ForthError::ExpectedInteger(self));
    }
}

impl std::fmt::Display for Cell {
    fn fmt(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.kind() {
            CellKind::Int(x) => { formatter.write_fmt(format_args!("[int] {}", x)) },
            CellKind::XT(XT(x))  => { formatter.write_fmt(format_args!("[xt] {}", x)) },
            CellKind::VarAddr(VarAddr(x))  => { formatter.write_fmt(format_args!("[addr] {}", x)) },
            CellKind::Str(st) => {
                match st {
                    ST::Allocated(v) => {
                        formatter.write_fmt(format_args!("[str:alloc] @ {} len={},addr={}", v, st.len(), st.addr())) },
                    ST::PadSpace(loc)   => { formatter.write_fmt(format_args!("[str:pad] len={},off={}", loc.len, loc.off)) },
                    ST::WordSpace(loc)  => { formatter.write_fmt(format_args!("[str:word] len={},off={}", loc.len, loc.off)) },
                    ST::InputSpace(loc) => { formatter.write_fmt(format_args!("[str:input] len={},off={}", loc.len, loc.off)) },
                    ST::PicSpace(loc)   => { formatter.write_fmt(format_args!("[str:pic] len={},off={}", loc.len, loc.off)) },
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

// Result of call into Forth interpreter via exec()
//
// Bye      interpreter is finished and should exit
// Refill   interpreter is awaiting more input
//
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
enum ForthResult {
    Bye,
    Refill,
}

// Builtin VM instructions
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
enum Instr {
    Empty,
    Nop,
    Bye,
    Push(Cell),
    Drop,
    Pick,
    Roll,
    Rot,
    Dup,
    Swap,
    Over,
    BinaryOp(BinOp),
    UnaryOp(UnaryOp),
    Branch(i32),
    BranchOnZero(i32),  // branches if stack top is 0
    ControlIndexPush(u8),
    ControlIndexDrop(u8),
    ControlIteration{incr:bool},
    ControlIndexPeek(u32),
    Defer(XT),
    Jump(XT),
    Error(u32),
    ReturnPush,
    ReturnPop,
    ReturnCopy,
    Execute,
    Func(u32),
    DoCol(XT),
    Refill,
    Exit,               // redundant with Unnest... but Unnest currently marks the end of a function
    Unnest,
}

// Unary operations for integers
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
#[repr(u8)]
enum UnaryOp {
    Negate,
    Invert,
}

// Binary operations on integers
//
// Bitwise operations treat the value as an unsigned 31-bit integer
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
#[repr(u8)]
enum BinOp {
    Plus,
    Minus,
    Star,
    Slash,

    // single cell operands, double cell output
    MStar,
    UMStar,

    And,
    Or,
    Xor,

    Greater,
    Less,
    Equal,
    NotEqual,

    UnsignedGreater,
    UnsignedLess,

    LeftShift,
    RightShift,
}

// used to compile DO ... LOOP and related
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
struct DoInfo {
    head: XT,
    qdo: Option<XT>,
}

// Control stack entries while compiling
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
enum ControlEntry {
    IfAddr(XT),
    ElseAddr(XT),

    DoAddr(DoInfo),
    BeginAddr(XT),
    WhileAddr{ head: XT, cond: XT },
    LeaveAddr{ head: DoInfo, leave: XT },

    CaseEntry{ exit_xt: XT },
    OfEntry{ exit_xt: XT, next_xt: XT },

    Index(i32),
}

// Dictionary entry
//
// Indicates whether the forth 
#[derive(Debug,Clone,Copy)]
struct DictEntry {
    st: ST,
    start: XT,
    end: XT,
    flags: u32,
}

impl DictEntry {
    const PRIMITIVE : u32 = 1<<0; // 0x0000_0001
    const IMMEDIATE : u32 = 1<<1; // 0x0000_0002
    const DEFERRED  : u32 = 1<<2; // 0x0000_0008

    fn check_flag(&self, flag: u32) -> bool {
        (self.flags & flag) == flag
    }

    pub fn is_primitive(&self) -> bool {
        self.check_flag(DictEntry::PRIMITIVE)
    }

    pub fn is_immediate(&self) -> bool {
        self.check_flag(DictEntry::IMMEDIATE)
    }

    pub fn is_deferred(&self) -> bool {
        self.check_flag(DictEntry::DEFERRED)
    }
}

struct ToyForth<'tf> {
    dstack: Vec<Cell>,
    rstack: Vec<XT>,
    aux_stack: Vec<Cell>,
    cstack: Vec<ControlEntry>,
    ufuncs: Vec<ForthFunc<'tf>>,
    funcnames: Vec<String>,

    dict: Vec<DictEntry>,
    vars: Vec<Cell>,
    strings: std::vec::Vec<u8>,
    code: Vec<Instr>,

    pc: u32,

    runtime_does_func: u32,
    invalid_deferred_xt: XT,
    compile_comma_xt: XT,

    pad:  [u8;256],
    word: [u8;256],
    pic:  [u8;256],

    input: String,
    input_off: usize,
    last_input_off: usize,
    last_word: ST,

    source: ST,
    source_id: i32,

    optimize: i32,

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
    DivisionByZero,

    InvalidNumberBase,
    NumberOutOfRange,

    InvalidEmptyString,
    StringTooLong,
    StringOffsetTooLarge,
    StringNotFound,
    InvalidHexEscape,
    StringNotTerminated,
    StringIsReadonly,

    FunctionSpaceOverflow,
    DictSpaceOverflow,
    VarSpaceOverflow,
    StringSpaceOverflow,

    WordInvalidWhileCompiling,
    WordInvalidWhileInterpreting,
    DefiningWordInvalid,
    UnfinishedColonDefinition,
    DictEmpty,

    DeferredFunctionNotSet,
    NotDeferredFunction,

    NoMatchingLoopHead,

    NotImplemented,
    Abort,

    WordNotFound(ST),

    InvalidArgument(Cell),
    InvalidCell(XT),
    InvalidControlEntry(ControlEntry),
    InvalidIndex(Cell),
    InvalidControlInstruction(XT),
    InvalidExecutionToken(Cell),
    InvalidString(ST),
    InvalidEscape(char),
    InvalidChar(i32),
    InvalidAddress(VarAddr),
    InvalidAddressAndOffset(Addr,i32),
    InvalidCountedString(ST),
    InvalidStringValue(u32),
    InvalidFunction(u32),
    InvalidPC(u32),
    ReadOnlyAddress(Addr),

    InvalidErrorCode(u32),

    ExpectedXT(Cell),
    ExpectedString(Cell),
    ExpectedInteger(Cell),
    ExpectedVarAddr(Cell),
    ExpectedAddr(Cell),

    IOError(std::io::Error),
}

impl ForthError {
    const STACK_UNDERFLOW                   : u32 = 101;
    const CONTROL_STACK_UNDERFLOW           : u32 = 102;
    const RETURN_STACK_UNDERFLOW            : u32 = 103;
    const INVALID_OPERATION                 : u32 = 104;
    const INVALID_ARGUMENT                  : u32 = 105;
    const DIVISION_BY_ZERO                  : u32 = 106;
    const INVALID_NUMBER_BASE               : u32 = 107;
    const NUMBER_OUT_OF_RANGE               : u32 = 108;
    const INVALID_EMPTY_STRING              : u32 = 109;

    const STRING_TOO_LONG                   : u32 = 110;
    const STRING_OFFSET_TOO_LARGE           : u32 = 111;
    const STRING_NOT_FOUND                  : u32 = 112;
    const INVALID_HEX_ESCAPE                : u32 = 113;
    const STRING_NOT_TERMINATED             : u32 = 114;
    const STRING_IS_READONLY                : u32 = 115;
    const FUNCTION_SPACE_OVERFLOW           : u32 = 116;
    const DICT_SPACE_OVERFLOW               : u32 = 117;
    const VAR_SPACE_OVERFLOW                : u32 = 118;
    const STRING_SPACE_OVERFLOW             : u32 = 119;

    const WORD_INVALID_WHILE_COMPILING      : u32 = 120;
    const WORD_INVALID_WHILE_INTERPRETING   : u32 = 121;
    const DEFINING_WORD_INVALID             : u32 = 122;
    const UNFINISHED_COLON_DEFINITION       : u32 = 123;
    const DICT_EMPTY                        : u32 = 124;
    const DEFERRED_FUNCTION_NOT_SET         : u32 = 125;
    const NOT_DEFERRED_FUNCTION             : u32 = 126;
    const NO_MATCHING_LOOPHEAD              : u32 = 127;
    const ABORT                             : u32 = 128;
    const NOT_IMPLEMENTED                   : u32 = 129;

    const WORD_NOT_FOUND                    : u32 = 130;
    const INVALID_CELL                      : u32 = 131;
    const INVALID_CONTROL_ENTRY             : u32 = 132;
    const INVALID_INDEX                     : u32 = 133;
    const INVALID_CONTROL_INSTRUCTION       : u32 = 134;
    const INVALID_EXECUTION_TOKEN           : u32 = 135;
    const INVALID_STRING                    : u32 = 136;
    const INVALID_ESCAPE                    : u32 = 137;
    const INVALID_CHAR                      : u32 = 138;
    const INVALID_ADDRESS                   : u32 = 139;
    const INVALID_ADDRESS_AND_OFFSET        : u32 = 140;

    const INVALID_COUNTED_STRING            : u32 = 141;
    const INVALID_STRING_VALUE              : u32 = 142;
    const INVALID_FUNCTION                  : u32 = 143;
    const INVALID_PC                        : u32 = 144;
    const READ_ONLY_ADDRESS                 : u32 = 145;
    const INVALID_ERROR_CODE                : u32 = 146;
    const EXPECTED_XT                       : u32 = 147;
    const EXPECTED_STRING                   : u32 = 148;
    const EXPECTED_INTEGER                  : u32 = 149;
    const EXPECTED_VARADDR                  : u32 = 150;

    const EXPECTED_ADDR                     : u32 = 151;
    const IO_ERROR                          : u32 = 152;

    fn from_code(code: u32, arg: Cell) -> Result<ForthError,ForthError> {
        let err = match code {
            ForthError::STACK_UNDERFLOW                 => ForthError::StackUnderflow,
            ForthError::CONTROL_STACK_UNDERFLOW         => ForthError::ControlStackUnderflow,
            ForthError::RETURN_STACK_UNDERFLOW          => ForthError::ReturnStackUnderflow,

            ForthError::INVALID_OPERATION               => ForthError::InvalidOperation,
            ForthError::DIVISION_BY_ZERO                => ForthError::DivisionByZero,

            ForthError::INVALID_NUMBER_BASE             => ForthError::InvalidNumberBase,
            ForthError::NUMBER_OUT_OF_RANGE             => ForthError::NumberOutOfRange,

            ForthError::INVALID_EMPTY_STRING            => ForthError::InvalidEmptyString,
            ForthError::STRING_TOO_LONG                 => ForthError::StringTooLong,
            ForthError::STRING_OFFSET_TOO_LARGE         => ForthError::StringOffsetTooLarge,
            ForthError::STRING_NOT_FOUND                => ForthError::StringNotFound,
            ForthError::INVALID_HEX_ESCAPE              => ForthError::InvalidHexEscape,
            ForthError::STRING_NOT_TERMINATED           => ForthError::StringNotTerminated,
            ForthError::STRING_IS_READONLY              => ForthError::StringIsReadonly,

            ForthError::FUNCTION_SPACE_OVERFLOW         => ForthError::FunctionSpaceOverflow,
            ForthError::DICT_SPACE_OVERFLOW             => ForthError::DictSpaceOverflow,
            ForthError::VAR_SPACE_OVERFLOW              => ForthError::VarSpaceOverflow,
            ForthError::STRING_SPACE_OVERFLOW           => ForthError::StringSpaceOverflow,

            ForthError::WORD_INVALID_WHILE_COMPILING    => ForthError::WordInvalidWhileCompiling,
            ForthError::WORD_INVALID_WHILE_INTERPRETING => ForthError::WordInvalidWhileInterpreting,
            ForthError::DEFINING_WORD_INVALID           => ForthError::DefiningWordInvalid,
            ForthError::UNFINISHED_COLON_DEFINITION     => ForthError::UnfinishedColonDefinition,
            ForthError::DICT_EMPTY                      => ForthError::DictEmpty,

            ForthError::DEFERRED_FUNCTION_NOT_SET       => ForthError::DeferredFunctionNotSet,
            ForthError::NOT_DEFERRED_FUNCTION           => ForthError::NotDeferredFunction,

            ForthError::NO_MATCHING_LOOPHEAD            => ForthError::NoMatchingLoopHead,

            ForthError::ABORT                           => ForthError::Abort,

            ForthError::NOT_IMPLEMENTED                 => ForthError::NotImplemented,

            ForthError::INVALID_ARGUMENT                => ForthError::InvalidArgument(arg),
            ForthError::WORD_NOT_FOUND                  => {
                let st = arg.to_str().ok_or(ForthError::InvalidArgument(arg))?;
                ForthError::WordNotFound(st)
            },
            ForthError::INVALID_CELL                    => {
                let xt = arg.to_xt().ok_or(ForthError::InvalidArgument(arg))?;
                ForthError::InvalidCell(xt)
            },

            // ForthError::INVALID_CONTROL_ENTRY           => ForthError::InvalidControlEntry(_),

            ForthError::INVALID_INDEX                   => ForthError::InvalidIndex(arg),
            ForthError::INVALID_CONTROL_INSTRUCTION     => {
                let xt = arg.to_xt().ok_or(ForthError::InvalidArgument(arg))?;
                ForthError::InvalidControlInstruction(xt)
            },
            ForthError::INVALID_EXECUTION_TOKEN         => ForthError::InvalidExecutionToken(arg),
            ForthError::INVALID_STRING                  => {
                let st = arg.to_str().ok_or(ForthError::InvalidArgument(arg))?;
                ForthError::InvalidString(st)
            },
            ForthError::INVALID_ESCAPE                  => {
                let n = arg.to_int().ok_or(ForthError::InvalidArgument(arg))?;
                if n < 0 || n > 255 {
                    return Err(ForthError::InvalidArgument(arg));
                }
                let b = n as u8;
                ForthError::InvalidEscape(b as char)
            },
            ForthError::INVALID_CHAR                    => {
                let n = arg.to_int().ok_or(ForthError::InvalidArgument(arg))?;
                ForthError::InvalidChar(n)
            },
            ForthError::INVALID_ADDRESS                 => {
                let addr = arg.to_addr().ok_or(ForthError::InvalidArgument(arg))?;
                ForthError::InvalidAddress(addr)
            },
            ForthError::INVALID_COUNTED_STRING          => {
                let st = arg.to_str().ok_or(ForthError::InvalidArgument(arg))?;
                ForthError::InvalidCountedString(st)
            },
            ForthError::INVALID_PC                      => {
                let xt = arg.to_xt().ok_or(ForthError::InvalidArgument(arg))?;
                ForthError::InvalidPC(xt.0)
            },

            ForthError::EXPECTED_XT                     => ForthError::ExpectedXT(arg),
            ForthError::EXPECTED_STRING                 => ForthError::ExpectedString(arg),
            ForthError::EXPECTED_INTEGER                => ForthError::ExpectedInteger(arg),
            ForthError::EXPECTED_VARADDR                => ForthError::ExpectedVarAddr(arg),
            ForthError::EXPECTED_ADDR                   => ForthError::ExpectedAddr(arg),

            // errors that can't be triggered by user code (yet)
            // ForthError::INVALID_ADDRESS_AND_OFFSET      => ForthError::InvalidAddressAndOffset(..),
            // ForthError::INVALID_STRING_VALUE            => ForthError::InvalidStringValue(_),
            // ForthError::INVALID_FUNCTION                => ForthError::InvalidFunction(_),
            // ForthError::IO_ERROR                        => ForthError::IOError(_),
            // ForthError::INVALID_ERROR_CODE              => ForthError::InvalidErrorCode(_),

            _ => {
                return Err(ForthError::InvalidErrorCode(code));
            }
        };

        Ok(err)
    }

    fn code(&self) -> u32 {
        match self {
            ForthError::StackUnderflow                  => ForthError::STACK_UNDERFLOW,
            ForthError::ControlStackUnderflow           => ForthError::CONTROL_STACK_UNDERFLOW,
            ForthError::ReturnStackUnderflow            => ForthError::RETURN_STACK_UNDERFLOW,

            ForthError::InvalidOperation                => ForthError::INVALID_OPERATION,
            ForthError::DivisionByZero		            => ForthError::DIVISION_BY_ZERO,

            ForthError::InvalidNumberBase	            => ForthError::INVALID_NUMBER_BASE,
            ForthError::NumberOutOfRange	            => ForthError::NUMBER_OUT_OF_RANGE,

            ForthError::InvalidEmptyString	            => ForthError::INVALID_EMPTY_STRING,
            ForthError::StringTooLong		            => ForthError::STRING_TOO_LONG,
            ForthError::StringOffsetTooLarge            => ForthError::STRING_OFFSET_TOO_LARGE,
            ForthError::StringNotFound		            => ForthError::STRING_NOT_FOUND,
            ForthError::InvalidHexEscape                => ForthError::INVALID_HEX_ESCAPE,
            ForthError::StringNotTerminated             => ForthError::STRING_NOT_TERMINATED,
            ForthError::StringIsReadonly                => ForthError::STRING_IS_READONLY,

            ForthError::FunctionSpaceOverflow	        => ForthError::FUNCTION_SPACE_OVERFLOW,
            ForthError::DictSpaceOverflow		        => ForthError::DICT_SPACE_OVERFLOW,
            ForthError::VarSpaceOverflow		        => ForthError::VAR_SPACE_OVERFLOW,
            ForthError::StringSpaceOverflow		        => ForthError::STRING_SPACE_OVERFLOW,

            ForthError::WordInvalidWhileCompiling		=> ForthError::WORD_INVALID_WHILE_COMPILING,
            ForthError::WordInvalidWhileInterpreting	=> ForthError::WORD_INVALID_WHILE_INTERPRETING,
            ForthError::DefiningWordInvalid			    => ForthError::DEFINING_WORD_INVALID,
            ForthError::UnfinishedColonDefinition		=> ForthError::UNFINISHED_COLON_DEFINITION,
            ForthError::DictEmpty			            => ForthError::DICT_EMPTY,

            ForthError::DeferredFunctionNotSet			=> ForthError::DEFERRED_FUNCTION_NOT_SET,
            ForthError::NotDeferredFunction             => ForthError::NOT_DEFERRED_FUNCTION,

            ForthError::NoMatchingLoopHead			    => ForthError::NO_MATCHING_LOOPHEAD,

            ForthError::NotImplemented                  => ForthError::NOT_IMPLEMENTED,

            ForthError::Abort                           => ForthError::ABORT,

            // some of these errors should produce an argument
            ForthError::InvalidArgument(_)              => ForthError::INVALID_ARGUMENT,
            ForthError::WordNotFound(_)			        => ForthError::WORD_NOT_FOUND,
            ForthError::InvalidCell(_)			        => ForthError::INVALID_CELL,
            ForthError::InvalidControlEntry(_)			=> ForthError::INVALID_CONTROL_ENTRY,
            ForthError::InvalidIndex(_)			        => ForthError::INVALID_INDEX,
            ForthError::InvalidControlInstruction(_)	=> ForthError::INVALID_CONTROL_INSTRUCTION,
            ForthError::InvalidExecutionToken(_)		=> ForthError::INVALID_EXECUTION_TOKEN,
            ForthError::InvalidString(_)				=> ForthError::INVALID_STRING,
            ForthError::InvalidEscape(_)				=> ForthError::INVALID_ESCAPE,
            ForthError::InvalidChar(_)			        => ForthError::INVALID_CHAR,
            ForthError::InvalidAddress(_)				=> ForthError::INVALID_ADDRESS,
            ForthError::InvalidAddressAndOffset(..)		=> ForthError::INVALID_ADDRESS_AND_OFFSET,
            ForthError::InvalidCountedString(_)			=> ForthError::INVALID_COUNTED_STRING,
            ForthError::InvalidStringValue(_)			=> ForthError::INVALID_STRING_VALUE,
            ForthError::InvalidFunction(_)				=> ForthError::INVALID_FUNCTION,
            ForthError::InvalidPC(_)				    => ForthError::INVALID_PC,
            ForthError::ReadOnlyAddress(_)              => ForthError::READ_ONLY_ADDRESS,

            ForthError::InvalidErrorCode(_)             => ForthError::INVALID_ERROR_CODE,

            ForthError::ExpectedXT(_)                   => ForthError::EXPECTED_XT,
            ForthError::ExpectedString(_)               => ForthError::EXPECTED_STRING,
            ForthError::ExpectedInteger(_)              => ForthError::EXPECTED_INTEGER,
            ForthError::ExpectedVarAddr(_)              => ForthError::EXPECTED_VARADDR,
            ForthError::ExpectedAddr(_)                 => ForthError::EXPECTED_ADDR,

            ForthError::IOError(_)			            => ForthError::IO_ERROR,
        }
    }
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
    const ADDR_STATE:      VarAddr = VarAddr(0);
    const ADDR_BASE:       VarAddr = VarAddr(1);
    const ADDR_SLASH_CDEF: VarAddr = VarAddr(2);
    const ADDR_SLASH_CXT:  VarAddr = VarAddr(3);
    const ADDR_SLASH_BRACKET:  VarAddr = VarAddr(4);

    // special variables
    const ADDR_IN     : VarAddr = VarAddr(VarAddr::BUILTIN | 0);
    const ADDR_OPTIMIZE:    VarAddr = VarAddr(VarAddr::BUILTIN | 1);

    const SOURCE_STRING : i32 = -1;
    const SOURCE_INPUT  : i32 =  0;

    pub fn new() -> ToyForth<'tf> {
        let mut tf = ToyForth{
            dstack:  std::vec::Vec::new(),
            rstack:  std::vec::Vec::new(),
            aux_stack: std::vec::Vec::new(),
            cstack:  std::vec::Vec::new(),
            ufuncs:  std::vec::Vec::new(),
            funcnames: std::vec::Vec::new(),

            dict:    std::vec::Vec::new(),
            vars:    std::vec::Vec::new(),
            strings: std::vec::Vec::new(),
            code:    std::vec::Vec::new(),

            pc: 0,

            runtime_does_func: u32::MAX,
            invalid_deferred_xt: XT(0),
            compile_comma_xt: XT(0),

            pad:     [0;256],
            word:    [0;256],
            pic:     [0;256],

            input: std::string::String::new(),
            input_off: 0,
            last_input_off: 0,
            last_word: ST::null(),

            source: ST::null(),
            source_id: 0,

            optimize: 1,

            in_stream: None,
            out_stream: None,
        };

        //
        // set up standard dictionary
        //

        // define words

        // First word in dict (addr 0) always holds BYE
        tf.add_prim("BYE", Instr::Bye);

        tf.invalid_deferred_xt = tf.mark_code();
        tf.add_instr(Instr::Error(ForthError::DEFERRED_FUNCTION_NOT_SET));
        tf.add_instr(Instr::Unnest);

        tf.add_prim("NOP", Instr::Nop);

        tf.add_prim("DUP", Instr::Dup);
        tf.add_prim("DROP", Instr::Drop);
        tf.add_prim("SWAP", Instr::Swap);
        tf.add_prim("OVER", Instr::Over);
        tf.add_prim("PICK", Instr::Pick);
        tf.add_prim("ROLL", Instr::Roll);
        tf.add_prim("ROT",  Instr::Rot);

        tf.add_prim("EXECUTE", Instr::Execute);

        tf.add_prim("+", Instr::BinaryOp(BinOp::Plus));
        tf.add_prim("-", Instr::BinaryOp(BinOp::Minus));
        tf.add_prim("*", Instr::BinaryOp(BinOp::Star));
        tf.add_prim("/", Instr::BinaryOp(BinOp::Slash));

        // double-cell arithmetic primitives
        tf.add_prim("M*", Instr::BinaryOp(BinOp::MStar));
        tf.add_prim("UM*", Instr::BinaryOp(BinOp::UMStar));

        tf.add_prim("AND", Instr::BinaryOp(BinOp::And));
        tf.add_prim("OR", Instr::BinaryOp(BinOp::Or));
        tf.add_prim("XOR", Instr::BinaryOp(BinOp::Xor));

        tf.add_prim("NEGATE", Instr::UnaryOp(UnaryOp::Negate));
        tf.add_prim("INVERT", Instr::UnaryOp(UnaryOp::Invert));

        tf.add_prim("LSHIFT", Instr::BinaryOp(BinOp::LeftShift));
        tf.add_prim("RSHIFT", Instr::BinaryOp(BinOp::RightShift));

        tf.add_prim(">", Instr::BinaryOp(BinOp::Greater));
        tf.add_prim("<", Instr::BinaryOp(BinOp::Less));
        tf.add_prim("=", Instr::BinaryOp(BinOp::Equal));
        tf.add_prim("<>", Instr::BinaryOp(BinOp::NotEqual));

        tf.add_prim("U>", Instr::BinaryOp(BinOp::UnsignedGreater));
        tf.add_prim("U<", Instr::BinaryOp(BinOp::UnsignedLess));

        // double-cell arithmetic builtins
        tf.add_func("*/MOD", ToyForth::builtin_star_slash_mod);
        tf.add_func("FM/MOD", ToyForth::builtin_fm_slash_mod);
        tf.add_func("SM/REM", ToyForth::builtin_sm_slash_rem);
        tf.add_func("UM/MOD", ToyForth::builtin_um_slash_mod);

        // address offset words
        tf.add_func("ADDR+", ToyForth::builtin_addr_plus);
        tf.add_func("ADDR-", ToyForth::builtin_addr_minus);

        let (emit,_) = tf.add_func("EMIT", ToyForth::builtin_emit);

        let (_,compile_comma_xt) = tf.add_immed("COMPILE,", ToyForth::builtin_add_instr);

        tf.compile_comma_xt = compile_comma_xt;
        tf.runtime_does_func = tf.add_anon_func(ToyForth::builtin_runtime_does).unwrap() as u32;

        tf.add_immed("RAISE-ERROR", ToyForth::builtin_raise_error);

        tf.add_func("ABORT", ToyForth::builtin_abort);

        // words that may be replaced with Forth definitions at some point
        tf.add_prim("BL", Instr::Push(Cell::int(' ' as i32)));
        tf.add_func("CHAR", ToyForth::builtin_char);
        tf.add_func("WORD", ToyForth::builtin_word);
        tf.add_func("C!", ToyForth::builtin_char_bang);
        tf.add_func("C@", ToyForth::builtin_char_at);
        tf.add_func("CHAR+", ToyForth::builtin_char_plus);
        tf.add_func("PARSE", ToyForth::builtin_parse);

        tf.add_func("ALLOT", ToyForth::builtin_allot);
        tf.add_func("CELL+", ToyForth::builtin_cell_plus);
        tf.add_func(",",     ToyForth::builtin_comma);
        tf.add_func("C,",    ToyForth::builtin_comma);

        tf.add_func("PIC", ToyForth::builtin_pic);

        tf.add_func("CALLOT", ToyForth::builtin_callot);
        tf.add_func("PAD", ToyForth::builtin_pad);
        tf.add_func("CSHRINK", ToyForth::builtin_cshrink);
        tf.add_func("CLENGTH", ToyForth::builtin_clength);

        tf.add_func("..", ToyForth::builtin_dot_dot);
        tf.add_func("U.", ToyForth::builtin_u_dot);
        tf.add_func("U.R", ToyForth::builtin_u_dot_r);

        tf.add_func(":", ToyForth::builtin_colon);
        tf.add_func(":NONAME", ToyForth::builtin_colon_noname);
        tf.add_immed(";", ToyForth::builtin_semi);
        tf.add_immed("POSTPONE", ToyForth::builtin_postpone);

        tf.add_immed("EXIT", ToyForth::builtin_exit);

        tf.add_immed("[CHAR]", ToyForth::builtin_brak_char);

        tf.add_immed("IF", ToyForth::builtin_if);
        tf.add_immed("ELSE", ToyForth::builtin_else);
        tf.add_immed("THEN", ToyForth::builtin_then);

        tf.add_immed("CASE", ToyForth::builtin_case);
        tf.add_immed("OF", ToyForth::builtin_of);
        tf.add_immed("ENDOF", ToyForth::builtin_endof);
        tf.add_immed("ENDCASE", ToyForth::builtin_endcase);

        tf.add_immed("DO", ToyForth::builtin_do);
        tf.add_immed("?DO", ToyForth::builtin_qdo);
        tf.add_immed("LOOP", ToyForth::builtin_loop);
        tf.add_immed("+LOOP", ToyForth::builtin_plus_loop);
        tf.add_immed("I", ToyForth::builtin_loop_ind0);
        tf.add_immed("J", ToyForth::builtin_loop_ind1);

        tf.add_immed("UNLOOP", ToyForth::builtin_unloop);
        tf.add_immed("LEAVE", ToyForth::builtin_leave);

        tf.add_immed("BEGIN", ToyForth::builtin_begin);
        tf.add_immed("AGAIN", ToyForth::builtin_again);
        tf.add_immed("UNTIL", ToyForth::builtin_until);
        tf.add_immed("WHILE", ToyForth::builtin_while);
        tf.add_immed("REPEAT", ToyForth::builtin_repeat);

        tf.add_immed("RECURSE", ToyForth::builtin_recurse);

        tf.add_func("IMMEDIATE", ToyForth::builtin_immediate);

        tf.add_func("FIND", ToyForth::builtin_find);
        tf.add_func("FIND-NAME", ToyForth::builtin_find_name);

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
        tf.add_immed("S\\\"", ToyForth::builtin_s_backslash_quote);
        tf.add_immed(".\"", ToyForth::builtin_dot_quote);
        tf.add_immed("C\"", ToyForth::builtin_c_quote);

        tf.add_immed(".(", ToyForth::builtin_dot_oparen);
        tf.add_immed("(", ToyForth::builtin_oparen);
        tf.add_immed("\\", ToyForth::builtin_backslash);

        tf.add_func("/ETYPE", ToyForth::builtin_err_type);
        tf.add_immed("E\"", ToyForth::builtin_err_quote);
        tf.add_func(".E", ToyForth::builtin_dot_e);

        tf.add_immed("[", ToyForth::builtin_obracket);
        tf.add_immed("]", ToyForth::builtin_cbracket);
        tf.add_immed("LITERAL", ToyForth::builtin_literal);

        tf.add_func("'", ToyForth::builtin_tick);
        tf.add_immed("[']", ToyForth::builtin_brak_tick);

        tf.add_func("DEFER", ToyForth::builtin_defer);
        tf.add_func("DEFER!", ToyForth::builtin_defer_bang);
        tf.add_func("DEFER@", ToyForth::builtin_defer_at);
        tf.add_immed("ACTION-OF", ToyForth::builtin_action_of);
        tf.add_immed("IS", ToyForth::builtin_is);

        tf.add_func("CREATE", ToyForth::builtin_create);
        tf.add_immed("DOES>", ToyForth::builtin_does);
        tf.add_func(">BODY", ToyForth::builtin_body);

        tf.add_func("/EMPTY-RETURN", ToyForth::builtin_empty_return);
        tf.add_func("/CLEAR-COMPILE-STATE", ToyForth::builtin_clear_compile_state);

        tf.add_func("EVALUATE", ToyForth::builtin_evaluate);

        tf.add_prim("/REFILL", Instr::Refill);
        tf.add_func("/INPUT-LENGTH", ToyForth::builtin_input_len);

        // debugging
        tf.add_func(".S", ToyForth::builtin_dot_s);
        tf.add_func("SEE", ToyForth::builtin_see);
        // tf.add_func("DUMP", ToyForth::builtin_dump);

        // define state variables
        //
        // FIXME: instead of /CDEF and /CXT, we should store the nest-sys
        // on the return stack.
        //
        let state_vars = vec![ "STATE", "BASE", "/CDEF", "/CXT", "/BRACKET" ];
        for v in &state_vars {
            let addr = tf.new_var(Cell(0)).unwrap();
            tf.add_prim(v, Instr::Push(addr.to_cell()));
        }

        tf.set_var_at(ToyForth::ADDR_BASE, Cell::int(10)).unwrap();

        // Add builtins
        tf.add_prim(">IN",    Instr::Push(ToyForth::ADDR_IN.to_cell()));
        tf.add_prim("/OPTIMIZE", Instr::Push(ToyForth::ADDR_OPTIMIZE.to_cell()));

        tf.add_func("DEPTH",  ToyForth::builtin_depth);
        tf.add_func("CONTROL-DEPTH",  ToyForth::builtin_control_depth);
        tf.add_func("RETURN-DEPTH",  ToyForth::builtin_return_depth);
        tf.add_func("HERE",   ToyForth::builtin_here);
        tf.add_func("CHAR-HERE", ToyForth::builtin_char_here);
        tf.add_func("CODE-HERE", ToyForth::builtin_code_here);
        tf.add_func("UNUSED", ToyForth::builtin_unused);

        // define standard words that are not primitives
        tf.add_word("CR", &[
            Instr::Push(Cell::int('\n' as i32)),
            Instr::Func(emit as u32),
            Instr::Unnest,
        ], 0).unwrap();

        tf.bootstrap_interpret("\
: . .. BL EMIT ;

: 0<  0 < ;
: 0>  0 > ;
: 0=  0 = ;
: 0<> 0 <> ;
: 1- 1 - ;
: 1+ 1 + ;

: MAYBE-DISPLAY-ABORT ( x caddr u -- )
    ROT ( x caddr u -- caddr u x )
    0<> IF .\" Error: \" TYPE CR ABORT THEN
    DROP DROP
;

: ABORT\" POSTPONE S\" POSTPONE MAYBE-DISPLAY-ABORT ; IMMEDIATE

130 CONSTANT ERR:WORD-NOT-FOUND

0    CONSTANT FALSE
0 0= CONSTANT TRUE

: DECIMAL 10 BASE ! ;
: HEX     16 BASE ! ;

: ALIGN   ; \\ data-space entities are always aligned
: ALIGNED DUP DROP ; \\ data-space entities are always aligned
: CELLS   0 + ; \\ cells are each one address unit wide
: CHARS   0 + ; \\ chars in a-addr space are also one unit wide

: BUFFER: CREATE ALLOT ;

: ABS DUP 0< IF NEGATE THEN ;

: +! SWAP OVER @ + SWAP ! ;

: NIP  SWAP DROP ;
: TUCK SWAP OVER ;

: PARSE-NAME BL PARSE ;

: SPACE BL EMIT ;
: SPACES DUP 0> IF 1 DO SPACE LOOP THEN ; 

: 2DROP ( n1 n2 -- ) DROP DROP ;
: 2DUP ( n1 n2 -- n1 n2 n1 n2 ) OVER OVER ;
: 2OVER ( n1 n2 n3 n4 -- n1 n2 n3 n4 n1 n2 ) 3 PICK 3 PICK ;
: 2SWAP ( n1 n2 n3 n4 -- n3 n4 n1 n2 ) 3 ROLL 3 ROLL ;
: 2>R ( n1 n2 -- ) ( R: -- n1 n2 )
    STATE @ 0= ABORT\" Can only use word while compiling\"
    POSTPONE SWAP POSTPONE >R POSTPONE >R
; IMMEDIATE

: 2R> ( -- n1 n2 ) ( R: n1 n2 -- )
    STATE @ 0= ABORT\" Can only use word while compiling\"
    POSTPONE R> POSTPONE R> POSTPONE SWAP
; IMMEDIATE

: 2R@ ( -- n1 n2 ) ( R: n1 n2 -- n1 n2 )
    STATE @ 0= ABORT\" Can only use word while compiling\"
    POSTPONE R> POSTPONE R>
    POSTPONE 2DUP
    POSTPONE >R POSTPONE >R
    POSTPONE SWAP
; IMMEDIATE

: 2! ( x1 x2 addr -- )
    SWAP    ( x1 x2 addr -- x1 addr x2 )
    OVER    ( x1 addr x2 -- x1 addr x2 addr )
    !       ( x1 addr x2 addr -- x1 addr )
    CELL+   ( x1 addr -- x1 addr1 )
    !
;

: 2@ ( addr -- )
    DUP     ( addr -- addr addr )
    CELL+   ( addr addr -- addr addr1 )
    @       ( addr addr1 -- addr x1 )
    SWAP    ( addr x1 -- x1 addr )
    @       ( x1 addr -- x1 x2 )
;

: MIN ( n1 n1 -- n3 ) 2DUP > IF SWAP THEN DROP ;
: MAX ( n1 n1 -- n3 ) 2DUP < IF SWAP THEN DROP ;

\\ From the forth-standard.org discussion of the word
: WITHIN ( test low high -- flag ) OVER - >R - R> U< ;

: 2* 1 LSHIFT ;
: 2/ 1 RSHIFT ;

: MOD ( num div -- rem )
    2DUP    ( num div         -- num div num div )
    /       ( num div num div -- num div quot )
    *       ( num div quot    -- num prod )
    -       ( num prod        -- rem )
;

\\ Do we need to do this as double-cell quantities to handle overflow?
: /MOD ( num div -- rem quot )
    2DUP /  ( num div -- num div quot )
    DUP >R  ( num div quot -- num div quot ) ( R: -- quot )
    * -     ( num div quot -- rem ) ( R: quot -- quot )
    R>      ( rem -- rem quot ) ( R: quot -- )
;

: COUNT DUP CHAR+ SWAP C@ ;

\\ Should this be a builtin?
: ?DUP DUP 0<> IF DUP THEN ;

\\ This should probably be a builtin so we can use memmove
: MOVE >R SWAP R> 0 DO 2DUP @ SWAP ! CELL+ SWAP CELL+ SWAP LOOP 2DROP ;

: COUNT-DIGITS 1 >R BEGIN 10 / DUP 0<> WHILE R> 1+ >R REPEAT DROP R> ;

: .R ( n1 n2 -- )
    OVER COUNT-DIGITS ( n1 n2 digs1 )
    - DUP       ( n1 n2 digs2 -- n1 n2-digs1 n2-digs1 )
    0> IF       ( n1 n2-digs1 n2-digs1 -- n1 n2-digs1 )
        SPACES  ( n1 n2-digs1 -- n1 )
    ELSE
        DROP    ( n1 n2-digs1 -- n1 )
    THEN
    ..          ( n1 -- )
;

\\ consider moving VALUE/TO into builtins?  This would make the words
\\ they use safer, but adds more builtins.
: VALUE CREATE , DOES> @ ;

\\ : TO
\\     STATE @ IF
\\         \\ compiling
\\         POSTPONE ' >BODY POSTPONE !
\\     ELSE
\\         \\ interpreting
\\         ' >BODY !
\\     THEN
\\ ; IMMEDIATE

: TO
    ' >BODY
    STATE @ IF
        POSTPONE LITERAL
        POSTPONE !
    ELSE
        !
    THEN
; IMMEDIATE

VARIABLE >PIC-IN
VARIABLE >PIC-STR
: <# 
    0   >PIC-IN !
    PIC >PIC-STR !
;

\\ Double cell stuff
: S>D DUP 0< IF -1 ELSE 0 THEN ;
: */ */MOD SWAP DROP ;

: REFILL 
    /REFILL /INPUT-LENGTH 0<>
;

VARIABLE LAST-WORD
CREATE REPL-PROMPT 2 ALLOT

: SET-DEFAULT-PROMPT S\" ok\" REPL-PROMPT 2! ;

: PARSE-NUMBER  ( caddr u -- n 1 | caddr u 0 )
    OVER >R             ( caddr u -- caddr u )      ( R: -- caddr )
    >R                  ( caddr u -- caddr )        ( R: caddr -- caddr u )
    DUP C@              ( caddr -- caddr ch )       ( R: caddr u -- caddr u )
    [CHAR] - =          ( caddr ch -- caddr -? )    ( R: caddr u -- caddr u )
    SWAP OVER           ( caddr -? -- -? caddr -? ) ( R: caddr u -- caddr u )
    0<> IF              ( -? caddr -? -- -? caddr ) ( R: caddr u -- caddr u )
        \\ remove leading minus, update length
        CHAR+           ( -? caddr -- -? caddr1 )   ( R: caddr u -- caddr u )
        R> 1 - >R       ( -? caddr -- -? caddr1 )   ( R: caddr u -- caddr u1 )
    THEN

    0 SWAP R> DUP >R    ( -? caddr -- -? 0 caddr u ) ( R: caddr u -- caddr u )
    >NUMBER             ( -? 0 caddr u -- -? ud caddr2 u2 ) ( R: caddr u -- caddr u )
    R> <>               ( -? ud caddr2 u2 -- -? ud caddr2 neq? ) ( R: caddr u -- caddr )
    IF                  ( -? ud caddr2 neq? -- -? ud caddr2 ) ( R: caddr -- caddr )
        R> [ ERR:WORD-NOT-FOUND ] RAISE-ERROR
    THEN

    DROP SWAP           ( -? ud caddr2 -- ud -? )   ( R: caddr -- caddr )
    R> DROP             ( ud -? -- ud -? )          ( R: caddr -- )
    IF NEGATE THEN      ( ud -? -- ud )
;

: SHOW-PROMPT
    REPL-PROMPT 2@
    ?DUP IF
        TYPE CR
    ELSE
        DROP
    THEN
;

: /INTERPRET
    BEGIN
        \\ parse next word
        BL PARSE            ( -- caddr u )

    ?DUP WHILE              \\ exit if there is no word

        OVER LAST-WORD !    ( caddr u -- caddr u )
        FIND-NAME           ( caddr u -- caddr u 0 | xt 1 | xt -1 )

        CASE
        0 OF                ( caddr u 0 -- caddr u ) \\ 0: not found, try parse as number
            PARSE-NUMBER
            STATE @ IF POSTPONE LITERAL THEN
        ENDOF

        1 OF                ( xt 1 -- xt ) \\ 1: immediate word, always execute
            EXECUTE         ( xt -- )
        ENDOF

        -1 OF               \\ -1: non-immediate word, execute or compile
            STATE @ IF
                POSTPONE COMPILE,    ( xt -- ) \\ compiling
            ELSE
                EXECUTE     ( xt -- ) \\ not compiling
            THEN
        ENDOF

        ENDCASE

    REPEAT
    DROP                    ( caddr -- )
;

: QUIT 
    /EMPTY-RETURN
    /CLEAR-COMPILE-STATE
    BEGIN
        SHOW-PROMPT
        \\ .\" ok\" CR
        REFILL IF
            /INTERPRET
            ( handle INTERPRET )
        THEN
    AGAIN
;

").unwrap();

        // tf.add_func("PARSE-NAME", ToyForth::builtin_parse);

        eprintln!("Code cell size is {}", std::mem::size_of::<Instr>());
        eprintln!("Data cell size is {}", std::mem::size_of::<Cell>());

        return tf;
    }

    fn cpush_if_addr(&mut self, xt: XT) {
        self.cstack.push(ControlEntry::IfAddr(xt));
    }

    fn cpush_else_addr(&mut self, xt: XT) {
        self.cstack.push(ControlEntry::ElseAddr(xt));
    }

    fn cpush_do_addr(&mut self, xt: XT, qdo: Option<XT>) {
        self.cstack.push(ControlEntry::DoAddr(DoInfo{ head:xt, qdo: qdo }));
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

    fn cpush_case(&mut self, exit_xt: XT) {
        self.cstack.push(ControlEntry::CaseEntry{exit_xt:exit_xt});
    }

    fn cpush_case_of(&mut self, exit_xt: XT, next_xt: XT) {
        self.cstack.push(ControlEntry::OfEntry{exit_xt:exit_xt, next_xt:next_xt});
    }

    fn cpop_entry(&mut self) -> Result<ControlEntry,ForthError> {
        self.cstack.pop().ok_or(ForthError::ControlStackUnderflow)
    }

    fn cpop_loop_addr(&mut self) -> Result<DoInfo, ForthError> {
        let ctl = self.cpop_entry()?;
        if let ControlEntry::DoAddr(info) = ctl {
            Ok(info)
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

    fn cpop_case(&mut self) -> Result<XT, ForthError> {
        let ctl = self.cpop_entry()?;
        if let ControlEntry::CaseEntry{exit_xt} = ctl {
            Ok(exit_xt)
        } else {
            Err(ForthError::InvalidControlEntry(ctl))
        }
    }

    fn cpop_case_of(&mut self) -> Result<(XT,XT), ForthError> {
        let ctl = self.cpop_entry()?;
        if let ControlEntry::OfEntry{exit_xt, next_xt} = ctl {
            Ok((exit_xt,next_xt))
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

    fn cpeek_case(&mut self) -> Result<XT,ForthError> {
        let ctl = self.cstack.last().ok_or(ForthError::ControlStackUnderflow)?;
        if let ControlEntry::CaseEntry{exit_xt} = ctl {
            Ok(*exit_xt)
        } else {
            Err(ForthError::InvalidControlEntry(*ctl))
        }
    }

    pub fn print_backtrace(&self) {
        // build xt -> dict entry
        use std::collections::BTreeMap;

        let mut xt_map = BTreeMap::<u32,usize>::new();
        for (ind,ent) in self.dict.iter().enumerate() {
            xt_map.insert(ent.start.0, ind);
        }

        let rstack = {
            let mut rstack : Vec<XT> = self.rstack.iter().map(|xt| *xt).collect();

            // first stack frame is pc
            rstack.push(XT(self.pc));
            rstack
        };

        let find_entry = |xt: XT| -> Option<&DictEntry> {
            let mut it = xt_map.range(0..xt.0+1);
            let (_,ind) = it.next_back()?;

            let entry = &self.dict[*ind];
            if entry.start.0 <= xt.0 && entry.end.0 > xt.0 {
                return Some(entry);
            }

            None
        };

        eprintln!("Backtrace:");

        // then proceed through return stack
        // FIXME: add an aux stack for return stack manip words
        //        currently we ignore non-XT values
        for (ind,xt) in rstack.iter().rev().enumerate() {
            let xt_pc = if ind == 0 || xt.0 == 0 { xt.0 } else { xt.0 - 1 };
            match find_entry(*xt) {
                Some(entry) => {
                    let name = if entry.st != ST::null() {
                        self.maybe_string_at(entry.st).unwrap_or("<invalid name>")
                    } else {
                        "<NONAME>"
                    };

                    eprintln!("[{:5}] [xt] {:24} | {}", ind, xt.0, name);

                    self.print_code_with_highlight(entry.start, 2, true, xt_pc, false);
                },
                None => {
                    eprintln!("[{:5}] [xt] {:24} | <unknown entry>", ind, xt.0);

                    if (xt_pc as usize) < self.code.len() {
                        self.print_code_with_highlight(*xt, 2, true, xt_pc, false);
                    }
                },
            }
        }

        eprintln!("\n");
    }

    pub fn print_code(&self, xt: XT) {
        self.print_code_with_highlight(xt, 0, false, 0, false);
    }

    pub fn print_code_with_highlight(&self, xt: XT, indent: usize, highlight: bool, highlight_xt: u32, rel_xt: bool) {
        use std::collections::HashMap;

        let mut xt_map = HashMap::<u32,&str>::with_capacity(self.dict.len());
        for ent in &self.dict {
            let w = self.string_at(ent.st);
            xt_map.insert(ent.start.0, w);
        };

        let indent_str = " ".repeat(4*indent);
        let highlight_i = if highlight_xt > xt.0 { (highlight_xt - xt.0) as usize } else { 0 };

        for (i,instr) in self.code[xt.0 as usize..].iter().enumerate() {
            let istr = format!("{:?}", instr);
            let highlight_str = if highlight && i == highlight_i { " <----" } else { "" };
            let highlight_char = if highlight && i == highlight_i { "*" } else { " " };
            let ind = if rel_xt { i } else { i+(xt.0 as usize) };

            if highlight && i == highlight_i {
                // eprintln!("{}vvvvvvvv", &indent_str);
                // eprintln!("");
            }
            match instr {
                Instr::Push(w) => {
                    if let CellKind::Int(n) = w.kind() {
                        eprintln!("{}[{:5}{}] {:30} {:6} |    Push([int] {})",
                            &indent_str, ind, highlight_char, istr, highlight_str, n);
                    } else {
                        eprintln!("{}[{:5}{}] {:30} {:6} |    Push({})",
                            &indent_str, ind, highlight_char, istr, highlight_str, w);
                    }
                }
                Instr::DoCol(xt) => {
                    let name = xt_map[&xt.0];
                    eprintln!("{}[{:5}{}] {:30} {:6} | C: {}",
                        &indent_str, ind, highlight_char, istr, highlight_str, name);
                },
                Instr::Func(func_ind) => {
                    let func_ind = *func_ind as usize;
                    let name = if func_ind < self.ufuncs.len() && func_ind < self.funcnames.len() {
                        &self.funcnames[func_ind]
                    } else {
                        "<unknown>"
                    };

                    eprintln!("{}[{:5}{}] {:30} {:6} | F: {}",
                        &indent_str, ind, highlight_char, istr, highlight_str, name);
                },
                _ => {
                    eprintln!("{}[{:5}{}] {:30} {:6} |    {}",
                        &indent_str, ind, highlight_char, istr, highlight_str, istr);
                }
            };
            if highlight && i == highlight_i {
                eprintln!("{}^^^^^^^^", &indent_str);
            }

            if let Instr::Unnest = *instr {
                break
            }

            if let Instr::Jump(_) = *instr {
                break
            }
        }
    }

    pub fn print_word_code(&self, word: &str) {
        match self.lookup_word(word) {
            Ok(xt) => {
                eprintln!("word: {}\ncode:", word);
                self.print_code(xt);
                eprintln!(".\n");
            }
            Err(err) => {
                eprintln!("error: {:?}", err);
            }
        };
    }

    pub fn print_stacks(&self, msg: &str) {
        eprintln!(">>> {}: ",msg);
        eprintln!("\nData:");
        if self.dstack.len() == 0 {
            eprintln!("<empty>");
        }
        for (i,w) in self.dstack.iter().enumerate() {
            let k = w.kind();
            if let CellKind::Str(st) = k {
                let s0 = self.maybe_string_at(st);
                if let Ok(s) = s0 {
                    eprintln!("[D {:3}] {} \"{}\"", i,st.descr(), s);
                } else if let Ok(b) = self.bytes_at(st) {
                    eprintln!("[D {:3}] {:?} {:?}", i,w.kind(), b);
                } else {
                    eprintln!("[D {:3}] invalid ST {}", i, st.descr());
                }
            } else {
                eprintln!("[D {:3}] {}", i,w);
            }
        }
        if self.rstack.len() > 0 {
            eprintln!("\nReturn:");
            for (i,xt) in self.rstack.iter().enumerate() {
                eprintln!("[R {:3}] {}", i,xt.to_cell());
            }
        }
        if self.cstack.len() > 0 {
            eprintln!("\nControl");
            for (i,itm) in self.cstack.iter().enumerate() {
                eprintln!("[C {:3}] {:?}", i, itm);
            }
        }
        eprintln!("done\n");
    }

    pub fn builtin_see(&mut self) -> Result<(),ForthError> {
        self.push_int(' ' as i32)?;
        self.builtin_parse()?;

        let _len = self.pop_int()?;
        let st = self.pop_str()?;

        let w = self.maybe_string_at(st)?;

        self.print_word_code(w);
        Ok(())
    }

    pub fn builtin_dot_s(&mut self) -> Result<(),ForthError> {
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

    pub fn stdout_interpret(&mut self, s: &str) -> Result<(), ForthError> {
        let stdout = std::io::stdout();
        let w = Rc::new(RefCell::new(stdout));

        return self.capture_interpret(s, w);
    }

    pub fn stderr_interpret(&mut self, s: &str) -> Result<(), ForthError> {
        let stderr = std::io::stderr();
        let w = Rc::new(RefCell::new(stderr));

        return self.capture_interpret(s, w);
    }

    pub fn interpret(&mut self, s: &str) -> Result<(), ForthError> {
        // initial interpret is dumb...

        let quit_xt = self.lookup_word("QUIT")?;
        self.pc = quit_xt.0;
        if let ForthResult::Bye = self.exec()? {
            return Ok(());
        }

        for l in s.lines() {
            // eprintln!("l: {}", l);
            self.set_input(l);

            let ret = self.exec()?;
            if let ForthResult::Bye = ret {
                return Ok(());
            }
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

    pub fn check_not_compiling(&self) -> Result<(), ForthError> {
        if !self.compiling() {
            Ok(())
        } else {
            Err(ForthError::WordInvalidWhileCompiling)
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

        if w == Cell(0) {
            Ok(())
        } else {
            Err(ForthError::DefiningWordInvalid)
        }
    }

    pub fn clear_stacks(&mut self) {
        self.dstack.clear();
        self.rstack.clear();
        self.cstack.clear();

        // reset any definitions, enter compilation state
        self.set_var_at(ToyForth::ADDR_STATE,      Cell::int(0)).unwrap();
        self.set_var_at(ToyForth::ADDR_SLASH_CDEF, Cell(0)).unwrap();
        self.set_var_at(ToyForth::ADDR_SLASH_CXT,  Cell(0)).unwrap();
    }

    pub fn builtin_raise_error(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        let code = self.pop_int()?;
        self.add_instr(Instr::Error(code as u32));

        Ok(())
    }

    pub fn builtin_abort(&mut self) -> Result<(), ForthError> {
        Err(ForthError::Abort)
    }

    pub fn bootstrap_interpret(&mut self, s: &str) -> Result<(), ForthError> {
        // initial interpret is dumb...

        for l in s.lines() {
            self.set_input(l);
            self.builtin_interpret()?;
        }

        Ok(())
    }

    pub fn handle_error(&mut self, err: &ForthError) {
        eprint!("E{}: ", err.code());
        match err {
            ForthError::Abort => {},

            ForthError::WordNotFound(st) => {
                if let Ok(s) = self.maybe_string_at(*st) {
                    eprintln!("Cell not found: {}", s);
                } else {
                    let b = self.bytes_at(*st);
                    eprintln!("Cell not found (bytes): {:?}", b);
                }
            },
            ForthError::InvalidArgument(w) => {
                eprintln!("Invalid argument: {}", w);
            },
            ForthError::ExpectedXT(w) => {
                eprintln!("Expected XT but found: {}", w);
            },
            ForthError::ExpectedString(w) => {
                eprintln!("Expected string but found: {}", w);
            },
            ForthError::ExpectedInteger(w) => {
                eprintln!("Expected integer but found: {}", w);
            },
            ForthError::ExpectedVarAddr(w) => {
                eprintln!("Expected var address but found: {}", w);
            },
            ForthError::ExpectedAddr(w) => {
                eprintln!("Expected address (var or char) but found: {}", w);
            },
            ForthError::InvalidCell(xt) => {
                eprintln!("Invalid cell at xt = {}", xt.0);
            },
            ForthError::InvalidControlEntry(ctl) => {
                // TODO: print control stack
                eprintln!("Invalid control entry: {:?}", ctl);
            },
            ForthError::InvalidIndex(w) => {
                eprintln!("Invalid index: {:?}", w);
            },
            ForthError::InvalidControlInstruction(xt) => {
                // TODO: print instructions around this one
                eprintln!("Invalid control instruction xt={:?}", xt.0);
            },
            ForthError::InvalidExecutionToken(w) => {
                eprintln!("Invalid execution token (expected XT): {:?}", w);
            },
            ForthError::InvalidString(st) => {
                let b = self.bytes_at(*st);
                eprintln!("Invalid string (not utf8): st={:?} bytes={:?}", st, b);
            },
            ForthError::InvalidChar(value) => {
                eprintln!("Invalid char (not in range): {}", value);
            },
            ForthError::InvalidAddress(addr) => {
                eprintln!("Invalid address (out of range or not a valid builtin): {:?}", addr);
            },
            ForthError::InvalidCountedString(st) => {
                let b = self.bytes_at(*st);
                eprintln!("Invalid counted string (len != count): st={:?}, bytes={:?}", st,b);
            },
            ForthError::InvalidStringValue(val) => {
                eprintln!("Invalid string value: u32 {:x} is not a valid string", val);
            },
            ForthError::InvalidFunction(ind) => {
                eprintln!("Invalid function index {}", ind);
            },

            ForthError::IOError(err) => {
                eprintln!("IO Error: {}", err);
            },

            _ => {
                eprintln!("Error: {:?}", err);
            }
        }

        if let ForthError::Abort = err {
        } else {
            eprintln!("Input: {}", self.input);

            if let ST::InputSpace(ScratchLoc{len,off}) = self.last_word {
                let pfx = format!("{:>width$}", "^", width=(off as usize)+1);
                let sfx = if len > 0 {
                    format!("{:->width$}", "^", width=(len as usize))
                } else {
                    "".to_string()
                };
                eprintln!("Word:  {}{}", pfx,sfx);
            }

            // FIXME: correctly handle utf-8 input...
            let pfx = format!("{:>width$}", "^", width=self.last_input_off+1);
            let sfx = if self.input_off > self.last_input_off {
                format!("{:->width$}", "^", width=self.input_off-self.last_input_off)
            } else {
                "".to_string()
            };
            eprintln!("Parsed:{}{}", pfx,sfx);

            self.print_backtrace();

            self.print_stacks("--[ STACKS ]--");
            // TODO: backtrace the stacks
        }

        self.clear_stacks();
        self.input.clear();
        self.input_off = 0;
        self.last_input_off = 0;
    }

    pub fn builtin_interpret(&mut self) -> Result<(), ForthError> {
        let ret = self.inner_interpret();

        if let Err(err) = &ret {
            self.handle_error(err);
        }

        ret
    }

    pub fn inner_interpret(&mut self) -> Result<(), ForthError> {
        loop {
            self.push_int(' ' as i32)?;
            self.builtin_parse()?;
            self.swap()?;
            self.last_word = self.pop_str()?;
            self.push(self.last_word.to_cell())?;
            self.swap()?;
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

                self.data_to_aux()?;    // ( caddr u -- caddr )           r: ( -- u )
                self.dup()?;                    // ( caddr -- caddr caddr )       r: ( u -- u )
                self.builtin_char_at()?;        // ( caddr caddr -- caddr ch )    r: ( u -- u )
                self.push_int('-' as i32)?;     // ( caddr ch -- caddr ch '-' )   r: ( u -- u )
                self.binary_op(BinOp::Equal)?;      // ( caddr ch '-' -- caddr neg? ) r: ( u -- u )
                self.swap()?;                   // ( caddr neg? -- neg? caddr )   r: ( u -- u )
                self.over()?;                   // ( neg? caddr -- neg? caddr neg? ) r: ( u -- u )

                if self.pop_int()? != 0 {       // ( neg? caddr neg? -- neg? caddr ) r: ( u -- u )
                    self.builtin_char_plus()?;  // ( neg? caddr -- neg? caddr2 )
                    self.aux_to_data()?; // ( neg? caddr2 -- neg? caddr2 u ) r: ( u -- )
                    let u = self.pop_int()?;    // ( neg? caddr2 u -- neg? caddr2 ) r: ( -- )
                    self.push_int(u - 1)?;      // ( neg? caddr2 -- neg? caddr2 u2 ) r: ( -- )

                    len -= 1;

                    self.data_to_aux()?;    // ( neg? caddr2 u2 -- neg? caddr2 )  r: ( -- u2 )
                }

                self.push_int(0)?;              // ( neg? caddr -- neg? caddr 0 ) r: ( u -- u )
                self.swap()?;                   // ( neg? caddr 0 -- neg? 0 caddr ) r: ( u -- u )

                self.aux_to_data()?;    // ( neg? 0 caddr -- neg? 0 caddr u ) r: ( u -- )

                self.builtin_to_number()?;      // ( neg? 0 caddr u1 -- neg? ud caddr u2 )

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
                    self.add_instr(Instr::Push(Cell::int(num)));
                }
            } else {
                let xt = self.pop_xt()?;
                if wh == 1 || !is_compiling {
                    self.ret_push_bye()?;
                    self.exec_at(xt)?;
                } else {
                    self.add_instr(Instr::DoCol(xt));
                }
            }
        }

        Ok(())
    }

    pub fn refill_from_in_stream(&mut self) -> Result<bool, ForthError> {
        self.last_input_off = 0;
        self.input_off = 0;
        self.input.clear();

        if let Some(inp) = &mut self.in_stream {
            let r = inp.borrow();
            let s = &mut self.input;
            r.read_line(s)?;
            match s.pop() {
                Some(ch) => {
                    if ch != '\n' {
                        s.push(ch);
                    }

                    return Ok(true);
                },

                None => {
                    return Ok(false);
                }
            }
        }

        Ok(false)
    }

    pub fn builtin_refill(&mut self) -> Result<(), ForthError> {
        self.refill_from_in_stream()?;
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

        let quit_xt = self.lookup_word("QUIT")?;
        self.pc = quit_xt.0;

        loop {
            match self.exec() {
                Ok(ForthResult::Bye) => {
                    break;
                },

                Ok(ForthResult::Refill) => {
                    let succ = self.refill_from_in_stream()?;
                    if !succ {
                        break;
                    }
                },

                Err(err) => {
                    self.handle_error(&err);
                    self.pc = quit_xt.0;
                },
            }
        }

        /*
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
        */

        self.in_stream  = old_in;
        self.out_stream = old_out;

        return Ok(());
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

    pub fn aux_stack_depth(&self) -> usize {
        return self.aux_stack.len();
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
            start: xt,
            end: self.mark_code(),
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

    fn add_named_func(&mut self, name: &str, func: fn (&mut ToyForth<'tf>) -> Result<(),ForthError>) -> Result<usize,ForthError> {
        let func_ind = self.ufuncs.len();

        if func_ind > 0xffff_ffff {
            return Err(ForthError::FunctionSpaceOverflow);
        }

        self.ufuncs.push(ForthFunc(func));
        self.funcnames.push(name.to_string());
        Ok(func_ind)
    }


    pub fn add_anon_func(&mut self, func: fn (&mut ToyForth<'tf>) -> Result<(),ForthError>) -> Result<usize,ForthError> {
        self.add_named_func("<anonymous>", func)
    }

    pub fn add_function(&mut self, word: &str, func: fn (&mut ToyForth<'tf>) -> Result<(),ForthError>) -> Result<(usize,XT),ForthError> {
        self.add_string(word)?;

        let func_ind = self.add_named_func(word, func)?;
        let xt = self.add_primitive(word, Instr::Func(func_ind as u32))?;

        Ok((func_ind,xt))
    }

    pub fn add_word(&mut self, word: &str, code: &[Instr], flags: u32) -> Result<XT,ForthError> {
        let entry = self.mark_code();
        for instr in code {
            self.add_instr(*instr);
        }

        let end = self.mark_code();

        self.define_word(word,entry,end,flags)?;
        Ok(entry)
    }

    pub fn allocate_string(&mut self, st: ST) -> Result<ST,ForthError> {
        // FIXME: completely unnecessary copy here...
        let s = self.maybe_string_at(st)?.to_string();

        self.add_string(&s)
    }

    pub fn define_word(&mut self, word: &str, entry: XT, end: XT, flags: u32) -> Result<ST,ForthError> {
        let st = self.add_string(word)?;

        self.dict.push(DictEntry{
            st: st,
            start: entry,
            end: end,
            flags: flags,
        });

        return Ok(st);
    }

    pub fn lookup_dict_entry(&self, word: &str) -> Result<DictEntry, ForthError> {
        // FIXME: use hash map for fast lookup

        if word.len() == 0 {
            return Err(ForthError::StringNotFound);
        }

        for ent in self.dict.iter().rev() {
            // skip :NONAME definitions
            if ent.st == ST::null() {
                continue;
            }

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
                return Ok(ent.start);
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

    fn add_instr_optimize(&mut self, code: Instr) -> Option<XT> {
        if self.optimize <= 0 {
            return None;
        }

        if let Instr::DoCol(col_xt) = code {
            let code_addr = col_xt.0 as usize;

            if code_addr >= self.code.len() {
                // can't look at the code, so we can't inline...
                return None;
            }

            // see if we can inline
            let mut code_to_inline : Vec<Instr> = Vec::new();

            for instr in &self.code[code_addr..] {
                match instr {
                    Instr::Unnest => {
                        break
                    },

                    Instr::Nop => {
                        /* we can omit this one */
                        continue;
                    },

                    // Instructions that we can 
                    Instr::Bye
                       | Instr::Push(_)
                       | Instr::Drop
                       | Instr::Pick
                       | Instr::Roll
                       | Instr::Rot
                       | Instr::Dup
                       | Instr::Swap 
                       | Instr::Over 
                       | Instr::BinaryOp(_)
                       | Instr::UnaryOp(_)
                       | Instr::Error(_)
                       | Instr::Execute
                       | Instr::Func(_)
                       | Instr::DoCol(_)
                       | Instr::Refill => {
                            code_to_inline.push(*instr);
                    },

                    // instructions that we won't inline at the moment
                    //
                    // If the word (called by DoCol) has any of these, don't inline...
                    Instr::Empty                // should not encounter this...
                        | Instr::Exit           // need to be careful here and consider effects...

                        | Instr::Branch(_)      // need to be careful about branching and study inlining
                        | Instr::BranchOnZero(_) 

                        | Instr::ControlIndexPush(_)   // avoid loops for now
                        | Instr::ControlIndexDrop(_) 
                        | Instr::ControlIteration{..} 
                        | Instr::ControlIndexPeek(_) 

                        | Instr::Defer(_)              // Defer and Jump can be changed dynamically and can't be
                        | Instr::Jump(_)               // inlined during initial compilation.

                        | Instr::ReturnPush            // Return* instructions should be inlineable, but 
                        | Instr::ReturnPop             // need to ensure that they're well behaved!
                        | Instr::ReturnCopy => {
                            return None
                    }
                }
            }

            let xt = self.mark_code();

            // arbitrary limit for now...
            let inline_limit = 3;
            if code_to_inline.len() > inline_limit {
                return None;
            }

            for instr in &code_to_inline {
                self.add_instr(*instr);
            }

            return Some(xt);
        }

        return None;
    }

    pub fn add_instr(&mut self, code: Instr) -> XT {
        let ind = self.code.len();

        if ind >= XT::MAX as usize {
            // XXX: handle with panic?
            panic!("cell at maximum dictionary size");
        }

        if let Some(xt) = self.add_instr_optimize(code) {
            return xt;
        }

        // fallback to a straightforward approach
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

    pub fn bytes_at_mut(&mut self, st: ST) -> Result<&mut [u8],ForthError> {
        match st {
            ST::Allocated(val) => {
                let len = (val&0xff) as usize;
                let off = (val >> 8) as usize;

                if off >= self.strings.len() {
                    return Err(ForthError::InvalidString(st));
                }

                let ind0 = off;
                let ind1 = off + len;

                if ind1 > self.strings.len() {
                    return Err(ForthError::InvalidString(st));
                }

                Ok(&mut self.strings[ind0..ind1])
            },
            ST::PadSpace(loc) => {
                let i0 = loc.off as usize;
                let i1 = (loc.off + loc.len) as usize;

                if i0 >= self.pad.len() || i1 > self.pad.len() {
                    return Err(ForthError::InvalidString(st));
                }

                Ok(&mut self.pad[i0..i1])
            },
            ST::WordSpace(loc) => {
                let i0 = loc.off as usize;
                let i1 = (loc.off + loc.len) as usize;

                if i0 >= self.word.len() || i1 > self.word.len() {
                    return Err(ForthError::InvalidString(st));
                }

                Ok(&mut self.word[i0..i1])
            },
            ST::PicSpace(loc) => {
                let i0 = loc.off as usize;
                let i1 = (loc.off + loc.len) as usize;

                if i0 >= self.word.len() || i1 > self.word.len() {
                    return Err(ForthError::InvalidString(st));
                }

                Ok(&mut self.pic[i0..i1])
            },
            ST::InputSpace(_) => {
                Err(ForthError::StringIsReadonly)
            },
        }
    }

    pub fn bytes_at(&self, st: ST) -> Result<&[u8],ForthError> {
        match st {
            ST::Allocated(val) => {
                let len = (val&0xff) as usize;
                let off = (val >> 8) as usize;

                if off >= self.strings.len() {
                    return Err(ForthError::InvalidString(st));
                }

                let ind0 = off;
                let ind1 = off + len;

                if ind1 > self.strings.len() {
                    return Err(ForthError::InvalidString(st));
                }

                Ok(&self.strings[ind0..ind1])
            },
            ST::PadSpace(loc) => {
                let i0 = loc.off as usize;
                let i1 = (loc.off + loc.len) as usize;

                if i0 >= self.pad.len() || i1 > self.pad.len() {
                    return Err(ForthError::InvalidString(st));
                }

                Ok(&self.pad[i0..i1])
            },
            ST::WordSpace(loc) => {
                let i0 = loc.off as usize;
                let i1 = (loc.off + loc.len) as usize;

                if i0 >= self.word.len() || i1 > self.word.len() {
                    return Err(ForthError::InvalidString(st));
                }

                Ok(&self.word[i0..i1])
            },
            ST::InputSpace(loc) => {
                let i0 = loc.off as usize;
                let i1 = (loc.off + loc.len) as usize;

                if i0 > self.input.len() || i1 > self.input.len() {
                    return Err(ForthError::InvalidString(st));
                }

                Ok(&self.input[i0..i1].as_bytes())
            },
            ST::PicSpace(loc) => {
                let i0 = loc.off as usize;
                let i1 = (loc.off + loc.len) as usize;

                if i0 >= self.word.len() || i1 > self.word.len() {
                    return Err(ForthError::InvalidString(st));
                }

                Ok(&self.pic[i0..i1])
            },
        }
    }

    pub fn maybe_counted_string_at(&self, st: ST) -> Result<&str, ForthError> {
        let b = self.bytes_at(st)?;

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
        let b = self.bytes_at(st)?;
        return std::str::from_utf8(b).map_err(|_| ForthError::InvalidString(st));
    }

    pub fn string_at(&self, st: ST) -> &str {
        self.maybe_string_at(st).unwrap()
    }

    pub fn push(&mut self, w: Cell) -> Result<(), ForthError> {
        self.dstack.push(w);
        Ok(())
    }

    pub fn push_uint(&mut self, v: u32) -> Result<(), ForthError> {
        if v > Cell::UINT_MAX {
            return Err(ForthError::NumberOutOfRange);
        }

        self.push(Cell(v))?;
        Ok(())
    }

    pub fn push_int(&mut self, v: i32) -> Result<(), ForthError> {
        self.push(Cell::int(v))
    }

    pub fn push_str(&mut self, st: ST) -> Result<(), ForthError> {
        self.push(st.to_cell())
    }

    fn push_addr(&mut self, addr: Addr) -> Result<(),ForthError> {
        match addr {
            Addr::Var(a_addr) => self.push_var_addr(a_addr),
            Addr::Char(c_addr) => self.push_str(c_addr),
        }
    }

    fn push_var_addr(&mut self, addr: VarAddr) -> Result<(),ForthError> {
        self.push(addr.to_cell())
    }

    fn drop(&mut self) -> Result<(), ForthError> {
        if let Some(_) = self.dstack.pop() {
            Ok(())
        } else {
            Err(ForthError::StackUnderflow)
        }
    }

    fn pick(&mut self, dist: usize) -> Result<(), ForthError> {
        let len = self.dstack.len();
        if dist >= len {
            return Err(ForthError::StackUnderflow);
        }

        let val = self.dstack[len-1-dist];
        self.dstack.push(val);
        Ok(())
    }

    fn roll(&mut self, dist: usize) -> Result<(), ForthError> {
        let len = self.dstack.len();
        if dist >= len {
            return Err(ForthError::StackUnderflow);
        }

        let ind = len - 1 - dist;
        let val = self.dstack.remove(ind);
        self.dstack.push(val);
        Ok(())
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

    fn data_to_aux(&mut self) -> Result<(), ForthError> {
        let w = self.dstack.pop().ok_or(ForthError::StackUnderflow)?;
        self.aux_stack.push(w);
        Ok(())
    }

    fn aux_to_data(&mut self) -> Result<(), ForthError> {
        let w = self.aux_stack.pop().ok_or(ForthError::StackUnderflow)?;
        self.dstack.push(w);
        Ok(())
    }

    fn aux_copy_to_data(&mut self) -> Result<(), ForthError> {
        let w = self.aux_stack.last().ok_or(ForthError::StackUnderflow)?;
        self.dstack.push(*w);
        Ok(())
    }

    fn pop_dbl_uint(&mut self) -> Result<u64, ForthError> {
        let hi = self.pop_uint()?;
        let lo = self.pop_uint()?;

        let d = ((hi as u64) << 31) | (lo as u64);
        return Ok(d);
    }

    fn pop_dbl_int(&mut self) -> Result<i64, ForthError> {
        let hi = self.pop_int()?;
        let lo = self.pop_int()?;

        let d = (((hi as u64) << 32) | (lo as u64)) as i64;
        return Ok(d);
    }

    fn floored_double_div_single(numer: i64, denom: i32) -> Result<(i32,i32), ForthError> {
        if denom == 0 {
            return Err(ForthError::DivisionByZero);
        }

        let div : i64 = denom as i64;
        let quot0 : i64 = numer.wrapping_div(div);
        let rem0 : i64 = numer - (quot0 * div);

        let (quot,rem) = if rem0 == 0 || ((numer < 0) == (div < 0)) {
            (quot0,rem0)
        } else {
            (quot0-1, rem0 + div)
        };

        if quot > (Cell::INT_MAX as i64) || quot < (Cell::INT_MIN as i64) {
            return Err(ForthError::NumberOutOfRange);
        }

        Ok((quot as i32, rem as i32))
    }

    fn double_div_single(numer: i64, denom: i32) -> Result<(i32,i32), ForthError> {
        let div : i64 = denom as i64;
        if div == 0 {
            return Err(ForthError::DivisionByZero);
        }

        let quot : i64 = numer.wrapping_div(div);

        if quot > (Cell::INT_MAX as i64) || quot < (Cell::INT_MIN as i64) {
            return Err(ForthError::NumberOutOfRange);
        }

        let rem : i64 = numer - (quot * div);
        Ok((quot as i32, rem as i32))
    }

    fn builtin_star_slash_mod(&mut self) -> Result<(), ForthError> {
        let div = self.pop_int()?;
        let a = self.pop_int()?;
        let b = self.pop_int()?;

        let mult : i64 = (a as i64).wrapping_mul(b as i64);
        let (quot,rem) = ToyForth::double_div_single(mult, div)?;

        self.push_int(rem as i32)?;
        self.push_int(quot as i32)?;
        Ok(())
    }

    fn builtin_fm_slash_mod(&mut self) -> Result<(), ForthError> {
        let denom = self.pop_int()?;
        let numer = self.pop_dbl_int()?;

        let (quot,rem) = ToyForth::floored_double_div_single(numer, denom)?;
        self.push_int(rem as i32)?;
        self.push_int(quot as i32)?;
        Ok(())
    }

    fn builtin_sm_slash_rem(&mut self) -> Result<(), ForthError> {
        let denom = self.pop_int()?;
        let numer = self.pop_dbl_int()?;

        let (quot,rem) = ToyForth::double_div_single(numer, denom)?;
        self.push_int(rem as i32)?;
        self.push_int(quot as i32)?;
        Ok(())
    }

    fn builtin_um_slash_mod(&mut self) -> Result<(), ForthError> {
        let divisor  = self.pop_uint()?;
        if divisor == 0 {
            return Err(ForthError::DivisionByZero);
        }

        let dividend = self.pop_dbl_uint()?;

        let quot : u64 = dividend / (divisor as u64);
        if quot > (Cell::UINT_MAX as u64) {
            return Err(ForthError::NumberOutOfRange);
        }

        let rem : u64 = dividend - (divisor as u64)*quot;

        self.push_uint(rem as u32)?;
        self.push_uint(quot as u32)?;
        Ok(())
    }

    fn offset_addr(&self, addr: Addr, off: i32) -> Result<Addr, ForthError> {
        match addr {
            Addr::Var(a_addr) => {
                let pos = (a_addr.0 as i64) + (off as i64);
                // eprintln!("addr = {:?}, off = {}, pos = {}, len(vars) = {}",
                //      addr, off, pos, self.vars.len());

                // 
                if pos < 0 || (pos as usize) > self.vars.len() {
                    return Err(ForthError::InvalidAddressAndOffset(addr, off));
                }

                Ok(Addr::Var(VarAddr(pos as u32)))
            },
            Addr::Char(caddr) => {
                if off < 0 || off > (u8::MAX as i32) {
                    return Err(ForthError::InvalidAddressAndOffset(addr, off));
                }

                Ok(Addr::Char(caddr.offset(off as u8)))
            },
        }
    }

    fn builtin_addr_plus(&mut self) -> Result<(), ForthError> {
        let off = self.pop_int()?;
        let addr = self.pop_addr()?;

        let new_addr = self.offset_addr(addr,off)?;
        self.push_addr(new_addr)?;
        Ok(())
    }

    fn builtin_addr_minus(&mut self) -> Result<(), ForthError> {
        let off = self.pop_int()?;
        let addr = self.pop_addr()?;

        let new_addr = self.offset_addr(addr,-off)?;
        self.push_addr(new_addr)?;
        Ok(())
    }

    fn builtin_defer(&mut self) -> Result<(), ForthError> {
        let st = self.next_word(' ' as u8, u8::MAX as usize)?;
        // FIXME: completely unnecessary copy here...
        let s = self.maybe_string_at(st)?.to_string();

        self.add_word(&s, &[ Instr::Defer(self.invalid_deferred_xt), Instr::Unnest ], DictEntry::DEFERRED)?;
        Ok(())
    }

    fn builtin_defer_bang(&mut self) -> Result<(), ForthError> {
        let deferred_xt = self.pop_xt()?;
        let xt = self.pop_xt()?;

        let code_ind = deferred_xt.0 as usize;
        if code_ind >= self.code.len() {
            return Err(ForthError::FunctionSpaceOverflow);
        }

        match self.code[code_ind] {
            Instr::Defer(_) => {
                self.code[code_ind] = Instr::Defer(xt);
            },
            _ => {
                return Err(ForthError::NotDeferredFunction);
            }
        }

        Ok(())
    }

    fn builtin_defer_at(&mut self) -> Result<(), ForthError> {
        let deferred_xt = self.pop_xt()?;

        let code_ind = deferred_xt.0 as usize;
        if code_ind >= self.code.len() {
            return Err(ForthError::FunctionSpaceOverflow);
        }

        match self.code[code_ind] {
            Instr::Defer(xt) => {
                self.push(xt.to_cell())?;
            },
            _ => {
                return Err(ForthError::NotDeferredFunction);
            }
        }

        Ok(())
    }

    fn builtin_action_of(&mut self) -> Result<(), ForthError> {
        let st = self.next_word(' ' as u8, u8::MAX as usize)?;
        let s = self.maybe_string_at(st)?;

        let entry = self.lookup_dict_entry(s)?;

        if !entry.is_deferred() {
            return Err(ForthError::NotDeferredFunction);
        }

        let deferred_xt = entry.start;

        if self.compiling() {
            let defer_at_xt = self.lookup_word("DEFER@")?;
            self.add_instr(Instr::Push(deferred_xt.to_cell()));
            self.add_instr(Instr::DoCol(defer_at_xt));
        } else {
            self.push(deferred_xt.to_cell())?;
            self.builtin_defer_at()?;
        }

        Ok(())
    }

    fn builtin_is(&mut self) -> Result<(), ForthError> {
        let st = self.next_word(' ' as u8, u8::MAX as usize)?;
        let s = self.maybe_string_at(st)?;

        let entry = self.lookup_dict_entry(s)?;

        if !entry.is_deferred() {
            return Err(ForthError::NotDeferredFunction);
        }

        let deferred_xt = entry.start;

        if self.compiling() {
            let defer_bang_xt = self.lookup_word("DEFER!")?;
            self.add_instr(Instr::Push(deferred_xt.to_cell()));
            self.add_instr(Instr::DoCol(defer_bang_xt));
        } else {
            self.push(deferred_xt.to_cell())?;
            self.builtin_defer_bang()?;
        }

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

    fn new_var(&mut self, initial_value: Cell) -> Result<VarAddr, ForthError> {
        let addr = self.vars.len();

        if addr > (VarAddr::MAX as usize) {
            return Err(ForthError::VarSpaceOverflow);
        }

        self.vars.push(initial_value);
        Ok(VarAddr(addr as u32))
    }

    fn get_var_at(&self, addr: VarAddr) -> Result<Cell, ForthError> {
        if (addr.0 & VarAddr::BUILTIN) != 0 {
            match addr {
                ToyForth::ADDR_IN => { return Ok(Cell::int(self.input_off as i32)) },
                ToyForth::ADDR_OPTIMIZE => { return Ok(Cell::int(self.optimize)) },
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

    fn set_var_at(&mut self, addr: VarAddr, value: Cell) -> Result<(), ForthError> {
        if (addr.0 & VarAddr::BUILTIN) != 0 {
            match addr {
                ToyForth::ADDR_IN => { return Err(ForthError::ReadOnlyAddress(Addr::Var(addr))); },
                ToyForth::ADDR_OPTIMIZE => {
                    let val = value.to_int().ok_or(ForthError::ExpectedInteger(value))?;
                    self.optimize = val;
                },
                _ => { return Err(ForthError::InvalidAddress(addr)) }
            }

            return Ok(());
        }

        let ind = addr.0 as usize;

        if ind >= self.vars.len() {
            return Err(ForthError::InvalidAddress(addr));
        }

        self.vars[ind] = value;

        Ok(())
    }

    fn get_char_at(&self, st: ST) -> Result<u8, ForthError> {
        let b = self.bytes_at(st)?;
        if b.len() == 0 {
            return Err(ForthError::InvalidEmptyString);
        }

        Ok(b[0])
    }

    fn set_char_at(&mut self, st: ST, value: u8) -> Result<(), ForthError> {
        let b = self.bytes_at_mut(st)?;
        if b.len() == 0 {
            return Err(ForthError::InvalidEmptyString);
        }

        b[0] = value;
        Ok(())
    }

    fn get_addr_value(&self, addr: Addr) -> Result<Cell, ForthError> {
        match addr {
            Addr::Var(a_addr) => {
                self.get_var_at(a_addr)
            },
            Addr::Char(c_addr) => {
                let ch = self.get_char_at(c_addr)?;
                Ok(Cell::int(ch as i32))
            },
        }
    }

    fn set_addr_value(&mut self, addr: Addr, value: Cell) -> Result<(), ForthError> {
        match addr {
            Addr::Var(a_addr) => {
                self.set_var_at(a_addr, value)?;
            },
            Addr::Char(c_addr) => {
                let ch = value.to_char()?;
                self.set_char_at(c_addr, ch)?;
            },
        };

        Ok(())
    }

    fn builtin_var_get(&mut self) -> Result<(), ForthError> {
        let addr = self.pop_addr()?;
        let w = self.get_addr_value(addr)?;
        self.push(w)?;
        Ok(())
    }

    fn builtin_var_set(&mut self) -> Result<(), ForthError> {
        let addr = self.pop_addr()?;
        let val = self.pop().ok_or(ForthError::StackUnderflow)?;
        self.set_addr_value(addr, val)?;
        Ok(())
    }

    fn unary_op(&mut self, op: UnaryOp) -> Result<(),ForthError> {
        let a = self.pop_int()?;
        match op {
            UnaryOp::Negate => { self.push_int(-a)?; Ok(()) },
            UnaryOp::Invert => {
                let inverted = !(a as u32);
                self.push(Cell(inverted & Cell::INT_MASK))?;
                Ok(())
            },
        }
    }

    fn binary_op(&mut self, op: BinOp) -> Result<(),ForthError> {
        // there's probably a more efficient way to do this...
        let bw = self.pop().ok_or(ForthError::StackUnderflow)?;
        let aw = self.pop().ok_or(ForthError::StackUnderflow)?;

        match op {
            BinOp::Equal    => { self.push(Cell::bool(aw.0 == bw.0))?; return Ok(()); },
            BinOp::NotEqual => { self.push(Cell::bool(aw.0 != bw.0))?; return Ok(()); },

            BinOp::UnsignedGreater => {
                let gt = match (aw.kind(), bw.kind()) {
                    (CellKind::Int(a), CellKind::Int(b)) => {
                        Cell::bool( (a as u32) > (b as u32) )
                    },
                    (CellKind::VarAddr(VarAddr(a)), CellKind::VarAddr(VarAddr(b))) => {
                        Cell::bool( (a as u32) > (b as u32) )
                    },
                    _ => {
                        // XXX: need a better error!
                        return Err(ForthError::InvalidArgument(aw));
                    }
                };

                self.push(gt)?;
                return Ok(());
            },
            BinOp::UnsignedLess => {
                let lt = match (aw.kind(), bw.kind()) {
                    (CellKind::Int(a), CellKind::Int(b)) => {
                        Cell::bool( (a as u32) < (b as u32) )
                    },
                    (CellKind::VarAddr(VarAddr(a)), CellKind::VarAddr(VarAddr(b))) => {
                        Cell::bool( (a as u32) < (b as u32) )
                    },
                    _ => {
                        // XXX: need a better error!
                        return Err(ForthError::InvalidArgument(aw));
                    }
                };

                self.push(lt)?;
                return Ok(());
            },

            // otherwise handle below
            _ => {},
        }

        let b = bw.to_int().ok_or(ForthError::ExpectedInteger(bw))?;
        let a = aw.to_int().ok_or(ForthError::ExpectedInteger(aw))?;

        // eprintln!("op = {:?}, a={}, b={}", op, a,b);
        let result: Cell = match op {
            BinOp::Plus  => { Cell::int(a+b) },
            BinOp::Minus => { Cell::int(a-b) },
            BinOp::Star  => { Cell::int(a.wrapping_mul(b)) },
            BinOp::Slash => {
                if b == 0 {
                    return Err(ForthError::DivisionByZero);
                }

                Cell::int(a.wrapping_div(b))
            },

            BinOp::MStar => {
                let m = (a as i64).wrapping_mul(b as i64);
                let um = m as u64;

                let cell_mask = Cell::INT_MASK as u64;

                let lo : u32 = (um & cell_mask) as u32;
                let hi : u32 = (um >> Cell::INT_BITS) as u32;

                self.push(Cell::int(lo as i32))?;
                self.push(Cell::int(hi as i32))?;
                return Ok(());
            },

            BinOp::UMStar => {
                let ua = (a as u32) & Cell::INT_MASK;
                let ub = (b as u32) & Cell::INT_MASK;
                let um = (ua as u64).wrapping_mul(ub as u64);
                let cell_mask = Cell::INT_MASK as u64;

                let lo : u32 = (um & cell_mask) as u32;
                let hi : u32 = (um >> Cell::INT_BITS) as u32;

                eprintln!("a = {}, b = {}, um = {}, lo = {}, hi = {}",
                      (ua as u64), (ub as u64), um, lo, hi);
                self.push(Cell::int(lo as i32))?;
                self.push(Cell::int(hi as i32))?;
                return Ok(());
            },

            BinOp::And      => { Cell::int(((a as u32) & (b as u32)) as i32) },
            BinOp::Or       => { Cell::int(((a as u32) | (b as u32)) as i32) },
            BinOp::Xor      => { Cell::int(((a as u32) ^ (b as u32)) as i32) },

            BinOp::Greater  => { Cell::bool(a > b ) },
            BinOp::Less     => { Cell::bool(a < b ) },

            BinOp::LeftShift  => {
                // TODO: check b for range
                Cell( ((a as u32) << (b as u32)) & Cell::INT_MASK )
            },
            BinOp::RightShift => {
                // TODO: check b for range
                let ub = b as u32;

                // ua requires some care.  -1 is all-bits-set, and has 31 bits in the native type.
                // 
                // When naively cast to u32, it has 32 bits, and the MSB is set.
                //
                // This creates a problem for right shift, because that extra bit will be shifted
                // downward, in effect making the RSHIFT shift one bit less when the operand has
                // the MSB set (ie: is negative).
                //
                // eg: `-1 1 RSHIFT` will yield the first 31 bits set, which is -1 in the native
                // type.
                //
                // To avoid this, we apply the integer mask to zero out the u32 MSB.
                //
                let ua = (a as u32) & Cell::INT_MASK;
                Cell( (ua >> ub) & Cell::INT_MASK )
            },

            BinOp::Equal | BinOp::NotEqual | BinOp::UnsignedGreater | BinOp::UnsignedLess => {
                /* handled previously */ panic!("should not reach");
            },
        };

        self.push(result)?;

        return Ok(());
    }

    fn builtin_find(&mut self) -> Result<(), ForthError> {
        let st = self.pop_str()?;
        let s = self.maybe_counted_string_at(st)?;

        match self.lookup_dict_entry(s) {
            Ok(entry) => {
                self.push(Cell::from_xt(entry.start))?;
                let wh = if (entry.flags & DictEntry::IMMEDIATE) != 0 { 1 } else { -1 };
                self.push(Cell::int(wh))?;
                Ok(())
            },
            Err(ForthError::StringNotFound) => {
                self.push(st.to_cell())?;
                self.push(Cell::int(0))?;
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
                self.push(Cell::from_xt(entry.start))?;
                let wh = if (entry.flags & DictEntry::IMMEDIATE) != 0 { 1 } else { -1 };
                self.push(Cell::int(wh))?;
                Ok(())
            },
            Err(ForthError::StringNotFound) => {
                self.push(st.to_cell())?;
                self.push_int(len)?;
                self.push(Cell::int(0))?;
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
            return Err(ForthError::NumberOutOfRange);
        }

        let st  = self.pop_str()?;
        // eprintln!("st = {:?}",st);
        let v0 = self.pop_int()?;
        // eprintln!("v0 = {:?}",v0);

        if v0 < 0 {
            return Err(ForthError::NumberOutOfRange);
        }

        let bytes = self.bytes_at(st)?;
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

        // TODO: check for cell overflow!
        self.push_int(val as i32)?;
        self.push(st.offset(consumed as u8).to_cell())?;
        self.push_int(consumed as i32)?;

        Ok(())
    }

    fn lookup_bye(&self) -> Result<XT,ForthError> {
        // BYE always at XT(0).
        Ok(XT(0))
    }

    fn ret_push(&mut self, xt: XT) -> Result<(),ForthError> {
        self.rstack.push(xt);
        Ok(())
    }

    fn ret_push_bye(&mut self) -> Result<(),ForthError> {
        let bye_xt = self.lookup_bye()?;
        self.rstack.push(bye_xt);
        Ok(())
    }

    fn builtin_recurse(&mut self) -> Result<(),ForthError> {
        self.check_compiling()?;

        let cxt = self.get_var_at(ToyForth::ADDR_SLASH_CXT)?;
        let xt = cxt.to_xt().ok_or(ForthError::ExpectedXT(cxt))?; // XXX: need better error
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

        self.push(xt.to_cell())?;
        Ok(())
    }

    fn builtin_add_instr(&mut self) -> Result<(),ForthError> {
        self.check_compiling()?;

        let xt = self.pop_xt()?;
        self.add_instr(Instr::DoCol(xt));
        Ok(())
    }

    fn builtin_postpone(&mut self) -> Result<(),ForthError> {
        self.check_compiling()?;

        let st = self.next_word(' ' as u8, u8::MAX as usize)?;

        let s = self.maybe_string_at(st)?;
        let ent = self.lookup_dict_entry(s)?;

        if ent.is_immediate() {
            self.add_instr(Instr::DoCol(ent.start));
        } else {
            self.add_instr(Instr::Push(ent.start.to_cell()));
            self.add_instr(Instr::DoCol(self.compile_comma_xt));
        }

        Ok(())
    }

    fn builtin_brak_tick(&mut self) -> Result<(),ForthError> {
        self.check_compiling()?;

        let st = self.next_word(' ' as u8, u8::MAX as usize)?;

        let s = self.maybe_string_at(st)?;
        let xt = self.lookup_word(s)?;

        self.add_instr(Instr::Push(xt.to_cell()));
        Ok(())
    }

    fn builtin_execute(&mut self) -> Result<(),ForthError> {
        if self.compiling() {
            self.add_instr(Instr::Execute);
        } else {
            let xt = self.pop_xt()?;
            /*
            self.ret_push_bye()?;
            self.exec_at(xt)?;
            */

            self.ret_push(XT(self.pc+1))?;
            self.pc = xt.0;
        }

        Ok(())
    }

    fn pop_char(&mut self) -> Result<u8, ForthError> {
        let w = self.pop().ok_or(ForthError::StackUnderflow)?;

        if let CellKind::Int(v) = w.kind() {
            if v > 0 && v < 256 {
                return Ok(v as u8);
            }

            return Err(ForthError::InvalidChar(v));
        } else {
            return Err(ForthError::ExpectedInteger(w));
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

    fn builtin_allot(&mut self) -> Result<(), ForthError> {
        let n = self.pop_int()?;

        if n < 0 {
            return Err(ForthError::NumberOutOfRange);
        }

        self.vars.resize(self.vars.len() + (n as usize), Cell(0));
        Ok(())
    }

    fn builtin_cell_plus(&mut self) -> Result<(), ForthError> {
        let addr = self.pop_var_addr()?;

        if (addr.0 as usize) + 1 > self.vars.len() {
            return Err(ForthError::VarSpaceOverflow);
        }

        self.push(VarAddr(addr.0+1).to_cell())?;
        Ok(())
    }

    fn builtin_comma(&mut self) -> Result<(), ForthError> {
        let w = self.pop().ok_or(ForthError::StackUnderflow)?;

        self.vars.push(w);
        Ok(())
    }

    fn free_field_number(mut num: i64, base: i64, out: &mut [u8], min_width: usize, trailing: bool) -> &[u8] {
        let mut off = out.len();

        let neg = num < 0;

        if neg {
            num = -num;
        }

        if trailing {
            off -= 1;
            out[off] = ' ' as u8;
        }

        loop {
            let dig = (num % base) as u8;

            off -= 1;
            out[off] = if dig <= 9 {
                ('0' as u8) + dig
            } else {
                ('A' as u8) + (dig-10)
            };

            num /= base;
            if num == 0 {
                break
            }
        }

        if neg {
            off -= 1;
            out[off] = '-' as u8;
        }

        let mut width = out.len() - off;
        while min_width > width {
            off -= 1;
            width += 1;
            out[off] = ' ' as u8;
        }

        &out[off..]
    }

    fn free_field_display<'b>(&self, num: i64, out: &'b mut [u8], min_width: usize, trailing: bool) -> Result<&'b [u8], ForthError> {
        let base_var = self.get_var_at(ToyForth::ADDR_BASE)?;
        let base_signed = base_var.to_int().ok_or(ForthError::InvalidNumberBase)?;

        if base_signed < 0 || base_signed > 36 {
            return Err(ForthError::InvalidNumberBase);
        }
        let base = base_signed as i64; // 10; // FIXME!

        Ok(ToyForth::free_field_number(num, base, out, min_width, trailing))
    }

    fn builtin_dot_dot(&mut self) -> Result<(), ForthError> {
        let w = self.pop().ok_or(ForthError::StackUnderflow)?;

        if let Some(out) = &self.out_stream {
            let mut wr = out.borrow_mut();

            if let CellKind::Int(n) = w.kind() {
                let mut buf = [0 as u8; 64];
                wr.write(self.free_field_display(n as i64, &mut buf, 0, false)?)?;
                // wr.write(&buf[..n])?;
                // write!(wr, "{}", n)?;
            } else {
                write!(wr, "{}", w)?;
            }
            wr.flush()?;
        }

        Ok(())
    }

    fn builtin_u_dot(&mut self) -> Result<(), ForthError> {
        let u = self.pop_uint()?;

        if let Some(out) = &self.out_stream {
            let mut wr = out.borrow_mut();

            let mut buf = [0 as u8; 256];
            wr.write(self.free_field_display(u as i64, &mut buf, 0, true)?)?;

            // write!(wr, "{} ", u)?;
            wr.flush()?;
        }

        Ok(())
    }

    fn builtin_u_dot_r(&mut self) -> Result<(), ForthError> {
        let n = self.pop_int()?;
        let u = self.pop_uint()?;

        if n < 0 || n > 255 {
            return Err(ForthError::NumberOutOfRange);
        }

        if let Some(out) = &self.out_stream {
            let mut wr = out.borrow_mut();

            let mut buf = [0 as u8; 256];
            wr.write(self.free_field_display(u as i64, &mut buf, n as usize, false)?)?;

            // write!(wr, "{} ", u)?;
            wr.flush()?;
        }

        Ok(())
    }

    fn builtin_pic(&mut self) -> Result<(), ForthError> {
        self.push_str(ST::pic_space(0,std::cmp::min(u8::MAX as usize, self.pic.len()) as u8))?;
        Ok(())
    }

    fn builtin_callot(&mut self) -> Result<(), ForthError> {
        let n = self.pop_int()?;

        // need to handle larger strings at some point
        if n < 0 {
            return Err(ForthError::NumberOutOfRange);
        }

        if n > u8::MAX as i32 {
            return Err(ForthError::StringTooLong);
        }

        let off = self.strings.len();
        if off > u32::MAX as usize {
            return Err(ForthError::StringOffsetTooLarge);
        }

        self.strings.resize(self.strings.len() + (n as usize), 0);
        self.push_str(ST::allocated_space(off as u32, n as u8))?;

        Ok(())
    }

    fn builtin_input_len(&mut self) -> Result<(), ForthError> {
        // TODO: check for overflow!
        self.push_int(self.input.len() as i32)?;
        Ok(())
    }

    fn builtin_pad(&mut self) -> Result<(), ForthError> {
        self.push_str(ST::pad_space(0,std::cmp::min(u8::MAX as usize, self.pad.len()) as u8))?;
        Ok(())
    }

    fn builtin_cshrink(&mut self) -> Result<(), ForthError> {
        let len = self.pop_int()?;
        let st = self.pop_str()?;

        if len < 0 {
            return Err(ForthError::NumberOutOfRange);
        }

        let new_len = std::cmp::min(st.len(), len as u32) as u8;

        let new_st = match st {
            ST::Allocated(_) => {
                ST::allocated_space(st.addr(), new_len)
            },
            ST::PadSpace(ScratchLoc{off,..}) => {
                ST::pad_space(off, new_len)
            },
            ST::WordSpace(ScratchLoc{off,..}) => {
                ST::word_space(off, new_len)
            },
            ST::InputSpace(ScratchLoc{off,..}) => {
                ST::input_space(off, new_len)
            },
            ST::PicSpace(ScratchLoc{off,..}) => {
                ST::pic_space(off, new_len)
            },
        };

        self.push_str(new_st)?;
        Ok(())
    }

    fn builtin_clength(&mut self) -> Result<(), ForthError> {
        let st = self.pop_str()?;
        self.push_int(st.len() as i32)?;
        Ok(())
    }

    fn builtin_create(&mut self) -> Result<(), ForthError> {
        self.push_int(' ' as i32)?;
        self.builtin_parse()?;

        let len = self.pop_int()?;
        let st = self.pop_str()?;
        if len == 0 {
            return Err(ForthError::InvalidEmptyString);
        }

        let addr = self.here();

        // FIXME: completely unnecessary copy here...
        let s = self.maybe_string_at(st)?.to_string();
        self.add_word(&s, &[ Instr::Push(addr.to_cell()), Instr::Unnest ], 0)?;

        Ok(())
    }

    fn builtin_runtime_does(&mut self) -> Result<(), ForthError> {
        let jump_xt = self.pop_xt()?;

        // look up last definition
        let entry = self.dict.last().ok_or(ForthError::DictEmpty)?;

        // find Unnest or Jump at the end, and change Unnest to Jump(jump_xt),
        //     or Jump to Jump(jump_xt)
        //
        // TODO: change dictionary entries to have the number of instructions
        //       to make this safer
        let i0 = entry.start.0 as usize;
        for i in i0..self.code.len() {
            match self.code[i] {
                Instr::Unnest | Instr::Jump(_) => {
                    self.code[i] = Instr::Jump(jump_xt);
                    break
                },
                _ => {},
            };
        }

        Ok(())
    }

    fn builtin_does(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;  // see gforth's interpration semantics?

        // add dummy push and call to runtime DOES>
        let xt = self.mark_code();
        self.add_instr(Instr::Push(Cell(0)));
        self.add_instr(Instr::Func(self.runtime_does_func));
        self.add_instr(Instr::Unnest);

        // now fix up push with XT after the call to runtime DOES>
        let after_xt = self.mark_code();
        self.code[xt.0 as usize] = Instr::Push(after_xt.to_cell());

        Ok(())
    }

    pub fn lookup_var_addr_by_xt(&self, xt: XT) -> Result<VarAddr, ForthError> {
        let addr = xt.0 as usize;
        if addr >= self.code.len() {
            return Err(ForthError::InvalidPC(xt.0));
        }

        if let Instr::Push(w) = self.code[addr] {
            let addr = w.to_addr().ok_or(ForthError::InvalidCell(xt))?;
            return Ok(addr);
        } else {
            return Err(ForthError::InvalidCell(xt));
        }
    }

    fn builtin_body(&mut self) -> Result<(), ForthError> {
        let xt = self.pop_xt()?;

        let addr = self.lookup_var_addr_by_xt(xt)?;
        self.push(addr.to_cell())?;
        Ok(())
    }

    fn builtin_empty_return(&mut self) -> Result<(), ForthError> {
        self.rstack.clear();
        Ok(())
    }

    fn builtin_clear_compile_state(&mut self) -> Result<(), ForthError> {
        self.set_var_at(ToyForth::ADDR_SLASH_CDEF, Cell(0))?;
        self.set_var_at(ToyForth::ADDR_SLASH_CXT, Cell(0))?;
        self.set_var_at(ToyForth::ADDR_STATE, Cell::int(0))?;
        Ok(())
    }

    fn builtin_evaluate(&mut self) -> Result<(), ForthError> {
        /*
        let len   = self.pop_uint()?;
        let caddr0 = self.pop_str()?;

        if len > u8::MAX as u32 {
        }

        let caddr = if caddr0.len() <= len {
            caddr0
        } else {
            if len > (u8::MAX as u32) {
                return Err(ForthError::StringTooLong);
            }
            caddr.substr(0, len as u8)
        };

        self.source = caddr;
        self.

        Ok(())
        */
        Err(ForthError::NotImplemented)
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
        self.add_word(&s, &[ Instr::Push(w), Instr::Unnest ], 0)?;

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

        let addr = self.new_var(Cell(0))?;

        // FIXME: completely unnecessary copy here...
        let s = self.maybe_string_at(st)?.to_string();
        self.add_word(&s, &[ Instr::Push(addr.to_cell()), Instr::Unnest ], 0)?;

        Ok(())
    }

    fn builtin_colon(&mut self) -> Result<(), ForthError> {
        self.check_not_in_bracket()?;
        // TODO: check not defining

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
        self.set_var_at(ToyForth::ADDR_SLASH_CDEF, st.to_cell())?;

        let xt = self.mark_code();
        self.set_var_at(ToyForth::ADDR_SLASH_CXT, xt.to_cell())?;
        self.set_var_at(ToyForth::ADDR_STATE, Cell::int(1))?;

        Ok(())
    }

    fn builtin_colon_noname(&mut self) -> Result<(), ForthError> {
        self.check_not_in_bracket()?;
        self.check_not_compiling()?;
        // TODO: check not defining

        // XXX: check that STATE==0, /CDEF and /CXT are not set
        self.set_var_at(ToyForth::ADDR_SLASH_CDEF, Cell(0))?;

        let xt = self.mark_code();
        self.set_var_at(ToyForth::ADDR_SLASH_CXT, xt.to_cell())?;
        self.set_var_at(ToyForth::ADDR_STATE, Cell::int(1))?;

        Ok(())
    }

    fn builtin_semi(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        self.add_instr(Instr::Unnest);

        let cdef = self.get_var_at(ToyForth::ADDR_SLASH_CDEF)?;
        let cxt  = self.get_var_at(ToyForth::ADDR_SLASH_CXT)?;
        let xt = cxt.to_xt().ok_or(ForthError::ExpectedXT(cxt))?; // XXX: need better error

        if cdef != Cell(0) {
            let st = cdef.to_str().ok_or(ForthError::ExpectedString(cdef))?; // XXX: need better error
            let end = self.mark_code();

            self.dict.push(DictEntry{
                st: st,
                start: xt,
                end: end,
                flags: 0,
            });
        } else {
            let st = ST::null();
            let end = self.mark_code();

            self.dict.push(DictEntry{
                st: st,
                start: xt,
                end: end,
                flags: 0,
            });
            self.push(xt.to_cell())?;
        }

        self.set_var_at(ToyForth::ADDR_SLASH_CDEF, Cell(0))?;
        self.set_var_at(ToyForth::ADDR_SLASH_CXT, Cell(0))?;
        self.set_var_at(ToyForth::ADDR_STATE, Cell::int(0))?;

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
        // TODO: add some safety here
        //
        // Look through the control stack to ensure that there's a valid DO..LOOP
        //
        // We should probably keep a bit more state for this.
        self.add_instr(Instr::ControlIndexDrop(2));

        Ok(())
    }

    fn builtin_obracket(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;
        self.set_var_at(ToyForth::ADDR_SLASH_BRACKET, Cell::int(1))?;
        self.set_var_at(ToyForth::ADDR_STATE, Cell::int(0))?;
        Ok(())
    }

    fn builtin_cbracket(&mut self) -> Result<(), ForthError> {
        self.check_interpreting()?;
        self.set_var_at(ToyForth::ADDR_SLASH_BRACKET, Cell::int(0))?;
        self.set_var_at(ToyForth::ADDR_STATE, Cell::int(1))?;
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

    fn builtin_case(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;
        self.add_instr(Instr::Branch(2));
        let exit_xt = self.add_instr(Instr::Branch(0));

        self.cpush_case(exit_xt);
        Ok(())
    }

    fn builtin_of(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        let exit_xt = self.cpeek_case()?;

        self.add_instr(Instr::Over);
        self.add_instr(Instr::BinaryOp(BinOp::Equal));
        let next_xt = self.add_instr(Instr::BranchOnZero(0));
        self.add_instr(Instr::Drop);

        self.cpush_case_of(exit_xt, next_xt);
        Ok(())
    }

    fn builtin_endof(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        let (exit_xt,next_xt) = self.cpop_case_of()?;

        // branch to end
        {
            let end_xt = self.mark_code();
            let delta : i32 = ((exit_xt.0 as i64) - (end_xt.0 as i64)) as i32;
            self.add_instr(Instr::Branch(delta));
        }

        {
            let xt = self.mark_code();
            let delta : i32 = ((xt.0 as i64) - (next_xt.0 as i64)) as i32;
            self.code[next_xt.0 as usize] = Instr::BranchOnZero(delta);
        }

        Ok(())
    }

    fn builtin_endcase(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        let exit_xt = self.cpop_case()?;

        self.add_instr(Instr::Drop);

        // TODO: sweep from exit_xt to the end, and rewire all of the
        //       branches to exit_xt to be branches to the end.
        //
        //       Also eliminate exit_xt and the branch over it.

        let xt = self.mark_code();
        let delta : i32 = ((xt.0 as i64) - (exit_xt.0 as i64)) as i32;
        self.code[exit_xt.0 as usize] = Instr::Branch(delta);

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

        // self.add_instr(Instr::ControlIndexDrop(2));
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
        self.cpush_do_addr(xt, None);
        Ok(())
    }

    fn builtin_qdo(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        // loop header
        self.add_code(&[
            Instr::Over,
            Instr::Over, // TODO: 2DUP
            Instr::ControlIndexPush(2),
            Instr::BinaryOp(BinOp::Minus),
        ]);

        let branch_xt = self.add_instr(Instr::BranchOnZero(0));

        // mark loop
        let xt = self.mark_code();
        self.cpush_do_addr(xt, Some(branch_xt));

        Ok(())
    }

    fn compile_loop(&mut self, incr: bool) -> Result<(), ForthError> {
        self.check_compiling()?;

        let do_xt : XT;
        let mut leave_xts : Vec<XT> = Vec::new();

        let entry = self.cpop_entry()?;
        match entry {
            ControlEntry::DoAddr(info) => {
                do_xt = info.head;
                if let Some(qdo_xt) = info.qdo {
                    leave_xts.push(qdo_xt);
                }
            },

            ControlEntry::LeaveAddr{head:info, leave: leave_xt} => {
                do_xt = info.head;
                if let Some(qdo_xt) = info.qdo {
                    leave_xts.push(qdo_xt);
                }
                leave_xts.push(leave_xt);
            },

            _ => {
                return Err(ForthError::InvalidControlEntry(entry));
            },
        };

        // ControlIteration: ( -- 0 | 1 ) (C: n1 n2 -- n1 n3 | )
        // if n2<n1, pushes n1 and n3=n2-1 onto the control stack, pushes 0 onto the data stack
        // if n2>=1, pops n1,n2 from the control stack, pushes 1 onto the data stack
        self.add_instr(Instr::ControlIteration{incr: incr});

        // branch back to DO (after loop header)
        {
            let xt = self.mark_code();
            let delta : i32 = ((do_xt.0 as i64) - (xt.0 as i64)) as i32;
            self.add_instr(Instr::BranchOnZero(delta));
        }

        {
            let after_xt = self.add_instr(Instr::ControlIndexDrop(2));

            for xt in leave_xts {
                let delta = ((after_xt.0 as i64) - (xt.0 as i64)) as i32;
                let new_instr = match self.code[xt.0 as usize] {
                    Instr::Branch(_) => { Instr::Branch(delta) },
                    Instr::BranchOnZero(_) => { Instr::BranchOnZero(delta) },
                    _ => { panic!("invalid instruction in LOOP"); }
                };

                self.code[xt.0 as usize] = new_instr;
            }
        }

        Ok(())
    }

    fn builtin_loop(&mut self) -> Result<(), ForthError> {
        self.compile_loop(false)
    }

    fn builtin_plus_loop(&mut self) -> Result<(), ForthError> {
        self.compile_loop(true)
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

    fn next_input_word(&mut self, delim: u8, max_len: usize) -> Result<ST, ForthError> {
        let off0 = self.input_off;
        let bytes = self.input.as_bytes();
        let (w0,w1,w2) = ToyForth::scan_word(&bytes[off0..], delim);

        let word_off = off0 + w0;
        let word_end = off0 + w1;
        self.last_input_off = self.input_off;
        self.input_off = off0 + w2;

        let len = word_end - word_off;
        if len >= max_len {
            return Err(ForthError::StringTooLong);
        }

        // TODO: Handle large offset by copying to word space?
        if word_off > self.word.len() || word_off > (u8::MAX as usize) || word_off + len > self.word.len() {
            return Err(ForthError::StringOffsetTooLarge);
        }

        Ok(ST::input_space(word_off as u8,len as u8))
    }

    fn next_word(&mut self, delim: u8, max_len: usize) -> Result<ST, ForthError> {
        if self.source_id == ToyForth::SOURCE_INPUT {
            return self.next_input_word(delim,max_len);
        }

        let off0 = self.input_off;
        let bytes = self.bytes_at(self.source)?;
        let (w0,w1,w2) = ToyForth::scan_word(&bytes[off0..], delim);

        let word_off = off0 + w0;
        let word_end = off0 + w1;
        self.last_input_off = self.input_off;
        self.input_off = off0 + w2;

        let len = word_end - word_off;
        if len >= max_len || len > (u8::MAX as usize) {
            return Err(ForthError::StringTooLong);
        }

        // TODO: Handle large offset by copying to word space?
        if word_off > self.word.len() || word_off > (u8::MAX as usize) || word_off + len > self.word.len() {
            return Err(ForthError::StringOffsetTooLarge);
        }

        Ok(self.source.substr(word_off as u8, len as u8))
    }

    // [CHAR]
    fn builtin_brak_char(&mut self) -> Result<(), ForthError> {
        self.check_compiling()?;

        let st = self.next_word(' ' as u8, u8::MAX as usize)?;

        let b = self.bytes_at(st)?;
        if b.len() == 0 {
            return Err(ForthError::InvalidEmptyString);
        }

        let ch = b[0];
        let w = Cell::int(ch as i32);
        self.add_instr(Instr::Push(w));
        Ok(())
    }

    fn builtin_char(&mut self) -> Result<(), ForthError> {
        let st = self.next_word(' ' as u8, u8::MAX as usize)?;

        let b = self.bytes_at(st)?;
        if b.len() == 0 {
            return Err(ForthError::InvalidEmptyString);
        }

        let ch = b[0];
        self.push_int(ch as i32)?;
        Ok(())
    }

    fn builtin_char_bang(&mut self) -> Result<(), ForthError> {
        let addr = self.pop_addr()?;
        // let ch = self.pop_char()?;
        let w = self.pop().ok_or(ForthError::StackUnderflow)?;

        self.set_addr_value(addr, w)?;
        Ok(())
    }

    fn builtin_char_at(&mut self) -> Result<(), ForthError> {
        let addr = self.pop_addr()?;
        let w = self.get_addr_value(addr)?;

        let ch = w.to_char()?;
        self.push_int(ch as i32)?;
        Ok(())
    }

    fn builtin_char_plus(&mut self) -> Result<(), ForthError> {
        let st = self.pop_str()?;
        self.push(st.offset(1).to_cell())?;
        Ok(())
    }

    fn builtin_word(&mut self) -> Result<(), ForthError> {
        let delim = self.pop_char()?;

        let max_len = self.word.len();
        let st = self.next_word(delim, std::cmp::min(u8::MAX as usize,max_len-1))?;

        let len = st.len() as usize;

        // if only there was some way to avoid making this copy...
        let tmp = self.bytes_at(st)?.to_vec();

        let wstr : &mut [u8] = &mut self.word[..];
        if len+1 >= wstr.len() {
            return Err(ForthError::StringTooLong);
        }

        wstr[0] = len as u8;
        wstr[1..(len+1)].copy_from_slice(&tmp);

        self.push(ST::word_space(0, (len+1) as u8).to_cell())?;
        Ok(())
    }

    fn builtin_parse(&mut self) -> Result<(), ForthError> {
        let delim = self.pop_char()?;

        let st = self.next_word(delim, u8::MAX as usize)?;
        let len = st.len();

        self.push(st.to_cell())?;
        self.push_int(len as i32)?;
        Ok(())
    }

    fn add_string_to_quote(&mut self, counted: bool) -> Result<(ST,usize),ForthError> {
        let off0 = self.input_off;
        let bytes = self.input.as_bytes();

        let (w0,w1,w2) = ToyForth::scan_word(&bytes[off0..], '"' as u8);

        let word_off = off0 + w0;
        let word_end = off0 + w1;
        self.input_off = off0 + w2;

        let len = word_end - word_off;
        if (counted && len > ST::MAX_LENGTH-1) || (!counted && len > ST::MAX_LENGTH) {
            return Err(ForthError::StringTooLong);
        }

        let st = if word_off < word_end {
            // allocate string
            let off = self.strings.len();

            if counted {
                self.strings.push( len as u8 );
            }

            let slen = if counted { len + 1 } else { len };

            self.strings.extend_from_slice(&bytes[word_off..word_end]);
            self.strings.push(0);
            ST::allocated_space(off as u32,slen as u8)
        } else {
            // empty string
            ST::allocated_space(0,0)
        };

        Ok((st,len))
    }

    pub fn builtin_s_quote(&mut self) -> Result<(),ForthError> {
        self.check_compiling()?;

        let (st,len) = self.add_string_to_quote(false)?;

        self.add_instr(Instr::Push(st.to_cell()));
        self.add_instr(Instr::Push(Cell::int(len as i32)));
        Ok(())
    }

    pub fn builtin_c_quote(&mut self) -> Result<(),ForthError> {
        self.check_compiling()?;

        let (st,_) = self.add_string_to_quote(true)?;

        self.add_instr(Instr::Push(st.to_cell()));
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

    fn hex2dec(dig: u8) -> Option<u8> {
        let upper = dig.to_ascii_uppercase();

        let zero  = '0' as u8;
        let nine  = '9' as u8;
        let let_a = 'A' as u8;
        let let_f = 'F' as u8;

        if upper >= zero && upper <= nine {
            Some(upper - zero)
        } else if upper >= let_a && upper <= let_f {
            Some(10 + upper - let_a)
        } else {
            None
        }
    }

    pub fn builtin_s_backslash_quote(&mut self) -> Result<(),ForthError> {
        let bytes = &self.input.as_bytes();

        // TODO: on error, truncate self.strings to str_off
        let str_off = self.strings.len();

        if str_off > ST::MAX_OFFSET {
            return Err(ForthError::StringOffsetTooLarge);
        }

        let mut esc = false;
        let mut end = false;
        while !end && self.input_off < bytes.len() {
            let b = bytes[self.input_off];
            let ch = b as char;

            eprintln!("offset {} len {} byte {} char {}", self.input_off, bytes.len(), b, ch);

            if !esc {
                match ch {
                    '"'  => {
                        end = true;
                        self.input_off += 1;
                    },
                    '\\' => {
                        esc = true;
                        self.input_off += 1;
                    },
                    _ => {
                        self.strings.push(b);
                        self.input_off += 1;
                    },
                }
            } else {
                if ch == 'm' {  // CR/LF pair
                    self.strings.push(13);
                    self.strings.push(10);
                    self.input_off += 1;
                } else if ch == 'x' { // \x<hex><hex>
                    if self.input_off+2 >= bytes.len() {
                        // TODO: pass ST token
                        return Err(ForthError::InvalidHexEscape);
                    }

                    let dig1 = bytes[self.input_off+1];
                    let dig2 = bytes[self.input_off+2];
                    let hex1 = ToyForth::hex2dec(dig1).ok_or(ForthError::InvalidHexEscape)?;
                    let hex2 = ToyForth::hex2dec(dig2).ok_or(ForthError::InvalidHexEscape)?;

                    self.strings.push(16*hex1 + hex2);
                    self.input_off += 3;
                } else if ch == 'n' { // newline, LF on Unix but implementation dependent
                    // TODO: add implementation dependence...
                    self.strings.push(10);
                    self.input_off += 1;
                } else {
                    let esc_b : u8 = match ch {
                        'a' =>  7,  // BEL  bell/alert
                        'b' =>  8,  // BS   backspace
                        'e' => 27,  // ESC  escape
                        'f' => 12,  // FF   formfeed
                        'l' => 10,  // LF   linefeed
                        'r' => 13,  // CR   carriage return
                        't' =>  9,  // HT   horizontal tab
                        'v' => 11,  // VT   vertical tab
                        'z' =>  0,  // NUL  null char

                        'q' => '"' as u8,  // double quote
                        '"' => '"' as u8,  // double quote

                        _ => {
                            // TODO: pass ST token
                            return Err(ForthError::InvalidEscape(b as char));
                        }
                    };

                    self.strings.push(esc_b);
                    self.input_off += 1;
                }

                esc = false;
            }
        }

        if !end {
            return Err(ForthError::StringNotTerminated);
        }

        let len = self.strings.len() - str_off;
        if len > ST::MAX_LENGTH {
            return Err(ForthError::StringTooLong);
        }

        let st = if len > 0 {
            self.strings.push(0);
            ST::allocated_space(str_off as u32, len as u8)
        } else {
            ST::allocated_space(0,0)
        };

        self.push(st.to_cell())?;
        self.push_int(len as i32)?;
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

    pub fn builtin_dot_e(&mut self) -> Result<(),ForthError> {
        let w = self.pop().ok_or(ForthError::StackUnderflow)?;
        eprintln!("{} ", w);
        Ok(())
    }

    pub fn builtin_depth(&mut self) -> Result<(),ForthError> {
        let depth = self.stack_depth();
        // TODO: check for overflow!
        self.push_int(depth as i32)?;
        Ok(())
    }

    pub fn builtin_control_depth(&mut self) -> Result<(),ForthError> {
        let depth = self.cstack_depth();
        // TODO: check for overflow!
        self.push_int(depth as i32)?;
        Ok(())
    }

    pub fn builtin_return_depth(&mut self) -> Result<(),ForthError> {
        let depth = self.rstack_depth();
        // TODO: check for overflow!
        self.push_int(depth as i32)?;
        Ok(())
    }

    pub fn here(&self) -> VarAddr {
        let here = self.vars.len();

        // TODO: check for overflow!
        VarAddr(here as u32)
    }

    pub fn builtin_here(&mut self) -> Result<(),ForthError> {
        self.push(self.here().to_cell())?;
        Ok(())
    }

    pub fn builtin_code_here(&mut self) -> Result<(),ForthError> {
        // check for overflow!
        self.push_uint(self.code_size())?;
        Ok(())
    }

    pub fn builtin_char_here(&mut self) -> Result<(),ForthError> {
        // check for overflow!
        self.push_uint(self.char_here())?;
        Ok(())
    }

    pub fn builtin_unused(&mut self) -> Result<(),ForthError> {
        let here = self.vars.len();
        let unused = Cell::INT_MAX - (here as i32);

        // TODO: check for overflow!
        self.push_int(unused)?;
        Ok(())
    }

    // nb: pop is only called from rust, so it's not a forth primitive
    pub fn pop(&mut self) -> Option<Cell> {
        self.dstack.pop()
    }

    // nb: pop is only called from rust, so it's not a forth primitive
    pub fn peek(&self) -> Option<Cell> {
        self.dstack.last().map(|x| *x)
    }

    // nb: pop is only called from rust, so it's not a forth primitive
    pub fn peek_str(&self) -> Result<ST, ForthError> {
        let w = self.peek().ok_or(ForthError::StackUnderflow)?;

        if let CellKind::Str(st) = w.kind() {
            Ok(st)
        } else {
            Err(ForthError::ExpectedString(w))
        }
    }

    fn pop_int(&mut self) -> Result<i32, ForthError> {
        let w = self.pop().ok_or(ForthError::StackUnderflow)?;
        if let CellKind::Int(x) = w.kind() {
            Ok(x)
        } else {
            Err(ForthError::ExpectedInteger(w))
        }
    }

    fn pop_uint(&mut self) -> Result<u32, ForthError> {
        let v = self.pop_int()?;
        Ok((v as u32) & Cell::INT_MASK)
    }

    fn pop_str(&mut self) -> Result<ST,ForthError> {
        let w = self.pop().ok_or(ForthError::StackUnderflow)?;
        if let CellKind::Str(st) = w.kind() {
            Ok(st)
        } else {
            Err(ForthError::ExpectedString(w))
        }
    }

    fn pop_xt(&mut self) -> Result<XT,ForthError> {
        let w = self.pop().ok_or(ForthError::StackUnderflow)?;
        if let CellKind::XT(xt) = w.kind() {
            Ok(xt)
        } else {
            Err(ForthError::ExpectedXT(w))
        }
    }

    fn pop_addr(&mut self) -> Result<Addr,ForthError> {
        let w = self.pop().ok_or(ForthError::StackUnderflow)?;
        match w.kind() {
            CellKind::VarAddr(a_addr) => {
                Ok(Addr::Var(a_addr))
            },
            CellKind::Str(c_addr) => {
                Ok(Addr::Char(c_addr))
            },
            _ => Err(ForthError::ExpectedAddr(w)),
        }
    }

    fn pop_var_addr(&mut self) -> Result<VarAddr,ForthError> {
        let w = self.pop().ok_or(ForthError::StackUnderflow)?;
        if let CellKind::VarAddr(addr) = w.kind() {
            Ok(addr)
        } else {
            Err(ForthError::ExpectedVarAddr(w))
        }
    }

    fn pop_kind(&mut self) -> Option<CellKind> {
        self.dstack.pop().map(Cell::kind)
    }

    pub fn exec_at(&mut self, xt: XT) -> Result<ForthResult, ForthError> {
        let prev_pc = self.pc;
        self.pc = xt.0;
        let ret = self.exec();
        if ret.is_ok() {
            self.pc = prev_pc;
        }
        return ret;
    }

    pub fn exec(&mut self) -> Result<ForthResult, ForthError> {
        loop {
            if self.pc as usize >= self.code.len() {
                return Err(ForthError::InvalidPC(self.pc));
            }
            let op = self.code[self.pc as usize];

            // eprintln!("pc = {}, code[pc] = {:?}", pc, op);
            match op {
                Instr::Empty => {
                    return Err(ForthError::InvalidCell(XT(self.pc)));
                },
                Instr::Nop => {
                    self.pc += 1;
                },
                Instr::Bye => {
                    return Ok(ForthResult::Bye);
                },
                Instr::Push(w) => {
                    self.push(w)?;
                    self.pc += 1;
                },
                Instr::Drop => {
                    self.drop()?;
                    self.pc += 1;
                },
                Instr::Pick => {
                    let u = self.pop_uint()?;
                    self.pick(u as usize)?;
                    self.pc += 1;
                },
                Instr::Roll => {
                    let u = self.pop_uint()?;
                    self.roll(u as usize)?;
                    self.pc += 1;
                },
                Instr::Rot => {
                    self.roll(2)?;
                    self.pc += 1;
                },
                Instr::Dup => {
                    self.dup()?;
                    self.pc += 1;
                },
                Instr::Swap => {
                    self.swap()?;
                    self.pc += 1;
                },
                Instr::Over => {
                    self.over()?;
                    self.pc += 1;
                },
                Instr::Defer(xt) | Instr::Jump(xt) => {
                    self.pc = xt.0;
                },
                Instr::Error(code) => {
                    let w = self.pop().ok_or(ForthError::StackUnderflow)?;
                    let err = ForthError::from_code(code, w)?;

                    return Err(err);
                },
                Instr::Branch(delta) => {
                    if delta == 0 {
                        return Err(ForthError::InvalidControlInstruction(XT(self.pc)));
                    }

                    let new_pc = (self.pc as i64) + (delta as i64);
                    // FIXME: check range
                    self.pc = new_pc as u32;
                },
                Instr::BranchOnZero(delta) => {
                    if delta == 0 {
                        return Err(ForthError::InvalidControlInstruction(XT(self.pc)));
                    }

                    let arg = self.pop_int()?;
                    if arg == 0 {
                        let new_pc = (self.pc as i64) + (delta as i64);
                        // FIXME: check range
                        self.pc = new_pc as u32;
                    } else {
                        self.pc += 1;
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
                            if let CellKind::Int(index) = itm.kind() {
                                self.cstack.push(ControlEntry::Index(index));
                            } else {
                                return Err(ForthError::InvalidIndex(itm));
                            }
                        }
                    }

                    self.pc += 1;
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

                    self.pc += 1;
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

                    self.pc += 1;
                },
                Instr::ControlIteration{incr} => {
                    let delta = if incr { self.pop_int()? } else { 1 };

                    let clen = self.cstack.len();
                    if clen < 2 {
                        return Err(ForthError::ControlStackUnderflow);
                    }

                    let top = if let ControlEntry::Index(idx) = self.cstack[clen-2] {
                        idx
                    } else {
                        return Err(ForthError::InvalidControlEntry(self.cstack[clen-2]));
                    };

                    let next = if let ControlEntry::Index(idx) = self.cstack[clen-1] {
                        idx+delta
                    } else {
                        return Err(ForthError::InvalidControlEntry(self.cstack[clen-1]));
                    };

                    self.cstack[clen-1] = ControlEntry::Index(next);
                    self.push(Cell::bool(next == top))?;

                    self.pc += 1;
                },
                Instr::ReturnPush => {
                    self.data_to_aux()?;
                    self.pc += 1;
                },
                Instr::ReturnPop => {
                    self.aux_to_data()?;
                    self.pc += 1;
                },
                Instr::ReturnCopy => {
                    self.aux_copy_to_data()?;
                    self.pc += 1;
                },
                Instr::Execute => {
                    let xt = self.pop_xt()?;
                    // TODO: check range
                    self.rstack.push(XT(self.pc+1));
                    self.pc = xt.0;
                },
                Instr::UnaryOp(op) => {
                    self.unary_op(op)?;
                    self.pc += 1;
                },
                Instr::BinaryOp(op) => {
                    self.binary_op(op)?;
                    self.pc += 1;
                },

                Instr::Func(x) => {
                    let ind = x as usize;
                    if ind >= self.ufuncs.len() {
                        return Err(ForthError::InvalidFunction(x));
                    }

                    let fxn = self.ufuncs[ind].0;

                    fxn(self)?;
                    self.pc += 1;
                },

                Instr::DoCol(new_pc) => {
                    // TODO: check range
                    self.rstack.push(XT(self.pc+1));
                    self.pc = new_pc.0;
                },
                Instr::Refill => {
                    // clear input state
                    self.input.clear();
                    self.input_off = 0;
                    self.last_input_off = 0;

                    // set up for next instruction
                    self.pc += 1;

                    return Ok(ForthResult::Refill);
                },
                Instr::Exit|Instr::Unnest => {
                    let ret = self.rstack.pop().ok_or(ForthError::ReturnStackUnderflow)?;
                    self.pc = ret.0;
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
        assert_eq!(Cell::int(123).to_int().unwrap(), 123);
        assert_eq!(Cell::int(-123).to_int().unwrap(), -123);

        assert_eq!(Cell::xt(123).to_xt().unwrap(), XT(123));

        assert_eq!(Cell::str(((123 as u32)<<8) | 10).to_str().unwrap(), ST::allocated_space(123, 10));

        assert_eq!(Cell::xt(123).to_int(), None);
        assert_eq!(Cell::xt(123).to_str(), None);
        assert_eq!(Cell::xt(123).to_addr(), None);

        assert_eq!(Cell::str(123).to_int(), None);
        assert_eq!(Cell::str(123).to_xt(), None);
        assert_eq!(Cell::str(123).to_addr(), None);

        assert_eq!(Cell::int(123).to_xt(), None);
        assert_eq!(Cell::int(123).to_str(), None);
        assert_eq!(Cell::int(123).to_addr(), None);

        assert_eq!(Cell::int(-123).to_xt(), None);
        assert_eq!(Cell::int(-123).to_str(), None);
        assert_eq!(Cell::int(-123).to_addr(), None);

        assert_eq!(Cell::addr(123), Cell(Cell::HIGH_BIT | Cell::SIGN_BIT | VarAddr::ADDR_BIT | 123));
        assert_eq!(Cell::addr(123), VarAddr(123).to_cell());
        assert_eq!(Cell::addr(123).to_addr().unwrap(), VarAddr(123));
        assert_eq!(Cell::addr(123).to_xt(), None);
        assert_eq!(Cell::addr(123).to_str(), None);
    }

    #[test]
    #[ignore]
    fn all_xt_values() {
        for x in 0 .. (XT::MAX+1) {
            let w = Cell::xt(x);
            assert_eq!(w.to_xt().unwrap(), XT(x), "word {:?} does not convert to XT({}) ", w, x);
            assert_eq!(w.to_int(),  None, "XT({}) incorrectly shares a representation with int", x);
            assert_eq!(w.to_str(),  None, "XT({}) incorrectly shares a representation with ST", x);
            assert_eq!(w.to_addr(), None, "XT({}) incorrectly shares a representation with VarAddr", x);
        }
    }

    #[test]
    #[ignore]
    fn all_addr_values() {
        for x in 0 .. (VarAddr::MAX+1) {
            let w = Cell::addr(x);
            assert_eq!(w.to_addr().unwrap(), VarAddr(x), "word {:?} does not convert to VarAddr({}) ", w, x);
            assert_eq!(w.to_int(), None, "VarAddr({}) incorrectly shares a representation with int", x);
            assert_eq!(w.to_str(), None, "VarAddr({}) incorrectly shares a representation with ST", x);
            assert_eq!(w.to_xt(),  None, "VarAddr({}) incorrectly shares a representation with XT", x);
        }
    }

    #[test]
    #[ignore]
    fn all_int_values() {
        for x in Cell::INT_MIN .. (Cell::INT_MAX+1) {
            let w = Cell::int(x);
            assert_eq!(w.to_int().unwrap(), x, "word {:?} does not convert to integer {} ", w, x);
            assert_eq!(w.to_xt(),  None, "int({}) incorrectly shares a representation with XT", x);
            assert_eq!(w.to_str(), None, "int({}) incorrectly shares a representation with ST", x);
            assert_eq!(w.to_addr(), None, "int({}) incorrectly shares a representation with VarAddr", x);
        }
    }

    #[test]
    fn stack_prims() {
        let mut forth = ToyForth::new();
        forth.push(Cell::int( 123)).unwrap();
        forth.push(Cell::int(-123)).unwrap();
        assert_eq!(forth.pop().unwrap(), Cell::int(-123));
        assert_eq!(forth.pop().unwrap(), Cell::int( 123));

        forth.push(Cell::int( 123)).unwrap();
        forth.push(Cell::int(-123)).unwrap();
        forth.swap().unwrap();
        assert_eq!(forth.pop().unwrap(), Cell::int( 123));
        assert_eq!(forth.pop().unwrap(), Cell::int(-123));

        forth.push(Cell::int( 123)).unwrap();
        forth.dup().unwrap();
        assert_eq!(forth.pop().unwrap(), Cell::int(123));
        assert_eq!(forth.pop().unwrap(), Cell::int(123));
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

        assert_eq!(st1.to_cell().kind(), CellKind::Str(st1));
        assert_eq!(st2.to_cell().kind(), CellKind::Str(st2));
    }

    #[test]
    fn run_stack_manip() {
        let mut forth = ToyForth::new();

        let code = vec![
            Instr::Push(Cell::int(4314)),
            Instr::Push(Cell::int(-132)),
            Instr::Push(Cell::int(-999)),
            Instr::Swap,
            Instr::Drop,
            Instr::Bye,
        ];

        let xt = forth.add_code(&code);

        forth.exec_at(xt).unwrap();
        assert_eq!(forth.pop().unwrap(), Cell::int(-999));
        assert_eq!(forth.pop().unwrap(), Cell::int(4314));
        assert_eq!(forth.pop(), None);
    }

    #[test]
    fn run_arith() {
        let mut forth = ToyForth::new();

        let code = vec![
            Instr::Push(Cell::int(4314)),
            Instr::Push(Cell::int(-132)),
            Instr::BinaryOp(BinOp::Plus),
            Instr::Push(Cell::int(-10)),
            Instr::BinaryOp(BinOp::Star),
            Instr::Bye,
        ];

        let xt = forth.add_code(&code);
        assert_eq!(forth.exec_at(xt).unwrap(), ForthResult::Bye);

        assert_eq!(forth.pop().unwrap(), Cell::int(-41820));
        assert_eq!(forth.pop(), None);
    }

    #[test]
    fn run_dictionary_entry() {
        let mut forth = ToyForth::new();

        let (xt0,entries) = forth.allocate_cells(5);

        assert_eq!(entries.len(), 5);

        /* f(x) = 2*x + 1 */
        entries[0] = Instr::Push(Cell::int(2));
        entries[1] = Instr::BinaryOp(BinOp::Star);
        entries[2] = Instr::Push(Cell::int(1));
        entries[3] = Instr::BinaryOp(BinOp::Plus);
        entries[4] = Instr::Unnest;

        let xt1 = forth.add_code(&vec![
            Instr::Push(Cell::int(2)),
            Instr::DoCol(xt0),
            Instr::Bye,
        ]);

        forth.exec_at(xt1).unwrap();
        assert_eq!(forth.pop().unwrap(), Cell::int(5));
        assert_eq!(forth.pop(), None);
    }

    #[test]
    fn can_define() {
        let mut forth = ToyForth::new();

        let (xt,entries) = forth.allocate_cells(5);
        assert_eq!(entries.len(), 5);

        /* f(x) = 2*x + 1 */
        entries[0] = Instr::Push(Cell::int(2));
        entries[1] = Instr::BinaryOp(BinOp::Star);
        entries[2] = Instr::Push(Cell::int(1));
        entries[3] = Instr::BinaryOp(BinOp::Plus);
        entries[4] = Instr::Unnest;

        forth.define_word("my_func", xt, forth.mark_code(), 0).unwrap();

        let lookup_xt = forth.lookup_word("my_func").unwrap();
        assert_eq!(xt, lookup_xt);
    }

    #[test]
    fn builtin_word_scans_words() {
        let mut forth = ToyForth::new();

        forth.set_input("  x  test foo bar   ");

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 5);
        assert_eq!(forth.counted_string_at(forth.peek_str().unwrap()), "x");
        assert_eq!(forth.pop().unwrap(), Cell::from_str(ST::word_space(0,2)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 10);
        assert_eq!(forth.counted_string_at(forth.peek_str().unwrap()), "test");
        assert_eq!(forth.pop().unwrap(), Cell::from_str(ST::word_space(0,5)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 14);
        assert_eq!(forth.counted_string_at(forth.peek_str().unwrap()), "foo");
        assert_eq!(forth.pop().unwrap(), Cell::from_str(ST::word_space(0,4)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 20);
        assert_eq!(forth.counted_string_at(forth.peek_str().unwrap()), "bar");
        assert_eq!(forth.pop().unwrap(), Cell::from_str(ST::word_space(0,4)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 20);
        let pk = forth.peek().unwrap();
        eprintln!("last word is {:?} - {} - {:b}", pk, pk, pk.0);
        assert_eq!(forth.counted_string_at(forth.peek_str().unwrap()), "");
        assert_eq!(forth.pop().unwrap(), ST::word_space(0,1).to_cell());

        // make sure we can search again and it's well behaved...
        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 20);
        let pk = forth.peek().unwrap();
        eprintln!("last word is {:?} - {} - {:b}", pk, pk, pk.0);
        assert_eq!(forth.counted_string_at(forth.peek_str().unwrap()), "");
        assert_eq!(forth.pop().unwrap(), ST::word_space(0,1).to_cell());
    }

    #[test]
    fn builtin_char_at_and_char_plus() {
        let mut forth = ToyForth::new();

        forth.set_input("  xtest  ");

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        assert_eq!(forth.input_off, 9);
        assert_eq!(forth.bytes_at(forth.peek_str().unwrap()).unwrap(),
            &vec![5 as u8, 'x' as u8, 't' as u8, 'e' as u8, 's' as u8, 't' as u8]);
        assert_eq!(forth.counted_string_at(forth.peek_str().unwrap()), "xtest");

        forth.dup().unwrap();
        forth.builtin_char_at().unwrap();
        assert_eq!(forth.pop_int().unwrap(), 5 as i32);

        forth.builtin_char_plus().unwrap();
        assert_eq!(forth.bytes_at(forth.peek_str().unwrap()).unwrap(),
            &vec!['x' as u8, 't' as u8, 'e' as u8, 's' as u8, 't' as u8]);
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
        assert_eq!(forth.pop().unwrap(), Cell::from_str(ST::input_space(2,1)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_parse().unwrap();
        assert_eq!(forth.input_off, 10);
        assert_eq!(forth.pop_int().unwrap(), 4);
        assert_eq!(forth.pop().unwrap(), Cell::from_str(ST::input_space(5,4)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_parse().unwrap();
        assert_eq!(forth.input_off, 14);
        assert_eq!(forth.pop_int().unwrap(), 3);
        assert_eq!(forth.pop().unwrap(), Cell::from_str(ST::input_space(10,3)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_parse().unwrap();
        assert_eq!(forth.input_off, 20);
        assert_eq!(forth.pop_int().unwrap(), 3);
        assert_eq!(forth.pop().unwrap(), Cell::from_str(ST::input_space(14,3)));

        forth.push_int(' ' as i32).unwrap();
        forth.builtin_parse().unwrap();
        assert_eq!(forth.input_off, 20);
        assert_eq!(forth.pop_int().unwrap(), 0);
        assert_eq!(forth.pop().unwrap(), ST::input_space(20,0).to_cell());

        // make sure we can search again and it's well behaved...
        forth.push_int(' ' as i32).unwrap();
        forth.builtin_parse().unwrap();
        assert_eq!(forth.input_off, 20);
        assert_eq!(forth.pop_int().unwrap(), 0);
        assert_eq!(forth.pop().unwrap(), ST::input_space(20,0).to_cell());
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
           Instr::Push(Cell::int(2)),
           Instr::BinaryOp(BinOp::Star),
           Instr::Push(Cell::int(1)),
           Instr::BinaryOp(BinOp::Plus),
           Instr::Unnest,
        ], 0).unwrap();

        // look up various things
        forth.set_input("test");
        {
            forth.push_int(' ' as i32).unwrap();
            forth.builtin_word().unwrap();
            let st = forth.peek_str().unwrap();

            forth.builtin_find().unwrap();

            assert_eq!(forth.pop_int().unwrap(), 0);
            assert_eq!(forth.pop_kind().unwrap(), CellKind::Str(st));
        }

        forth.set_input("my_func");
        {
            forth.push_int(' ' as i32).unwrap();
            forth.builtin_word().unwrap();
            forth.builtin_find().unwrap();

            assert_eq!(forth.pop_int().unwrap(), -1);
            assert_eq!(forth.pop_kind().unwrap(), CellKind::XT(xt));
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
           Instr::Push(Cell::int(2)),
           Instr::BinaryOp(BinOp::Star),
           Instr::Push(Cell::int(1)),
           Instr::BinaryOp(BinOp::Plus),
           Instr::Unnest,
        ], 0).unwrap();

        // look up various things
        forth.set_input("test");
        {
            forth.push_int(' ' as i32).unwrap();
            forth.builtin_parse().unwrap();

            let len = forth.pop_int().unwrap();
            let st  = forth.pop_str().unwrap();

            forth.push(st.to_cell()).unwrap();
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
            assert_eq!(forth.pop_kind().unwrap(), CellKind::XT(xt));
        }
    }

    #[test]
    fn can_execute_token() {
        let mut forth = ToyForth::new();

        forth.add_word("my_func", &vec![
           Instr::Push(Cell::int(2)),
           Instr::BinaryOp(BinOp::Star),
           Instr::Push(Cell::int(1)),
           Instr::BinaryOp(BinOp::Plus),
           Instr::Unnest,
        ], 0).unwrap();

        forth.push_int(1234).unwrap();

        forth.set_input("my_func");
        forth.push_int(' ' as i32).unwrap();
        forth.builtin_word().unwrap();
        forth.builtin_find().unwrap();

        assert_eq!(forth.pop_int().unwrap(), -1);
        forth.interpret("EXECUTE").unwrap();
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

        forth.add_primitive("ONE", Instr::Push(Cell::int(1))).unwrap();
        forth.add_primitive("TWO", Instr::Push(Cell::int(2))).unwrap();

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
        forth.push(Cell::from_str(st)).unwrap();
        forth.push_int(3).unwrap();
        forth.builtin_to_number().unwrap();

        assert_eq!(forth.stack_depth(), 3);
        assert_eq!(forth.pop_int().unwrap(), 3);
        assert_eq!(forth.pop_str().unwrap(), st.offset(3));
        assert_eq!(forth.pop_int().unwrap(), 123);

        forth.push_int(0).unwrap();
        let st = forth.add_string("54a3").unwrap();
        forth.push(Cell::from_str(st)).unwrap();
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
        assert!(matches!(forth.data_to_aux().unwrap_err(), ForthError::StackUnderflow));
        assert!(matches!(forth.aux_to_data().unwrap_err(), ForthError::StackUnderflow));

        forth.push_int(1).unwrap();
        forth.push_int(2).unwrap();

        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.rstack_depth(), 0);

        forth.data_to_aux().unwrap();

        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.aux_stack_depth(), 1);
        assert_eq!(forth.rstack_depth(), 0);

        assert_eq!(forth.dstack.last().map(|x| *x).unwrap(), Cell::int(1));
        assert_eq!(forth.aux_stack.last().map(|x| *x).unwrap(), Cell::int(2));

        forth.push_int(3).unwrap();
        forth.aux_to_data().unwrap();

        assert_eq!(forth.stack_depth(), 3);
        assert_eq!(forth.aux_stack_depth(), 0);
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

        let addr = forth.new_var(Cell::int(0)).unwrap();
        assert_eq!(forth.get_var_at(addr).unwrap(), Cell::int(0));

        forth.set_var_at(addr, Cell::int(123)).unwrap();
        assert_eq!(forth.get_var_at(addr).unwrap(), Cell::int(123));
    }

    #[test]
    fn forth_can_allocate_and_use_vars() {
        let mut forth = ToyForth::new();

        let base = VarAddr(forth.addr_here());

        forth.interpret("VARIABLE V1").unwrap();
        assert_eq!(forth.stack_depth(), 0);

        forth.interpret("V1").unwrap();
        assert_eq!(forth.stack_depth(), 1);

        assert_eq!(forth.pop_var_addr().unwrap(), base);
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
        assert_eq!(forth.pop_var_addr().unwrap(), ToyForth::ADDR_STATE);

        forth.interpret("STATE @").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 0);
    }

    #[test]
    fn comparisons() {
        let mut forth = ToyForth::new();

        // 5,3
        forth.interpret("5 3 >").unwrap();
        assert_eq!(forth.pop().unwrap(), Cell::true_value());

        forth.interpret("5 3 <").unwrap();
        assert_eq!(forth.pop().unwrap(), Cell::false_value());

        forth.interpret("5 3 =").unwrap();
        assert_eq!(forth.pop().unwrap(), Cell::false_value());

        forth.interpret("5 3 <>").unwrap();
        assert_eq!(forth.pop().unwrap(), Cell::true_value());

        // 3,5
        forth.interpret("3 5 >").unwrap();
        assert_eq!(forth.pop().unwrap(), Cell::false_value());

        forth.interpret("3 5 <").unwrap();
        assert_eq!(forth.pop().unwrap(), Cell::true_value());

        forth.interpret("3 5 =").unwrap();
        assert_eq!(forth.pop().unwrap(), Cell::false_value());

        forth.interpret("3 5 <>").unwrap();
        assert_eq!(forth.pop().unwrap(), Cell::true_value());

        // 3,3
        forth.interpret("3 3 =").unwrap();
        assert_eq!(forth.pop().unwrap(), Cell::true_value());

        forth.interpret("3 3 >").unwrap();
        assert_eq!(forth.pop().unwrap(), Cell::false_value());

        forth.interpret("3 3 <").unwrap();
        assert_eq!(forth.pop().unwrap(), Cell::false_value());

        forth.interpret("3 3 <>").unwrap();
        assert_eq!(forth.pop().unwrap(), Cell::false_value());
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

        forth.interpret(": foo 3 0 do dup . 5 + loop ;").unwrap();

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
    fn plus_loop() {
        let mut forth = ToyForth::new();

        forth.interpret(": foo 0 3 do dup . 5 + -1 +loop ;").unwrap();

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
    3 0 do \
        3 0 do \
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
I 0   J 0 
I 0   J 1 
I 0   J 2 
I 1   J 0 
I 1   J 1 
I 1   J 2 
I 2   J 0 
I 2   J 1 
I 2   J 2 
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
    fn s_backslash_quote_strings() {
        let mut forth = ToyForth::new();

        {
            forth.interpret(": test S\\\" foo\\n\\\"bar\\\"\" ; test").unwrap();
            forth.print_word_code("test");
            assert_eq!(forth.stack_depth(), 2);

            let count = forth.pop_int().unwrap();
            let st = forth.pop_str().unwrap();
            assert_eq!(count, 9);
            assert_eq!(forth.string_at(st), "foo\n\"bar\"");
        }
    }

    #[test]
    fn c_quote_strings() {
        let mut forth = ToyForth::new();

        forth.interpret(": test C\" foo bar \" ;").unwrap();

        {
            forth.interpret("test").unwrap();
            forth.print_word_code("test");
            assert_eq!(forth.stack_depth(), 1);
            let st = forth.pop_str().unwrap();
            assert_eq!(st.len(), 9);
            assert_eq!(forth.counted_string_at(st), "foo bar ");
        }

        {
            forth.interpret("test COUNT").unwrap();
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

        forth.interpret("test").unwrap();
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

        forth.interpret("NOP").unwrap();
        let default_rstack_depth = forth.rstack_depth();

        forth.interpret("\
: BAR 3
    BEGIN
        5 +
        DUP . CR
        DUP .S 28 > IF .S EXIT THEN 
    AGAIN
;

BAR
").unwrap();

        forth.print_word_code("bar");

        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.cstack_depth(), 0);
        assert_eq!(forth.rstack_depth(), default_rstack_depth);

        assert_eq!(forth.pop_int().unwrap(), 33);
    }

    #[test]
    fn begin_until_loop() {
        let mut forth = ToyForth::new();

        forth.interpret("NOP").unwrap();
        let default_rstack_depth = forth.rstack_depth();

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
        assert_eq!(forth.rstack_depth(), default_rstack_depth);

        assert_eq!(forth.pop_int().unwrap(), 33);
    }

    #[test]
    fn begin_while_loop() {
        let mut forth = ToyForth::new();

        forth.interpret("NOP").unwrap();
        let default_rstack_depth = forth.rstack_depth();

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
        assert_eq!(forth.rstack_depth(), default_rstack_depth);

        assert_eq!(forth.pop_int().unwrap(), 30);
    }

    #[test]
    fn do_loop_with_leave() {
        let mut forth = ToyForth::new();

        forth.interpret("NOP").unwrap();
        let default_rstack_depth = forth.rstack_depth();

        forth.interpret("\
: BAR
    1
    10 0 DO
        OVER *
        DUP 100 > IF LEAVE THEN
        .\" Iteration \" I .  .\" Value \" DUP . CR
        .S
    LOOP
    SWAP DROP
    .S
    .\" Final: \" DUP . CR
;
").unwrap();

        forth.print_word_code("BAR");

        forth.interpret("5 BAR").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.cstack_depth(), 0);
        assert_eq!(forth.rstack_depth(), default_rstack_depth);

        assert_eq!(forth.pop_int().unwrap(), 125);

        forth.interpret("2 BAR").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.cstack_depth(), 0);
        assert_eq!(forth.rstack_depth(), default_rstack_depth);

        assert_eq!(forth.pop_int().unwrap(), 128);
    }

    #[test]
    fn loop_unloop_exit() {
        let mut forth = ToyForth::new();

        forth.interpret("NOP").unwrap();
        let default_rstack_depth = forth.rstack_depth();

        forth.interpret("\
: TEST ( num1 niter -- num2 iters )
    .\" Starting value \" OVER . CR
    0 ?DO
        2 *
        DUP 15 / +
        1+
        .\" Iter \" I 1+ . .\" value \" DUP . CR
        DUP 35 > IF UNLOOP EXIT THEN
    LOOP
;").unwrap();

        forth.stdout_interpret("1 10 TEST").unwrap();
        // iteration        value
        // start            1
        // 1                3
        // 2                7
        // 3                15
        // 4                33
        // 5                66 + 4 + 1 = 71
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 71);
        assert_eq!(forth.rstack_depth(), default_rstack_depth);
        assert_eq!(forth.cstack_depth(), 0);
    }

    #[test]
    fn qdo_loop() {
        let mut forth = ToyForth::new();

        forth.interpret("\
VARIABLE iter
: BAR
    .\" Starting iteration\" CR
    .S
    -1 iter !
    5 SWAP 
    ?DO
        1+
        I iter !
        .\" Iteration\" I . .\" iter = \" iter @ . CR
        .S
        \\ LEAVE
    LOOP
    .\" Done. iter = \" iter @ . CR
    .S
;").unwrap();

        forth.print_word_code("BAR");

        forth.interpret("0 5 BAR iter @ .S").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), -1);
        assert_eq!(forth.pop_int().unwrap(),  0);

        forth.interpret("0 0 BAR iter @").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), 4);
        assert_eq!(forth.pop_int().unwrap(), 5);

        forth.interpret("17 -3 BAR iter @").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), 4);
        assert_eq!(forth.pop_int().unwrap(), 25);
    }

    #[test]
    fn plus_bang() {
        let mut forth = ToyForth::new();

        forth.interpret("NOP").unwrap();
        let default_rstack_depth = forth.rstack_depth();

        forth.interpret("\
VARIABLE FOO
3 FOO !
5 FOO +!
FOO @
").unwrap();

        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.cstack_depth(), 0);
        assert_eq!(forth.rstack_depth(), default_rstack_depth);

        assert_eq!(forth.pop_int().unwrap(), 8);
    }

    #[test]
    fn recurse() {
        let mut forth = ToyForth::new();

        forth.interpret("\
: FACTORIAL 
    E\" DEFINING FACTORIAL\"
    DUP 1 .S > IF
        DUP 1- RECURSE *
        .S
    THEN
;
").unwrap();

        forth.interpret("5 DROP").unwrap();
        forth.print_stacks("--1--");
        forth.print_word_code("FACTORIAL");

        let normal_depth = forth.rstack_depth();
        eprintln!("normal depth = {}", normal_depth);

        forth.interpret("5 FACTORIAL").unwrap();
        forth.print_stacks("factorial");

        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.cstack_depth(), 0);
        assert_eq!(forth.rstack_depth(), normal_depth);

        assert_eq!(forth.pop_int().unwrap(), 120);
    }

    #[test]
    fn comments() {
        let mut forth = ToyForth::new();
        let outv = Rc::new(RefCell::new(Vec::<u8>::new()));

        forth.interpret("NOP").unwrap();
        let default_rstack_depth = forth.rstack_depth();

        forth.capture_interpret("\
: FACTORIAL  .( Computes factorial )
    ( n1 -- n2 )
    DUP 1 > IF              \\ if n > 1, recurse, otherwise return 1
        DUP 1- RECURSE *    \\ return n * (n-1)!
    THEN
;
", outv.clone()).unwrap();

        forth.capture_interpret("5 FACTORIAL", outv.clone()).unwrap();

        forth.print_word_code("FACTORIAL");

        {
            let outb = outv.borrow();
            let s = std::str::from_utf8(&outb).unwrap();
            assert_eq!(s, "Computes factorial ");
        }

        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.cstack_depth(), 0);
        assert_eq!(forth.rstack_depth(), default_rstack_depth);

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

    #[test]
    fn within_works_on_signed_and_unsigned() {
        let mut forth = ToyForth::new();
        forth.interpret("\
 5  0 10 WITHIN \\ easy one, all positive
15  0 10 WITHIN \\ outside of range
-5  0 10 WITHIN \\ outside of range
 5 10  0 WITHIN \\ flip order

-2 -3 -1 WITHIN \\ negative
-4 -3 -1 WITHIN \\ negative: outside of range
 3 -3 -1 WITHIN \\ negative: outside of range
-2 -1 -3 WITHIN \\ negative: flip order

 0 -5  5 WITHIN \\ sign change
 6 -5  5 WITHIN \\ sign change: outside of range
-6 -5  5 WITHIN \\ sign change: outside of range
 0  5 -5 WITHIN \\ sign change: flip order
").unwrap();

        assert_eq!(forth.stack_depth(), 12);

        assert_eq!(forth.pop_int().unwrap(),  0); //  0  5 -5 WITHIN \\ sign change: flip order
        assert_eq!(forth.pop_int().unwrap(),  0); // -6 -5  5 WITHIN \\ sign change: outside of range
        assert_eq!(forth.pop_int().unwrap(),  0); //  6 -5  5 WITHIN \\ sign change: outside of range
        assert_eq!(forth.pop_int().unwrap(), -1); //  0 -5  5 WITHIN \\ sign change
        
        assert_eq!(forth.pop_int().unwrap(),  0); // -2 -1 -3 WITHIN \\ negative: flip order
        assert_eq!(forth.pop_int().unwrap(),  0); //  3 -3 -1 WITHIN \\ negative: outside of range
        assert_eq!(forth.pop_int().unwrap(),  0); // -4 -3 -1 WITHIN \\ negative: outside of range
        assert_eq!(forth.pop_int().unwrap(), -1); // -2 -3 -1 WITHIN \\ negative

        assert_eq!(forth.pop_int().unwrap(),  0); //  5 10  0 WITHIN \\ flip order
        assert_eq!(forth.pop_int().unwrap(),  0); // -5  0 10 WITHIN \\ outside of range
        assert_eq!(forth.pop_int().unwrap(),  0); // 15  0 10 WITHIN \\ outside of range
        assert_eq!(forth.pop_int().unwrap(), -1); //  5  0 10 WITHIN \\ easy one, all positive
    }

    #[test]
    fn logical_shifts() {
        let mut forth = ToyForth::new();

        forth.interpret("\
HEX
0        CONSTANT 0S
0 INVERT CONSTANT 1S
1S 1 RSHIFT INVERT CONSTANT MSB

   1 0 RSHIFT \\ 1
   1 1 RSHIFT \\ 0
   2 1 RSHIFT \\ 1
   4 2 RSHIFT \\ 1
8000 F RSHIFT \\ 1
MSB  1 RSHIFT MSB AND \\ 0

   1 0 LSHIFT \\ 1
   1 1 LSHIFT \\ 2
   1 2 LSHIFT \\ 4
   1 F LSHIFT \\ 8000
 MSB 1 LSHIFT \\ 0

  1 2* \\ 2
  2 2* \\ 4
  4 2* \\ 8
 -1 2* \\ -2
MSB 2* \\ 0

  1 2/ \\ 0
  2 2/ \\ 1
  4 2/ \\ 2
 -1 2/ MSB AND \\ 0
MSB 2/ MSB AND \\ 0
 -2 2/ INVERT MSB = \\ <true>
").unwrap();


        assert_eq!(forth.pop_int().unwrap(),  -1);//  -2 2/ INVERT MSB = \\ <true>
        assert_eq!(forth.pop_uint().unwrap(),  0); // MSB 2/ MSB AND \\ 0
        assert_eq!(forth.pop_uint().unwrap(),  0); //  -1 2/ MSB AND \\ 0
        assert_eq!(forth.pop_uint().unwrap(),  2); //   4 2/ \\ 2
        assert_eq!(forth.pop_uint().unwrap(),  1); //   2 2/ \\ 1
        assert_eq!(forth.pop_uint().unwrap(),  0); //   1 2/ \\ 0

        assert_eq!(forth.pop_uint().unwrap(),  0); // MSB 2* \\ 0
        assert_eq!(forth.pop_int().unwrap(),  -2); //  -1 2* \\ -2
        assert_eq!(forth.pop_uint().unwrap(),  8); //   4 2* \\ 8
        assert_eq!(forth.pop_uint().unwrap(),  4); //   2 2* \\ 4
        assert_eq!(forth.pop_uint().unwrap(),  2); //   1 2* \\ 2

        assert_eq!(forth.pop_uint().unwrap(), 0);       //  MSB 1 LSHIFT \\ 0
        assert_eq!(forth.pop_uint().unwrap(), 0x8000);  //    1 F LSHIFT \\ 8000
        assert_eq!(forth.pop_uint().unwrap(), 4);       //    1 2 LSHIFT \\ 4
        assert_eq!(forth.pop_uint().unwrap(), 2);       //    1 1 LSHIFT \\ 2
        assert_eq!(forth.pop_uint().unwrap(), 1);       //    1 0 LSHIFT \\ 1

        assert_eq!(forth.pop_uint().unwrap(), 0);       // MSB  1 RSHIFT MSB AND \\ 0
        assert_eq!(forth.pop_uint().unwrap(), 1);       // 8000 F RSHIFT \\ 1
        assert_eq!(forth.pop_uint().unwrap(), 1);       //    4 2 RSHIFT \\ 1
        assert_eq!(forth.pop_uint().unwrap(), 1);       //    2 1 RSHIFT \\ 1
        assert_eq!(forth.pop_uint().unwrap(), 0);       //    1 1 RSHIFT \\ 0
        assert_eq!(forth.pop_uint().unwrap(), 1);       //    1 0 RSHIFT \\ 1
    }

    #[test]
    fn mod_produces_remainder() {
        let mut forth = ToyForth::new();

        forth.interpret("\
 5 2 MOD \\  1
-5 2 MOD \\ -1
10 3 MOD \\  1
10 1 MOD \\  0
11 3 MOD \\  2
12 3 MOD \\  0").unwrap();

        assert_eq!(forth.stack_depth(), 6);

        assert_eq!(forth.pop_int().unwrap(),  0); // 12 3 MOD \\  0
        assert_eq!(forth.pop_int().unwrap(),  2); // 11 3 MOD \\  2
        assert_eq!(forth.pop_int().unwrap(),  0); // 10 1 MOD \\  0
        assert_eq!(forth.pop_int().unwrap(),  1); // 10 3 MOD \\  1
        assert_eq!(forth.pop_int().unwrap(), -1); // -5 2 MOD \\ -1
        assert_eq!(forth.pop_int().unwrap(),  1); //  5 2 MOD \\  1

        forth.interpret("\
 5 2 /MOD \\  1  2
-5 2 /MOD \\ -1 -2
10 3 /MOD \\  1  3
10 1 /MOD \\  0 10
11 3 /MOD \\  2  3
12 3 /MOD \\  0  4").unwrap();

        assert_eq!(forth.stack_depth(), 12);

        assert_eq!(forth.pop_int().unwrap(),  4); // 12 3 /MOD \\  0  4
        assert_eq!(forth.pop_int().unwrap(),  0);

        assert_eq!(forth.pop_int().unwrap(),  3); // 11 3 /MOD \\  2  3
        assert_eq!(forth.pop_int().unwrap(),  2);

        assert_eq!(forth.pop_int().unwrap(), 10); // 10 1 /MOD \\  0 10
        assert_eq!(forth.pop_int().unwrap(),  0);

        assert_eq!(forth.pop_int().unwrap(),  3); // 10 3 /MOD \\  1  3
        assert_eq!(forth.pop_int().unwrap(),  1);

        assert_eq!(forth.pop_int().unwrap(), -2); // -5 2 /MOD \\ -1 -2
        assert_eq!(forth.pop_int().unwrap(), -1);

        assert_eq!(forth.pop_int().unwrap(),  2); //  5 2 /MOD \\  1  2
        assert_eq!(forth.pop_int().unwrap(),  1);
    }

    #[test]
    fn depth() {
        let mut forth = ToyForth::new();

        forth.interpret("DEPTH").unwrap();
        assert_eq!(forth.pop_int().unwrap(), 0);

        forth.interpret("1 DEPTH").unwrap();
        assert_eq!(forth.pop_int().unwrap(), 1);

        forth.interpret("2 3 DEPTH").unwrap();
        assert_eq!(forth.pop_int().unwrap(), 3);
    }

    #[test]
    fn pick() {
        let mut forth = ToyForth::new();

        forth.interpret("1 2 3").unwrap(); // load stack

        forth.interpret("0 PICK").unwrap();  // 0 PICK == DUP
        assert_eq!(forth.stack_depth(), 4);
        assert_eq!(forth.pop_int().unwrap(), 3);

        forth.interpret("1 PICK").unwrap();  // 1 PICK == OVER
        assert_eq!(forth.stack_depth(), 4);
        assert_eq!(forth.pop_int().unwrap(), 2);

        forth.interpret("2 PICK").unwrap();
        assert_eq!(forth.stack_depth(), 4);
        assert_eq!(forth.pop_int().unwrap(), 1);
    }

    #[test]
    fn roll_and_rot() {
        let mut forth = ToyForth::new();

        fn check_eq(forth: &ToyForth, vals: &[isize]) {
            assert_eq!(forth.dstack,
                       vals.iter().map(
                           |x| Cell::int(*x as i32)
                        ).collect::<Vec<Cell>>());
        }

        forth.interpret("0 1 2 3 4 5 6 7").unwrap();  // load stack
        forth.interpret("4 ROLL").unwrap(); // ( 0  1  2 *3* 4  5  6  7 -- 0  1  2 *4* 5  6  7  3 )
        check_eq(&forth, &[0,1,2,4,5,6,7,3]);

        forth.interpret("2 ROLL").unwrap(); // ( 0  1  2  4  5 *6* 7  3 -- 0  1  2  4  5 *7* 3  6 )
        check_eq(&forth, &[0,1,2,4,5,7,3,6]);

        forth.interpret("6 ROLL").unwrap(); // ( 0 *1* 2  4  5  7  3  6 -- 0 *2* 4  5  7  3  6  1 )
        check_eq(&forth, &[0,2,4,5,7,3,6,1]);

        forth.interpret("ROT").unwrap();    // ( 0  2  4  5  7 *3* 6  1 -- 0  2  4  5  7 *6* 1  3 )
        check_eq(&forth, &[0,2,4,5,7,6,1,3]);
    }

    #[test]
    fn qdup_duplicates_non_zeros() {
        let mut forth = ToyForth::new();

        forth.interpret("123 ?DUP").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), 123);
        assert_eq!(forth.pop_int().unwrap(), 123);

        forth.interpret("-5 ?DUP").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), -5);
        assert_eq!(forth.pop_int().unwrap(), -5);

        forth.interpret("0 ?DUP").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 0);
    }

    #[test]
    fn colon_noname() {
        let mut forth = ToyForth::new();

        let next_xt = forth.mark_code();

        forth.interpret(":NONAME 3 + ;").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_xt().unwrap(), next_xt);

        forth.interpret(":NONAME 5 + ; 2 SWAP EXECUTE").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 7);
    }

    #[test]
    fn postpone() {
        let mut forth = ToyForth::new();

        forth.interpret("\
: GT1 123 ;
\\ { ' GT1 EXECUTE -> 123 }
\\ { : GT2 ['] GT1 ; IMMEDIATE -> }
\\ { GT2 EXECUTE -> 123 }
\\ HERE 3 C, CHAR G C, CHAR T C, CHAR 1 C, CONSTANT GT1STRING
\\ HERE 3 C, CHAR G C, CHAR T C, CHAR 2 C, CONSTANT GT2STRING
\\ { GT1STRING FIND -> ' GT1 -1 }
\\ { GT2STRING FIND -> ' GT2 1 }
\\ ( HOW TO SEARCH FOR NON-EXISTENT WORD? )
\\ { : GT3 GT2 LITERAL ; -> }
\\ { GT3 -> ' GT1 }
\\ { GT1STRING COUNT -> GT1STRING CHAR+ 3 }

: GT4 POSTPONE GT1 ; IMMEDIATE
: GT5 GT4 ;
GT5
").unwrap();

        forth.print_word_code("GT1");
        forth.print_word_code("GT4");
        forth.print_word_code("GT5");

        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 123);

        forth.interpret("\
: GT6 345 ; IMMEDIATE
: GT7 POSTPONE GT6 ;
GT7
").unwrap();

        forth.print_word_code("GT6");
        forth.print_word_code("GT7");

        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 345);

        forth.print_word_code("GT6");
        forth.print_word_code("GT7");
    }

    #[test]
    fn defer_and_related() {
        let mut forth = ToyForth::new();

        // Test basic DEFER, DEFER!, and DEFER@ words
        forth.interpret("\
DEFER defer3
' * ' defer3 DEFER!
2 3 defer3
' defer3 DEFER@
").unwrap();

        let star_xt = forth.lookup_word("*").unwrap();
        let plus_xt = forth.lookup_word("+").unwrap();
        let minus_xt = forth.lookup_word("-").unwrap();

        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_xt().unwrap(), star_xt);
        assert_eq!(forth.pop_int().unwrap(), 6);


        // Test interpretation semantics of ACTION-OF
        forth.interpret("ACTION-OF defer3").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_xt().unwrap(), star_xt);


        // Test compilation semantics of ACTION-OF
        forth.interpret("\
: action-of-defer3 ACTION-OF defer3 ;
").unwrap();
        assert_eq!(forth.stack_depth(), 0);

        forth.interpret("\
: foo 123 ;
action-of-defer3 foo
").unwrap();

        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), 123);
        assert_eq!(forth.pop_xt().unwrap(), star_xt);


        // Test: interpretation semantics of IS
        forth.interpret("\
' + IS defer3
ACTION-OF defer3
' defer3 DEFER@").unwrap();

        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_xt().unwrap(), plus_xt);
        assert_eq!(forth.pop_xt().unwrap(), plus_xt);

        // Test: compilation semantics of IS
        forth.interpret("\
: is-defer3 IS defer3 ;
' - is-defer3 ACTION-OF defer3
").unwrap();

        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_xt().unwrap(), minus_xt);
    }

    #[test]
    fn equal_and_not_equal_work_for_xt_and_st() {
        let mut forth = ToyForth::new();

        forth.interpret("' parse ' parse =").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop().unwrap(), Cell::true_value());

        forth.interpret("' parse ' word =").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop().unwrap(), Cell::false_value());

        forth.interpret("' parse ' parse <>").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop().unwrap(), Cell::false_value());

        forth.interpret("' parse ' * <>").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop().unwrap(), Cell::true_value());
    }

    #[test]
    fn case_switches() {
        let mut forth = ToyForth::new();

        forth.interpret("NOP").unwrap();
        let default_rstack_depth = forth.rstack_depth();

        forth.interpret("\
: cs1 CASE 1 OF 111 ENDOF
   2 OF 222 ENDOF
   3 OF 333 ENDOF
   >R 999 R>
   ENDCASE
;").unwrap();

        forth.print_word_code("cs1");

        forth.interpret("1 cs1").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 111);
        assert_eq!(forth.cstack_depth(), 0);
        assert_eq!(forth.rstack_depth(), default_rstack_depth);

        forth.interpret("2 cs1").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 222);
        assert_eq!(forth.cstack_depth(), 0);
        assert_eq!(forth.rstack_depth(), default_rstack_depth);

        forth.interpret("3 cs1").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 333);
        assert_eq!(forth.cstack_depth(), 0);
        assert_eq!(forth.rstack_depth(), default_rstack_depth);

        forth.interpret("4 cs1").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 999);
        assert_eq!(forth.cstack_depth(), 0);
        assert_eq!(forth.rstack_depth(), default_rstack_depth);

        forth.interpret("-1501 cs1").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 999);
        assert_eq!(forth.cstack_depth(), 0);
        assert_eq!(forth.rstack_depth(), default_rstack_depth);

        forth.interpret("17 cs1").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 999);
        assert_eq!(forth.cstack_depth(), 0);
        assert_eq!(forth.rstack_depth(), default_rstack_depth);
    }

    #[test]
    fn memory_allocation() {
        let mut forth = ToyForth::new();

        forth.interpret("\
HERE 1 ALLOT HERE
CONSTANT 2ND
CONSTANT 1ST

1ST 2ND U<
").unwrap();

        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop().unwrap(), Cell::bool(true));

        forth.interpret("1ST CELL+ 2ND =").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop().unwrap(), Cell::bool(true));

        forth.interpret("16 , 2ND @").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 16);
    }

    #[test]
    fn create_does_and_body() {
        let mut forth = ToyForth::new();

        forth.interpret("\
: MYVAR CREATE , ;
").unwrap();

        forth.interpret("\
HERE CONSTANT 1ST   \\ grab current top of data addresses
17 MYVAR FOO        \\ define variable using MYVAR

1ST FOO =           \\ check that FOO was defined at previous top of data address

FOO @               \\ access values via FOO and 1ST
1ST @
").unwrap();

        assert_eq!(forth.stack_depth(), 3);
        assert_eq!(forth.pop_int().unwrap(), 17);
        assert_eq!(forth.pop_int().unwrap(), 17);
        assert_eq!(forth.pop_int().unwrap(), -1);

        forth.interpret("\
: MYCONST CREATE , DOES> @ ;
").unwrap();

        forth.print_word_code("MYCONST");

        assert_eq!(forth.stack_depth(), 0);

        forth.interpret("23 MYCONST C23
C23
").unwrap();

        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 23);

        forth.print_word_code("FOO");

        forth.interpret("' FOO >BODY 1ST =").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), -1);
    }

    #[test]
    fn value_and_to() {
        let mut forth = ToyForth::new();

        // from https://forth-standard.org/standard/testsuite#test:core:VALUE

        forth.interpret("\
 111 VALUE v1
-999 VALUE v2").unwrap();
        assert_eq!(forth.stack_depth(), 0);

        forth.interpret("v1").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 111);

        forth.interpret("v2").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), -999);

        forth.interpret("222 to v1").unwrap();
        assert_eq!(forth.stack_depth(), 0);

        forth.interpret("v1").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 222);

        forth.interpret(": vd1 v1 ;").unwrap();
        assert_eq!(forth.stack_depth(), 0);

        forth.interpret("vd1").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 222);

        forth.interpret("\
212 TO v1
vd1").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 212);

        forth.print_word_code("TO");

        forth.interpret(": vd2 TO v2 ; .S").unwrap();
        forth.print_word_code("vd2");
        assert_eq!(forth.stack_depth(), 0);

        forth.interpret("v2").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), -999);

        forth.interpret("-333 vd2").unwrap();
        assert_eq!(forth.stack_depth(), 0);

        forth.interpret("v2").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), -333);

        forth.interpret("v1").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 212);

        forth.interpret("vd1").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 212);
    }

    #[test]
    fn two_word_stack_functions() {
        let mut forth = ToyForth::new();

        forth.interpret("NOP").unwrap();
        let default_rstack_depth = forth.rstack_depth();

        forth.interpret("1 2 3 2DROP .S").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 1);

        forth.interpret("1 2 3 2DUP").unwrap();
        assert_eq!(forth.stack_depth(), 5);
        assert_eq!(forth.pop_int().unwrap(), 3);
        assert_eq!(forth.pop_int().unwrap(), 2);
        assert_eq!(forth.pop_int().unwrap(), 3);
        assert_eq!(forth.pop_int().unwrap(), 2);
        assert_eq!(forth.pop_int().unwrap(), 1);

        forth.interpret("0 1 2 3 2OVER").unwrap();
        assert_eq!(forth.stack_depth(), 6);
        assert_eq!(forth.pop_int().unwrap(), 1);
        assert_eq!(forth.pop_int().unwrap(), 0);
        assert_eq!(forth.pop_int().unwrap(), 3);
        assert_eq!(forth.pop_int().unwrap(), 2);
        assert_eq!(forth.pop_int().unwrap(), 1);
        assert_eq!(forth.pop_int().unwrap(), 0);

        forth.interpret("0 1 2 3 2SWAP").unwrap();
        assert_eq!(forth.stack_depth(), 4);
        assert_eq!(forth.pop_int().unwrap(), 1);
        assert_eq!(forth.pop_int().unwrap(), 0);
        assert_eq!(forth.pop_int().unwrap(), 3);
        assert_eq!(forth.pop_int().unwrap(), 2);

        forth.interpret(": FOO 0 1 2>R 2 3 2R> ; FOO").unwrap();
        assert_eq!(forth.stack_depth(), 4);
        assert_eq!(forth.rstack_depth(), default_rstack_depth);
        assert_eq!(forth.pop_int().unwrap(), 1);
        assert_eq!(forth.pop_int().unwrap(), 0);
        assert_eq!(forth.pop_int().unwrap(), 3);
        assert_eq!(forth.pop_int().unwrap(), 2);

        forth.interpret(": BAR 0 1 2>R 2R@ 2R> ; BAR").unwrap();
        assert_eq!(forth.stack_depth(), 4);
        assert_eq!(forth.rstack_depth(), default_rstack_depth);
        assert_eq!(forth.pop_int().unwrap(), 1);
        assert_eq!(forth.pop_int().unwrap(), 0);
        assert_eq!(forth.pop_int().unwrap(), 1);
        assert_eq!(forth.pop_int().unwrap(), 0);

        forth.interpret("CREATE TWO-AT 2 ALLOT").unwrap();
        forth.interpret("0 1 2 3 TWO-AT 2!").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), 1);
        assert_eq!(forth.pop_int().unwrap(), 0);

        forth.interpret("TWO-AT @").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 3);

        forth.interpret("TWO-AT CELL+ @").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 2);

        forth.interpret("TWO-AT 2@").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), 3);
        assert_eq!(forth.pop_int().unwrap(), 2);
    }

    #[test]
    fn callot_cshrink_and_clength() {
        let mut forth = ToyForth::new();

        forth.interpret("\
VARIABLE st1
100 CALLOT st1 !
").unwrap();

        forth.interpret("st1 @ CLENGTH").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 100);

        forth.interpret("st1 @ 50 CSHRINK CLENGTH").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 50);

        forth.interpret("st1 @ 150 CSHRINK CLENGTH").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 100);

        forth.interpret("st1 @ CHAR+ CLENGTH").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_int().unwrap(), 99);
    }

    #[test]
    fn char_bang_and_char_at_work_on_string_spaces_and_addresses() {
        let mut forth = ToyForth::new();

        forth.interpret("\
VARIABLE ch1
VARIABLE st1

1 CALLOT st1 !

BL st1 @ C!
BL ch1 C!

ch1 C@
st1 @ C@
").unwrap();

        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), ' ' as i32);
        assert_eq!(forth.pop_int().unwrap(), ' ' as i32);
    }

    #[test]
    fn bang_and_at_work_on_string_spaces_and_addresses() {
        let mut forth = ToyForth::new();

        forth.interpret("\
VARIABLE ch1
VARIABLE st1

1 CALLOT st1 !

BL st1 @ !
BL ch1 !

ch1 @
st1 @ @
").unwrap();

        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), ' ' as i32);
        assert_eq!(forth.pop_int().unwrap(), ' ' as i32);
    }

    #[test]
    fn unsigned_dot_words() {
        let mut forth = ToyForth::new();
        let outv = Rc::new(RefCell::new(Vec::<u8>::new()));

        forth.capture_interpret("1 U.", outv.clone()).unwrap();
        {
            let mut outb = outv.borrow_mut();
            let s = std::str::from_utf8(&outb).unwrap();
            eprintln!("output is\n{}", s);
            assert_eq!(s, "1 ");
            outb.clear();
        }

        forth.capture_interpret("-1 U.", outv.clone()).unwrap();
        {
            let mut outb = outv.borrow_mut();
            let s = std::str::from_utf8(&outb).unwrap();
            eprintln!("output is\n{}", s);
            assert_eq!(s, format!("{} ", Cell::INT_MASK));
            outb.clear();
        }

        forth.capture_interpret("-100 U.", outv.clone()).unwrap();
        {
            let mut outb = outv.borrow_mut();
            let s = std::str::from_utf8(&outb).unwrap();
            eprintln!("output is\n{}", s);
            assert_eq!(s, format!("{} ", Cell::UINT_MAX-99));
            outb.clear();
        }

        forth.capture_interpret("DECIMAL 20 HEX U.", outv.clone()).unwrap();
        {
            let mut outb = outv.borrow_mut();
            let s = std::str::from_utf8(&outb).unwrap();
            eprintln!("output is\n{}", s);
            assert_eq!(s, "14 ");
            outb.clear();
        }

        forth.capture_interpret("23 5 U.R", outv.clone()).unwrap();
        {
            let mut outb = outv.borrow_mut();
            let s = std::str::from_utf8(&outb).unwrap();
            eprintln!("output is\n{}", s);
            assert_eq!(s, "   23");
            outb.clear();
        }
    }

    #[test]
    fn double_cell_operations() {
        let mut forth = ToyForth::new();

        forth.interpret("1 S>D").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), 0);
        assert_eq!(forth.pop_int().unwrap(), 1);

        forth.interpret("-1 S>D").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), -1);
        assert_eq!(forth.pop_int().unwrap(), -1);

        forth.interpret("100000 100000 100 */MOD").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), 100_000_000);
        assert_eq!(forth.pop_int().unwrap(), 0);

        forth.interpret("1 1 M*").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), 0);
        assert_eq!(forth.pop_int().unwrap(), 1);

        forth.interpret("-1 1 M*").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), -1);
        assert_eq!(forth.pop_int().unwrap(), -1);

        forth.interpret("1 -1 M*").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), -1);
        assert_eq!(forth.pop_int().unwrap(), -1);

        forth.interpret("-1 -1 M*").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), 0);
        assert_eq!(forth.pop_int().unwrap(), 1);

        forth.interpret("100000 100000 M*").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), 4);
        assert_eq!(forth.pop_int().unwrap(), -737418240);

        forth.interpret("-1 -1 UM*").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), -2);
        assert_eq!(forth.pop_int().unwrap(),  1);

        forth.interpret("100000 100000 UM*").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), 4);
        assert_eq!(forth.pop_int().unwrap(), -737418240);

        forth.interpret("10 S>D 7 FM/MOD").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), 1);
        assert_eq!(forth.pop_int().unwrap(), 3);

        forth.interpret("-10 S>D 7 FM/MOD").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), -2);
        assert_eq!(forth.pop_int().unwrap(),  4);

        forth.interpret("10 S>D -7 FM/MOD").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), -2);
        assert_eq!(forth.pop_int().unwrap(), -4);

        forth.interpret("-10 S>D -7 FM/MOD").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(),  1);
        assert_eq!(forth.pop_int().unwrap(), -3);

        forth.interpret("10 S>D 7 SM/REM").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), 1);
        assert_eq!(forth.pop_int().unwrap(), 3);

        forth.interpret("-10 S>D 7 SM/REM").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), -1);
        assert_eq!(forth.pop_int().unwrap(), -3);

        forth.interpret("10 S>D -7 SM/REM").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(), -1);
        assert_eq!(forth.pop_int().unwrap(),  3);

        forth.interpret("-10 S>D -7 SM/REM").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(),  1);
        assert_eq!(forth.pop_int().unwrap(), -3);

        // FIXME: need better UM/MOD tests
        forth.interpret("10 S>D 7 UM/MOD").unwrap();
        assert_eq!(forth.stack_depth(), 2);
        assert_eq!(forth.pop_int().unwrap(),  1);
        assert_eq!(forth.pop_int().unwrap(),  3);
    }

    #[test]
    fn can_offset_var_addresses() {
        let mut forth = ToyForth::new();

        // variable addresses allow both positive and negative offsets within the var address space

        forth.interpret("\
VARIABLE a-addr1
VARIABLE a-addr2
").unwrap();

        let here = forth.here();
        forth.interpret("\
HERE a-addr1 !
10 ALLOT 
a-addr1 @ 5 ADDR+ DUP a-addr2 !").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_var_addr().unwrap(), VarAddr(here.0 + 5));

        forth.interpret("a-addr2 @ 2 ADDR-").unwrap();
        assert_eq!(forth.stack_depth(), 1);
        assert_eq!(forth.pop_var_addr().unwrap(), VarAddr(here.0 + 3));

        forth.interpret("a-addr2 @ 5 ADDR+").unwrap();
        assert_eq!(forth.pop_var_addr().unwrap(), VarAddr(here.0 + 10));

        {
            let err = forth.interpret("a-addr2 @ 6 ADDR+").unwrap_err();
            assert!(matches!(err, ForthError::InvalidAddressAndOffset(Addr::Var(VarAddr(_)),_)));
            if let ForthError::InvalidAddressAndOffset(Addr::Var(VarAddr(addr)),off) = err {
                assert_eq!(addr, here.0+5);
                assert_eq!(off, 6);
            }
        }
    }

    #[test]
    fn can_offset_char_addresses() {
        let mut forth = ToyForth::new();

        // character/string/ST addresses allow both positive and negative offsets within the var
        // address space

        forth.interpret("\
VARIABLE c-addr1
VARIABLE c-addr2
").unwrap();

        let char_here = forth.char_here();
        {
            forth.interpret("100 CALLOT c-addr1 ! c-addr1 @").unwrap();
            assert_eq!(forth.stack_depth(), 1);
            let st = forth.pop_str().unwrap();
            assert!(matches!(st, ST::Allocated(_)));
            assert_eq!(st.addr(), char_here);
            assert_eq!(st.len(), 100);
        }

        {
            forth.interpret("c-addr1 @ 25 ADDR+ DUP c-addr2 !").unwrap();
            assert_eq!(forth.stack_depth(), 1);
            let st = forth.pop_str().unwrap();
            assert!(matches!(st, ST::Allocated(_)));
            assert_eq!(st.addr(), char_here+25);
            assert_eq!(st.len(), 75);
        }

        {
            let err = forth.interpret("c-addr1 @ -10 ADDR+").unwrap_err();
            assert!(matches!(err, ForthError::InvalidAddressAndOffset(Addr::Char(_),_)));
            if let ForthError::InvalidAddressAndOffset(Addr::Char(st),off) = err {
                assert_eq!(st.addr(), char_here);
                assert_eq!(st.len(), 100);
                assert_eq!(off, -10);
            }
        }

        /* check that ADDR+ works for non-allocated strings (eg: PAD) */
        {
            forth.interpret("PAD c-addr1 ! c-addr1 @").unwrap();
            assert_eq!(forth.stack_depth(), 1);
            let st = forth.pop_str().unwrap();
            assert!(matches!(st, ST::PadSpace(_)));
            assert_eq!(st.addr(), 0);
            assert_eq!(st.len(), 255);
        }

        {
            forth.interpret("c-addr1 @ 25 ADDR+").unwrap();
            assert_eq!(forth.stack_depth(), 1);
            let st = forth.pop_str().unwrap();
            assert!(matches!(st, ST::PadSpace(_)));
            assert_eq!(st.addr(), 25);
            assert_eq!(st.len(), 255-25);
        }
    }
}

