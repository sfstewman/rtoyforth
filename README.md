# rtoyforth #

## Introduction ##

`rtoyforth` is a small Forth interpreter as a project to learn Rust
and write something close to compatible with ANS Forth.  It has most
of the core Forth words, but has several oddities.

This Forth system uses bytecode instead of direct or indirect threading,
but a future version may use indirect threading.  The compiler does
some amount of inlining.


## Quirks and limitations ##

The cell size is 32-bits.  Single cell integers are signed two's
complement 31-bit quantities.

In a probably misguided effort to write a safer Forth, the address space
is fragmented: executable code is separate from strings and variables.

Most ambiguous conditions should result in errors.


## Future plans ##

- The overall system needs more Forth words, including the floating
  point set, better execution control (eg: THROW and CATCH words).

- Make the system easier to embed into other programs.

- Compiler: translate the stack machine into a register machine,
  experiment with SSA optimizations.  Either translate SSA IR back to
  a stack machine or try emitting actual machine code.


