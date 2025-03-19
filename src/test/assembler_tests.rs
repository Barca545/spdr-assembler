use crate::{interner::intern, Compiler, Ty, VarDecl};
use spdr_isa::{
  opcodes::{CmpFlag, OpCode},
  program::Program,
  registers::{EQ, LOOP},
};
use spdr_vm::vm::VM;
use std::{any::Any, io, path::PathBuf};

#[test]
fn load_header() {
  let mut compiler = Compiler::new("", io::stdout(),);
  compiler.read_header(PathBuf::from("../spdr-assembler/src/test/test_header.hd",),);

  let decl_1 = match compiler.table.get(&intern("foo",),).unwrap().ty {
    Ty::ExternalFunction(idx,) => idx,
    _ => panic!(),
  };
  assert_eq!(decl_1, 0);

  let decl_2 = match compiler.table.get(&intern("bar",),).unwrap().ty {
    Ty::ExternalFunction(idx,) => idx,
    _ => panic!(),
  };
  assert_eq!(decl_2, 1);
}

#[test]
fn eat_instruction_works() {
  let src = include_str!("./full_compilation_test.spdr");
  let p = Compiler::new(src, io::stdout(),).eat_compile();
  assert_eq!(p.as_slice(), []);
}

#[test]
#[rustfmt::skip]
fn compile_load_cpy() {
  let p = Compiler::new("Load $14 1 Copy $15 $12",io::stdout()).compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);
  
  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 4
    OpCode::Load.into(), 14, 0, 0, 128, 63,
    OpCode::Copy.into(), 15, 12,
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);
}

#[test]
#[rustfmt::skip]
fn compile_memcpy_rmem_wmem() {
  let p = Compiler::new("wmem $14 $15 1 $16 memcpy $55 $50 rmem $255 $40 1 $20",io::stdout()).compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 4
    OpCode::WMem.into(), 14, 15, 0, 0, 128, 63, 16,
    OpCode::MemCpy.into(), 55, 50,
    OpCode::RMem.into(), 255, 40, 0, 0, 128, 63, 20,
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);
}

#[test]
#[rustfmt::skip]
fn compile_alloc_dealloc() {
  let p = Compiler::new("Alloc $14 $90 Dealloc", io::stdout()).compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 4
    OpCode::Alloc.into(), 14,   90,
    OpCode::Dealloc.into(),
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);
}

#[test]
#[rustfmt::skip]
fn compile_arith() {
  // ADDII
  let p = Compiler::new("ADD $14 15 10", io::stdout(),).compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5  
    OpCode::Load.into(), 14, 0, 0, 200, 65,  
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);

  // ADDRI
  let p = Compiler::new("ADD $14 $15 10", io::stdout(),).compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5  
    OpCode::AddRI.into(), 14, 15, 0, 0, 32, 65,  
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);

  // ADDRR
  let p = Compiler::new("ADD $14 $14 $15", io::stdout(),).compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5  
    OpCode::AddRR.into(), 14, 14, 15,  
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);

  // SUBII
  let p = Compiler::new("SUB $14 10 30", io::stdout(),).compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5  
    OpCode::Load.into(), 14, 0, 0, 160, 193,  
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);

  // SUBIR
  let p = Compiler::new("SUB $15 90 $14", io::stdout(),).compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5  
    OpCode::RvSubRI.into(), 15, 14, 0, 0, 180, 66,  
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);

  // SUBRI
  let p = Compiler::new("SUB $15 $14 90", io::stdout(),).compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5  
    OpCode::SubRI.into(), 15, 14, 0, 0, 180, 66,  
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);

  // SUBRR
  let p = Compiler::new("SUB $15 $14 $14", io::stdout(),).compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5  
    OpCode::SubRR.into(), 15, 14, 14,  
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);

  // MULII
  let p = Compiler::new("MUL $14 10 29.32", io::stdout(),).compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5  
    OpCode::Load.into(), 14, 154, 153, 146, 67,  
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);

  // MULRI
  let p = Compiler::new("MUL $15 $14 10", io::stdout(),).compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5  
    OpCode::MulRI.into(), 15, 14, 0, 0, 32, 65,  
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);

  // MULRR
  let p = Compiler::new("MUL $15 $14 $14", io::stdout(),).compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5  
    OpCode::MulRR.into(), 15, 14, 14,  
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);

  // DIVII
  let p = Compiler::new("DIV $14 32.54 653", io::stdout(),).compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5  
    OpCode::Load.into(), 14, 42, 28, 76, 61,  
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);

  // DIVRI
  let p = Compiler::new("DIV $15 $14 90", io::stdout(),).compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5  
    OpCode::DivRI.into(), 15, 14, 0, 0, 180, 66,  
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);

  // DIVIR
  let p = Compiler::new("DIV $15 90 $14", io::stdout(),).compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5  
    OpCode::RvDivRI.into(), 15, 14, 0, 0, 180, 66,  
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);

  // DIVRR
  let p = Compiler::new("DIV $15 $14 $14", io::stdout(),).compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5  
    OpCode::DivRR.into(), 15, 14, 14,  
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);

  // POWII
  let p = Compiler::new("POW $14 76.253216 3.7", io::stdout(),).compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5  
    OpCode::Load.into(), 14, 127, 144, 12, 75,  
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);

  // POWRI
  let p = Compiler::new("POW $15 $14 90", io::stdout(),).compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5  
    OpCode::PowRI.into(), 15, 14, 0, 0, 180, 66,  
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);

  // POWIR
  let p = Compiler::new("POW $15 90 $14", io::stdout(),).compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5  
    OpCode::RvPowRI.into(), 15, 14, 0, 0, 180, 66,  
    OpCode::Hlt.into(),    
  ];
  assert_eq!(p.as_slice(), expected);

  // PowRR
  let p = Compiler::new("POW $15 $14 $14", io::stdout(),).compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(),  5,  0,  0,  0, // `main` starts on 5
    OpCode::PowRR.into(),  15,  14,  14,
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);
}

#[test]
#[rustfmt::skip]
fn compile_loop() {
  // Test plain loop compilation
  let mut c = Compiler::new("Loop {ADD $14 $30 1}", io::stdout());
  let p = c.compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  // Check the output is accurate
  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
    OpCode::AddRI.into(), 14, 30, 0, 0, 128, 63,
    OpCode::Jmp.into(), 5, 0, 0, 0, // Jump to 5
    OpCode::Hlt.into()
  ];
  assert_eq!(p.as_slice(), expected);

  // Test plain loop compilation with function at beginning
  let mut c = Compiler::new("Loop {ADD $14 $30 1} FN foo {SUB $16 $94 $233 RET 1}", io::stdout());
  let p = c.compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  // Check the output is accurate
  let expected = [
    OpCode::Jmp.into(), 11, 0, 0, 0, // `main` starts on 11
    OpCode::SubRR.into(), 16, 94, 233,
    OpCode::Ret.into(), 1,
    OpCode::AddRI.into(), 14, 30, 0, 0, 128, 63,
    OpCode::Jmp.into(), 11, 0, 0, 0,  // Jump to 11
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);
}

#[test]
#[rustfmt::skip]
fn compile_while_loop(){
  // Test while loop compilation when `true`
  let mut c = Compiler::new("while true {noop noop noop}",io::stdout());
  let p = c.compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  // Check the output is accurate
  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
    OpCode::Noop.into(),
    OpCode::Noop.into(),
    OpCode::Noop.into(),
    OpCode::Jmp.into(), 5, 0, 0, 0, 
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);

  // Test While loop compilation when `false`
  let p = Compiler::new("while false {noop noop noop}", io::stdout()).compile();
  
  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);

  // Test While loop compilation with real condition
  let mut c = Compiler::new("while EQ $15 1 {noop noop noop}", io::stdout());
  let p = c.compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
    OpCode::Jmp.into(), 13, 0, 0, 0, // Jump to 13
    OpCode::Noop.into(),
    OpCode::Noop.into(),
    OpCode::Noop.into(),
    OpCode::CmpRI.into(), CmpFlag::Eq.into(), 15, 0, 0, 128, 63,
    OpCode::Jnz.into(), EQ as u8, 10, 0, 0, 0, // Jump to 10
    OpCode::Hlt.into()
  ];
  assert_eq!(p.as_slice(), expected);

  // Test While loop compiles when binary contains function
  let mut c = Compiler::new("WHILE EQ $15 1 {ADD $15 $15 $54 } FN foo {NOOP NOOP}", io::stdout());
  let p = c.compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);
  
  let expected = [
    OpCode::Jmp.into(), 7, 0, 0, 0, // `main` starts on 7
    // foo
    OpCode::Noop.into(),
    OpCode::Noop.into(),
    // Main 
    OpCode::Jmp.into(), 16, 0, 0, 0,// Jump to 16
    OpCode::AddRR.into(), 15, 15, 54,
    OpCode::CmpRI.into(), CmpFlag::Eq.into(), 15, 0, 0, 128, 63,
    OpCode::Jnz.into(), EQ as u8, 12, 0, 0, 0, // Jump to 12
    OpCode::Hlt.into()
  ];
  assert_eq!(p.as_slice(), expected);
}

#[test]
#[rustfmt::skip]
fn compile_for_loop(){
  // Test For loop compilation
  let mut c = Compiler::new("for i in 0..9 {noop noop noop}", io::stdout());
  let p = c.compile();   

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
    OpCode::Load.into(), LOOP as u8, 0, 0, 0, 0,
    OpCode::Noop.into(),
    OpCode::Noop.into(),
    OpCode::Noop.into(),
    OpCode::AddRI.into(), LOOP as u8, LOOP as u8, 0, 0, 128, 63,
    OpCode::CmpRI.into(), CmpFlag::Eq.into(), LOOP as u8, 0, 0, 0, 65,
    OpCode::Jz.into(), EQ as u8, 11, 0, 0, 0, // Jump to 11
    OpCode::Hlt.into(),
  ];

  assert_eq!(p.as_slice(), expected);

  // Test for loop compiles when binary has function
  let mut c = Compiler::new("FOR i IN 0..9 {NOOP NOOP NOOP} FN foo {NOOP NOOP}", io::stdout());
  let p = c.compile(); 

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p); 

  let expected = [
    OpCode::Jmp.into(), 7, 0, 0, 0, // `main` starts on 7
    // This is the function
    OpCode::Noop.into(),
    OpCode::Noop.into(),
    // This is main
    OpCode::Load.into(), LOOP as u8, 0, 0, 0, 0,
    OpCode::Noop.into(),
    OpCode::Noop.into(),
    OpCode::Noop.into(),
    OpCode::AddRI.into(), LOOP as u8, LOOP as u8, 0, 0, 128, 63,
    OpCode::CmpRI.into(), CmpFlag::Eq.into(), LOOP as u8, 0, 0, 0, 65,
    OpCode::Jz.into(), EQ as u8, 13, 0, 0, 0, // Jump to 13
    OpCode::Hlt.into(),
  ];

  // Check the output is accurate when binary contains a function
  assert_eq!(p.as_slice(), expected);
}

#[test]
#[rustfmt::skip]
fn compile_if_else() {
  // Compile IF with boolean true check
  // Compile ELSE
  let p = Compiler::new("IF true {Noop Noop Noop Noop} else {Add $15 0 1} Mul $16 1 1", io::stdout()).compile();
  
  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
    OpCode::Noop.into(),
    OpCode::Noop.into(),
    OpCode::Noop.into(),
    OpCode::Noop.into(),
    OpCode::Load.into(), 16, 0, 0, 128, 63, 
    OpCode::Hlt.into(),
  ];
  
  assert_eq!(p.as_slice(), expected);

  // Compile IF with boolean false check
  let p = Compiler::new("IF false {mul $54 0 1 } else {add $26 $17 1} add $46 0 1", io::stdout()).compile();
  
  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
    // Else Block
    OpCode::AddRI.into(), 26, 17, 0, 0, 128, 63,
    // Trailing expression
    OpCode::Load.into(), 46, 0, 0, 128, 63,
    OpCode::Hlt.into(),
  ];

  assert_eq!(p.as_slice(), expected);


  // Compile IF with runtime check
  // Compile ELSE IF
  let p = Compiler::new(
    "IF EQ $14 0 {Noop Noop Noop Noop} Else If GT $15 1 {add $26 0 1 Noop Noop Noop} Mul $14 $14 1 ",
    io::stdout())
  .compile();
  // If is failing likely because it is placing the jump location after the else

  assert_eq!(
    p.as_slice(),
    [
      OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5
      // IF expression
      OpCode::CmpRI.into(), CmpFlag::Eq.into(), 14, 0, 0, 0, 0,
      OpCode::Jz.into(), EQ as u8, 22, 0, 0, 0, // Jump to idx 22 if the comparison fails
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      // ELSE IF expression
      OpCode::CmpRI.into(), CmpFlag::Gt.into(), 15, 0, 0, 128, 63,
      OpCode::Jz.into(), EQ as u8, 44, 0, 0, 0, // Jump to idx 44 if the comparison fails
      OpCode::Load.into(), 26, 0, 0, 128, 63,
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::Noop.into(),
      OpCode::MulRI.into(), 14, 14, 0, 0, 128, 63,
      OpCode::Hlt.into(),
    ]
  );
}

#[test]
#[rustfmt::skip]
fn compile_when_single_function_defined(){
  let mut c = Compiler::new("Sub $54 $34 $65 FN foo {ADD $14 $14 $15 NOOP MUL $88 $87 $98 RET 0} Div $65 $58 $30", io::stdout());
  let p = c.compile();
  // Check the function pointer of `foo` is correct
  match c.table.get(&intern("foo")){
    Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [5, 0, 0, 0]),
    _ => panic!("Should be a function pointer"),
  }

  // Check the program is correct
  let expected = [
    OpCode::Jmp.into(), 16, 0, 0, 0, // `main`'s address is 16
    // Beginning of `lib`
    OpCode::AddRR.into(), 14, 14, 15,
    OpCode::Noop.into(),
    OpCode::MulRR.into(), 88, 87, 98,
    OpCode::Ret.into(), 0, 
    // Beginning of `main`
    OpCode::SubRR.into(), 54, 34, 65,
    OpCode::DivRR.into(), 65, 58, 30,
    OpCode::Hlt.into(),
  ];

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  assert_eq!(p.as_slice(), expected);
}

#[test]
#[rustfmt::skip]
fn compile_call_when_single_function_defined_before_calling(){
  let mut c = Compiler::new("Sub $54 $34 $65 fn foo {ADD $14 $14 $15 NOOP MUL $88 $87 $98 RET 0} Div $65 $58 $30 CALL foo", io::stdout());
  let p = c.compile();
  // Check the function pointer of `foo` is correct
  match c.table.get(&intern("foo")){
    Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [5, 0, 0, 0]),
    _ => panic!("Should be a function pointer"),
  }

  // Check the program is correct
  let expected = [
    OpCode::Jmp.into(), 16, 0, 0, 0, // `main`'s address is 16
    // Beginning of `lib`
    OpCode::AddRR.into(), 14, 14, 15,
    OpCode::Noop.into(),
    OpCode::MulRR.into(), 88, 87, 98,
    OpCode::Ret.into(), 0,
    // Beginning of `main`
    OpCode::SubRR.into(), 54, 34, 65,
    OpCode::DivRR.into(), 65, 58, 30,
    OpCode::Call.into(), 5, 0, 0, 0, // Call 5
    OpCode::Hlt.into(),
  ];

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  assert_eq!(p.as_slice(), expected);
}

#[test]
#[rustfmt::skip]
fn compile_when_single_function_defined_after_call(){
  let mut c = Compiler::new("CALL foo SUB $54 $34 $65 CALL foo FN foo {ADD $14 $14 $15 NOOP MUL $88 $87 $98 RET 0} DIV $65 $58 $30 CALL foo", io::stdout());
  let p = c.compile();
  // Check the function pointer of `foo` is correct
  match c.table.get(&intern("foo")){
    Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [5, 0, 0, 0]),
    _ => panic!("Should be a function pointer"),
  }

  let expected = [
    OpCode::Jmp.into(), 16, 0, 0, 0, // `main`'s address is 16
    // Beginning of `lib`
    OpCode::AddRR.into(), 14, 14, 15,
    OpCode::Noop.into(),
    OpCode::MulRR.into(), 88, 87, 98,
    OpCode::Ret.into(), 0, 
    // Beginning of `main`
    OpCode::Call.into(), 5, 0, 0, 0, // Call 5
    OpCode::SubRR.into(), 54, 34, 65,
    OpCode::Call.into(), 5, 0, 0, 0, // Call 5
    OpCode::DivRR.into(), 65, 58, 30,
    OpCode::Call.into(), 5, 0, 0, 0, // Call 5
    OpCode::Hlt.into(),
  ];

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  assert_eq!(p.as_slice(), expected);
}

#[test]
#[rustfmt::skip]
fn compile_when_single_function_contains_recursion(){
  let mut c = Compiler::new("CALL foo FN foo {ADD $14 $14 $15 CALL foo NOOP MUL $88 $87 $98 RET 0} DIV $65 $58 $30 CALL foo", io::stdout());
  let p = c.compile();
  // Check the function pointer of `foo` is correct
  match c.table.get(&intern("foo")){
    Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [5, 0, 0, 0]),
    _ => panic!("Should be a function pointer"),
  }

  let expected = [
    OpCode::Jmp.into(), 21, 0, 0, 0, // `main`'s address is 21
    // Beginning of `lib`
    OpCode::AddRR.into(), 14, 14, 15,
    OpCode::Call.into(), 5, 0, 0, 0, // Call 5
    OpCode::Noop.into(),
    OpCode::MulRR.into(), 88, 87, 98,
    OpCode::Ret.into(), 0,
    // Beginning of `main`
    OpCode::Call.into(), 5, 0, 0, 0, // Call 5
    OpCode::DivRR.into(), 65, 58, 30,
    OpCode::Call.into(), 5, 0, 0, 0, // Call 5
    OpCode::Hlt.into(),
  ];

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);
  
  assert_eq!(p.as_slice(), expected);

}

#[test]
#[rustfmt::skip]
fn compile_when_multiple_functions_defined(){
  let src = "FN foo {ADD $14 $60 $37 RET 3} FN bar {POW $67 $64 $75 RET 2}";
  let mut c = Compiler::new(src, io::stdout());
  let p = c.compile();

  // Check the function pointer of `foo` is correct
  let foo_fn_idx = &intern("foo");
  assert_eq!(foo_fn_idx, &0);
  match c.table.get(foo_fn_idx){
    Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [5, 0, 0, 0]),
    _ => panic!("Should be a function pointer"),
  }

  // Check the function pointer of `bar` is correct
  let bar_fn_idx = &intern("bar");
  assert_eq!(bar_fn_idx, &1);
  match c.table.get(bar_fn_idx){
    Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [11, 0, 0, 0]),
    _ => panic!("Should be a function pointer"),
  }

  let expected = [
    OpCode::Jmp.into(), 17, 0, 0, 0, // `main` starts at 17
    OpCode::AddRR.into(), 14, 60, 37, // `foo` starts at 5
    OpCode::Ret.into(), 3,
    OpCode::PowRR.into(), 67, 64, 75, // `bar` starts at 11
    OpCode::Ret.into(), 2,
    OpCode::Hlt.into(),
  ];

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  assert_eq!(p.as_slice(), expected);
}

#[test]
#[rustfmt::skip]
fn compile_call_when_multiple_functions_defined_before_calling(){
  let src = "FN foo {ADD $14 $60 $37 RET 3} FN bar {POW $67 $64 $75 RET 2} CALL foo CALL bar";
  let mut c = Compiler::new(src, io::stdout());
  let p = c.compile();
  
  // Check the function pointer of `foo` is correct
  let foo_fn_idx = &intern("foo");
  assert_eq!(foo_fn_idx, &0);
  match c.table.get(foo_fn_idx){
    Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [5, 0, 0, 0]),
    _ => panic!("Should be a function pointer"),
  }

  // Check the function pointer of `bar` is correct
  let bar_fn_idx = &intern("bar");
  assert_eq!(bar_fn_idx, &1);
  match c.table.get(bar_fn_idx){
    Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [11, 0, 0, 0]),
    _ => panic!("Should be a function pointer"),
  }

  let expected = [
    OpCode::Jmp.into(), 17, 0, 0, 0, // `main` starts at 17
    OpCode::AddRR.into(),  14, 60, 37, // `foo` starts at 5
    OpCode::Ret.into(), 3,
    OpCode::PowRR.into(), 67, 64, 75, // `bar` starts at 11
    OpCode::Ret.into(), 2,
    // Call foo
    OpCode::Call.into(), 5, 0, 0, 0,
    // Call bar
    OpCode::Call.into(), 11, 0, 0, 0,
    OpCode::Hlt.into(),
  ];

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  assert_eq!(p.as_slice(), expected);
}

#[test]
#[rustfmt::skip]
fn compile_when_multiple_functions_defined_after_call(){
  let mut c = Compiler::new("CALL bar CALL foo FN foo {ADD $14 $60 $37 RET 3} FN bar {POW $67 $64 $75 RET 2} CALL foo CALL bar", io::stdout());
  let p = c.compile();

  // Check the function pointer of `foo` is correct
  let foo_fn_idx = &intern("foo");
  assert_eq!(foo_fn_idx, &1);
  match c.table.get(foo_fn_idx){
    Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [5, 0, 0, 0]),
    _ => panic!("Should be a function pointer"),
  }

  // Check the function pointer of `bar` is correct
  let bar_fn_idx = &intern("bar");
  assert_eq!(bar_fn_idx, &0);
  match c.table.get(bar_fn_idx){
    Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [11, 0, 0, 0]),
    _ => panic!("Should be a function pointer"),
  }

  // Check the binary is correct
  let expected = [
    OpCode::Jmp.into(), 17, 0, 0, 0, // `main` starts at 17
    OpCode::AddRR.into(), 14, 60, 37, // `foo` starts at 5
    OpCode::Ret.into(), 3,
    OpCode::PowRR.into(), 67, 64, 75, // `bar` starts at 11
    OpCode::Ret.into(), 2,
    // Call bar
    OpCode::Call.into(), 11, 0, 0, 0,
    // Call foo
    OpCode::Call.into(), 5, 0, 0, 0,
    // Call foo
    OpCode::Call.into(), 5, 0, 0, 0,
    // Call bar
    OpCode::Call.into(), 11, 0, 0, 0,
    OpCode::Hlt.into(),
  ];
  
  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  assert_eq!(p.as_slice(), expected);
}

#[test]
#[should_panic = "\x1b[93mUNAVAILABLE FUNCTION NAME:\x1b[0m The name foo is already in use."]
fn function_errors_when_name_in_use() {
  // Test fuction name reuse fails
  let _ = Compiler::new("FN foo {ADD $14 $14 4} FN foo {NOOP NOOP}", io::stdout(),).compile();
}

#[test]
#[should_panic = "\x1b[93mUNDEFINED FUNCTION:\x1b[0m Cannot use foo (idx:5, ln:1, col:6) without defining it."]
fn function_errors_when_not_defined() {
  // Test fuction name reuse fails
  let _ = Compiler::new("CALL foo", io::stdout(),).compile();
}

#[test]
#[rustfmt::skip]
fn compile_syscall() {   
  let mut compiler = Compiler::new("syscall foo", io::stdout());
  compiler
    .read_header(PathBuf::from("../spdr-assembler/src/test/test_header.hd"),);

  let p = compiler.compile();

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
    OpCode::SysCall.into(), 0,
    OpCode::Hlt.into()
  ];

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  assert_eq!(p.as_slice(), expected);
}

#[test]
#[rustfmt::skip]
fn compile_push_pop() {
  let p = Compiler::new("Push $1 Push $1 Pop PopR $16", io::stdout()).compile();

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
    OpCode::Push.into(), 1, 
    OpCode::Push.into(), 1,
    OpCode::Pop.into(),
    OpCode::PopR.into(), 16,
    OpCode::Hlt.into(),
  ];

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  assert_eq!(p.as_slice(), expected);
}

#[test]
#[rustfmt::skip]
fn compile_eq() {
  // EQII
  let p = Compiler::new("eq 2 2", io::stdout()).compile();

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
    OpCode::Load.into(), EQ as u8, 1, 0, 0, 0, 
    OpCode::Hlt.into()
  ]; 

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  assert_eq!(p.as_slice(), expected);

  // EQIR
  let p = Compiler::new("eq $14 1", io::stdout()).compile();
  
  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
    OpCode::CmpRI.into(), CmpFlag::Eq.into(), 14, 0, 0, 128, 63, 
    OpCode::Hlt.into()
  ];

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  assert_eq!(p.as_slice(), expected);

  // EQRR
  let p = Compiler::new("eq $14 $15", io::stdout()).compile();
  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
    OpCode::CmpRR.into(), CmpFlag::Eq.into(), 14, 15, 
    OpCode::Hlt.into()
  ];

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  assert_eq!(p.as_slice(), expected);
}

#[test]
#[rustfmt::skip]
fn compile_geq(){
  // GEQII
  let p = Compiler::new("geq 4 2", io::stdout()).compile();
  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
    OpCode::Load.into(), EQ as u8, 1, 0, 0, 0, 
    OpCode::Hlt.into()
  ];

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  assert_eq!(p.as_slice(), expected);

  // GEQRI
  let p = Compiler::new("geq $14 1", io::stdout()).compile();
  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
    OpCode::CmpRI.into(), CmpFlag::Geq.into(), 14, 0, 0, 128, 63, 
    OpCode::Hlt.into()
  ];

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  assert_eq!(p.as_slice(), expected);

  // GEQIR
  let p = Compiler::new("geq 1 $14", io::stdout()).compile();
  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
    OpCode::CmpRI.into(), CmpFlag::Geq.into(), 14, 0, 0, 128, 63,
    OpCode::Not.into(), EQ as u8, EQ as u8,
    OpCode::Hlt.into(),
  ];

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  assert_eq!(p.as_slice(), expected);

  // GEQRR
  let p = Compiler::new("geq $15 $14", io::stdout()).compile();
  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
    OpCode::CmpRR.into(), CmpFlag::Geq.into(), 15, 14, 
    OpCode::Hlt.into()
  ];

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  assert_eq!(p.as_slice(), expected);
}

#[test]
#[rustfmt::skip]
fn compile_leq(){
  // LEQII
  let p = Compiler::new("leq 4 2", io::stdout()).compile();
  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
    OpCode::Load.into(), EQ as u8, 0, 0, 0, 0, OpCode::Hlt.into()
  ];

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  assert_eq!(p.as_slice(), expected);

  // LEQRI
  let p = Compiler::new("leq $14 1", io::stdout()).compile();
  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
    OpCode::CmpRI.into(), CmpFlag::Leq.into(), 14, 0, 0, 128, 63, 
    OpCode::Hlt.into()
  ];

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  assert_eq!(p.as_slice(), expected);

  // LEQIR
  let p = Compiler::new("leq 1 $14", io::stdout()).compile();
  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
    OpCode::CmpRI.into(), CmpFlag::Leq.into(), 14, 0, 0, 128, 63,
    OpCode::Not.into(), EQ as u8, EQ as u8,
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);

  // LEQRR
  let p = Compiler::new("leq $15 $14", io::stdout()).compile();
  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
    OpCode::CmpRR.into(), CmpFlag::Leq.into(), 15, 14, 
    OpCode::Hlt.into()
  ];

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  assert_eq!(p.as_slice(), expected);
}

#[test]
#[rustfmt::skip]
fn compile_gt(){
  // GTII
  let p = Compiler::new("gt 4 2", io::stdout()).compile();
  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
    OpCode::Load.into(), EQ as u8, 1, 0, 0, 0, 
    OpCode::Hlt.into()
  ];
  
  assert_eq!(p.as_slice(), expected);

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  // GTRI
  let p = Compiler::new("gt $14 1", io::stdout()).compile();
  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
    OpCode::CmpRI.into(), CmpFlag::Gt.into(), 14, 0, 0, 128, 63, 
    OpCode::Hlt.into()
  ];
  assert_eq!(p.as_slice(), expected);

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  // GTIR
  let p = Compiler::new("gt 1 $14", io::stdout()).compile();
  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
    OpCode::CmpRI.into(), CmpFlag::Gt.into(), 14, 0, 0, 128, 63,
    OpCode::Not.into(), EQ as u8, EQ as u8,
    OpCode::Hlt.into(),
  ];

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  assert_eq!(p.as_slice(), expected);

  // GTRR
  let p = Compiler::new("gt $15 $14", io::stdout()).compile();
  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
    OpCode::CmpRR.into(), CmpFlag::Gt.into(), 15, 14, 
    OpCode::Hlt.into()
  ];

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  assert_eq!(p.as_slice(), expected);
}

#[test]
#[rustfmt::skip]
fn compile_lt(){
  // LTII
  let p = Compiler::new("LT 2 1", io::stdout()).compile();
  assert_eq!(
    p.as_slice(), 
    [
      OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
      OpCode::Load.into(), EQ as u8, 0, 0, 0, 0, 
      OpCode::Hlt.into()
    ]
  );

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  // LTRI
  let p = Compiler::new("LT $14 1", io::stdout()).compile();
  assert_eq!(
    p.as_slice(),
    [
      OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
      OpCode::CmpRI.into(), CmpFlag::Lt.into(), 14, 0, 0, 128, 63, 
      OpCode::Hlt.into()
    ]
  );

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);    

  // LTIR
  let p = Compiler::new("LT 1 $14 ", io::stdout()).compile();
  assert_eq!(
    p.as_slice(),
    [
      OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
      OpCode::CmpRI.into(), CmpFlag::Lt.into(), 14, 0, 0, 128, 63,
      OpCode::Not.into(), EQ as u8, EQ as u8,
      OpCode::Hlt.into(),
    ]
  );

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);    

  // LTRR
  let p = Compiler::new("LT $15 $14", io::stdout()).compile();
  assert_eq!(
    p.as_slice(), 
    [
      OpCode::Jmp.into(), 5, 0, 0, 0, // main starts on 5
      OpCode::CmpRR.into(), CmpFlag::Lt.into(), 15, 14, 
      OpCode::Hlt.into()
    ]
  );

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);    
}

#[test]
#[rustfmt::skip]
fn compile_all_commands() {
  let src = include_str!("./full_compilation_test.spdr");
  let p = Compiler::new(src, io::stdout()).compile();

  let expected = [
    OpCode::Jmp.into(), 14, 0, 0, 0, // Jump to 14
    // Fn
    OpCode::RvSubRI.into(), 13, 90, 0, 0, 112, 65,
    OpCode::Ret.into(), 3,
    // Basic instructions
    OpCode::Load.into(), 14, 0, 0, 128, 63,
    OpCode::Copy.into(), 14, 16,
    OpCode::Not.into(), 14, 15,
    // Arithmetic
    OpCode::AddRI.into(), 14, 13, 0, 0, 128, 63,
    OpCode::SubRI.into(), 14, 13, 0, 0, 128, 63,
    OpCode::MulRI.into(), 14, 13, 0, 0, 128, 63,
    OpCode::DivRI.into(), 14, 13, 0, 0, 128, 63,
    OpCode::PowRI.into(), 14, 13, 0, 0, 128, 63,
    // Comparisons
    OpCode::CmpRR.into(), CmpFlag::Eq.into(), 14, 16,
    OpCode::CmpRR.into(), CmpFlag::Gt.into(), 14, 16,
    OpCode::CmpRR.into(), CmpFlag::Lt.into(), 14, 16,
    OpCode::CmpRR.into(), CmpFlag::Geq.into(), 14, 16,
    OpCode::CmpRR.into(), CmpFlag::Leq.into(), 14, 16,
    // Loop
    OpCode::Noop.into(),
    OpCode::Noop.into(),
    OpCode::Noop.into(),
    OpCode::Jmp.into(), 81, 0, 0, 0, // Jump to 81
    // While loop
    OpCode::Jmp.into(), 115, 0, 0, 0, // Jump to 115
    OpCode::AddRI.into(), 14, 13, 0, 0, 128, 63,
    OpCode::AddRI.into(), 14, 13, 0, 0, 128, 63,
    OpCode::AddRI.into(), 14, 13, 0, 0, 128, 63,
    OpCode::CmpRR.into(), CmpFlag::Leq.into(), 14, 16,
    OpCode::Jnz.into(), EQ as u8, 94, 0, 0, 0, // Jump to 94
    // For Loop
    OpCode::Load.into(), LOOP as u8, 0, 0, 0, 0,
    OpCode::SubRI.into(), 14, 13, 0, 0, 128, 63,
    OpCode::Noop.into(),
    OpCode::SubRI.into(), 14, 13, 0, 0, 128, 63,
    OpCode::AddRI.into(), LOOP as u8, LOOP as u8, 0, 0, 128, 63,
    OpCode::CmpRI.into(), CmpFlag::Eq.into(), LOOP as u8, 0, 0, 16, 65,
    OpCode::Jz.into(), EQ as u8, 131, 0, 0, 0, // Jump to 131
    // Memory manipulation
    OpCode::Push.into(), 15,
    OpCode::Pop.into(),
    OpCode::PopR.into(), 14,
    OpCode::WMem.into(), 14, 15, 0, 0, 32, 65, 10,
    OpCode::RMem.into(), 14, 15, 0, 0, 32, 65, 10,
    OpCode::MemCpy.into(), 16, 18,
    OpCode::Alloc.into(), 16, 18,
    OpCode::Dealloc.into(),
    // If
    OpCode::CmpRI.into(), CmpFlag::Gt.into(), 15, 0, 0, 96, 65,
    OpCode::Jz.into(), EQ as u8, 212, 0, 0, 0, // Jump to 215
    OpCode::Call.into(), 5, 0, 0, 0, // Jump to 5
    // Else If
    OpCode::CmpRI.into(), CmpFlag::Lt.into(), 15, 0, 0, 96, 65,
    OpCode::Jz.into(), EQ as u8, 228, 0, 0, 0, // Jump to 228
    OpCode::Noop.into(),
    OpCode::Noop.into(),
    OpCode::Noop.into(),
    OpCode::Hlt.into(),
  ];

    // Check printing the disassembled program does not cause the program to crash
    dbg!(&p);

  assert_eq!(p.as_slice(), expected);
}

#[test]
#[rustfmt::skip]
fn test_script_with_while_loop_compiles() {
  //Testing a while loop
  let src = include_str!("./test_script_while_loop.spdr");
  let mut w = io::stdout();
  let program = Compiler::new(src, &mut w,).compile();

  let loop_var = 9.0f32.to_le_bytes();

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5  
    OpCode::Load.into(), 15, 0, 0, 128, 63,  
    OpCode::Jmp.into(), 30, 0, 0, 0,  
    OpCode::AddRI.into(), 94, 94, 0, 0, 128, 63,  
    OpCode::AddRI.into(), 15, 15, 0, 0, 128, 63,  
    OpCode::CmpRI.into(), CmpFlag::Lt.into(), 15, loop_var[0], loop_var[1], loop_var[2], loop_var[3],  
    OpCode::Jnz.into(), EQ as u8, 16, 0, 0, 0, // Jump to 16  
    OpCode::Hlt.into(),
  ];
  assert_eq!(program.as_slice(), expected);

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&program);

  let mut vm = VM::new();
  vm.upload(program,);
  vm.run();

  assert_eq!(vm.reg()[15].as_f32(), 9.0);
}

#[test]
#[rustfmt::skip]
fn test_script_compiles_with_function_calls() {
  // Testing a function called
  let src = include_str!("./test_script_function.spdr");
  let mut w = io::stdout();
  let program = Compiler::new(src, &mut w,).compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&program);

  // Confirm function compiled properly
  let expected = [
    OpCode::Jmp.into(), 21, 0, 0, 0, // Main begins on 21  
    OpCode::MulRR.into(), 6, 4, 5,  
    OpCode::AddRI.into(), 6, 6, 16, 88, 244, 65, // [16, 88, 244, 65,] = 30.543  
    OpCode::Copy.into(), 4, 6,  
    OpCode::Ret.into(), 0,  
    OpCode::Load.into(), 4, 205, 204, 172, 64,  
    OpCode::Load.into(), 5, 80, 141, 83, 65,  
    OpCode::Call.into(), 5, 0, 0, 0,  
    OpCode::Copy.into(), 15, 4,  
    OpCode::Hlt.into(),
  ];

  assert_eq!(program.as_slice(), expected);

  // Foo is the equivalent of this function so test against each other
  fn foo(a:f32, b:f32,) -> f32 {
    let mut c = a * b;
    c += 30.543;
    c
  }

  let mut vm = VM::new();
  vm.upload(program,);
  vm.run();

  assert_eq!(vm.reg()[4].as_f32(), foo(5.4, 13.222));
}

#[test]
#[rustfmt::skip]
fn test_script_compiles_with_external_function() {
  // Test an external function call
  let src = include_str!("./test_external_script_function.spdr");
  let hd = PathBuf::from("./src/test/test_external_script_function.hd",);

  let mut compiler = Compiler::new(src, io::stdout(),);
  // Upload the header file to the compiler
  compiler.read_header(hd,);
  let program = compiler.compile();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&program);

  let a = 1.0f32.to_le_bytes();
  let b = 3.0f32.to_le_bytes();

  let expected = [
    OpCode::Jmp.into(), 5, 0, 0, 0, // `main` starts on 5  
    OpCode::Load.into(), 14, a[0], a[1], a[2], a[3],  
    OpCode::Load.into(), 15, b[0], b[1], b[2], b[3],  
    OpCode::Push.into(), 14,  
    OpCode::Push.into(), 15,  
    OpCode::SysCall.into(), 0,  
    OpCode::PopR.into(), 16,  
    OpCode::Hlt.into(),
  ];

  assert_eq!(program.as_slice(), expected);

  let mut vm = VM::new();

  fn foo_inner(a:f32, b:f32,) -> f32 {
    a * b + 30.543
  }

  fn foo_wrap(vm:&mut VM, _:&mut dyn Any,) {
    let a = vm.extern_read(vm.sp().as_u32() as usize,).unwrap().as_f32();
    // Add one to read the next lowest entry in the stack because the stack grows
    // downwards
    let b = vm.extern_read(vm.sp().as_u32() as usize + 1,).unwrap().as_f32();

    let c = foo_inner(a, b,);

    // Push c into the VM
    vm.extern_push(c,);
  }

  vm.register_extern(foo_wrap,);
  vm.upload(program,);
  vm.run();

  assert_eq!(vm.reg()[16].as_f32(), foo_inner(1.0, 3.0));
}

#[test]
#[rustfmt::skip]
fn load_and_run_assembled_script() {
  let program = Program::load("../spdr-assembler/src/test/basic_script_function.spex",).unwrap();
  let mut vm = VM::new();

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&program);

  // Confirm function compiled properly
  let expected = [
    OpCode::Jmp.into(), 21, 0, 0, 0, // Main begins on 21
    OpCode::MulRR.into(), 6, 4, 5, 
    OpCode::AddRI.into(), 6, 6, 16, 88, 244, 65, // 30.543.to_le_bytes() = [16, 88, 244, 65,]
    OpCode::Copy.into(), 4, 6,
    OpCode::Ret.into(), 0,
    OpCode::Load.into(), 4, 205, 204, 172, 64,
    OpCode::Load.into(), 5, 80, 141, 83, 65, 
    OpCode::Call.into(), 5, 0, 0, 0,
    OpCode::Copy.into(), 15, 4, 
    OpCode::Hlt.into(),
  ];

  assert_eq!(program.as_slice(), expected);

  // Run the actual program
  vm.upload(program,);
  vm.run();

  // Foo is the equivalent of this function so test against each other
  fn foo(a:f32, b:f32,) -> f32 {
    let mut c = a * b;
    c += 30.543;
    c
  }

  // Check program output
  assert_eq!(vm.reg()[4].as_f32(), foo(5.4, 13.222));
}

// This always has to be at the end.
// Because it has foo and bar in different orders and one run of the program
// shares the same interner it messes up the interned strings for every other
// test
#[test]
#[rustfmt::skip]
fn compile_multiple_functions_when_one_calls_other_before_other_defined(){
  let mut c = Compiler::new("CALL bar CALL foo FN foo {CALL bar RET 3} FN bar {POW $67 $64 $75 RET 2} CALL foo CALL bar", io::stdout());
  let p = c.compile();
  
  // Check the function pointer of `foo` is correct
  let foo_fn_idx = &intern("foo");
  assert_eq!(foo_fn_idx, &1);
  match c.table.get(foo_fn_idx){
    Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [5, 0, 0, 0,]),
    _ => panic!("Should be a function pointer"),
  }

  // Check the function pointer of `bar` is correct
  let bar_fn_idx = &intern("bar");
  assert_eq!(bar_fn_idx, &0);
  match c.table.get(bar_fn_idx){
    Some(VarDecl{ ty: Ty::Function(ptr) }) => assert_eq!(*ptr, [12, 0, 0, 0,]),
    _ => panic!("Should be a function pointer"),
  }

  // Check printing the disassembled program does not cause the program to crash
  dbg!(&p);

  // Check the binary is correct
  let expected = [
    OpCode::Jmp.into(),  18, 0, 0, 0, // `main` starts at 24
    // Call bar
    OpCode::Call.into(), 12, 0, 0, 0, // `foo` starts at 5
    OpCode::Ret.into(), 3,
    OpCode::PowRR.into(), 67, 64, 75, // `bar` starts at 12
    OpCode::Ret.into(), 2,
    // Call bar
    OpCode::Call.into(), 12, 0, 0, 0,
    // Call foo
    OpCode::Call.into(), 5, 0, 0, 0,
    // Call foo
    OpCode::Call.into(), 5, 0, 0, 0,
    // Call bar
    OpCode::Call.into(), 12, 0, 0, 0,
    OpCode::Hlt.into(),
  ];
  assert_eq!(p.as_slice(), expected);
}

impl<'tcx,> Compiler<'tcx,> {
  /// Method created to test `self.eat_current_instruction()` works.
  fn eat_compile(&mut self,) -> Program {
    // Iterate over each each and interpret it as an opcode
    while let Some(_,) = self.next_token() {
      // Match the instruction
      self.eat_current_instruction();
    }
    // Once all lines are compiled return the program
    return self.main.clone();
  }
}
