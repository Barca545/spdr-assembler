use crate::{tokenizer::TokenKind, Ty};
use thiserror::Error;

#[derive(Debug, Error,)]
pub enum ASMError<'e,> {
  #[error("UNRECOGNIZED TOKEN: {0} (ln {1} col {2}) is not a legal token.")]
  UnrecognizedToken(&'e str, u16, u16,),
  #[error("INVALID TOKEN: {current}{next} is not a valid token. Did you mean '+','-','*','/','+=','-=','*=', or '/='?")]
  IllegalMathToken { current:char, next:char, },
  #[error("NOT AN OPCODE: {0} (ln {1} col {2}) cannot be used as the basis of an opcode.")]
  NotAnOpcode(TokenKind, u16, u16,),
  #[error("UNDECLARED Identifier: {0} (ln {1} col {2}) is not declared as an identifier before use.")]
  UndeclaredIdentifier(&'e str, u16, u16,),
  #[error("INVALID IMMEDIATE TYPE: Immediate value must be a boolean or a number not {0} (ln {1} col{2}).")]
  InvalidImmediateType(TokenKind, u16, u16,),
  #[error("MISSING EQUALS IN VAR DECLARATION: A variable declaration must be followed by \"=\" not {0}")]
  NoEquals(TokenKind,),
  // Can these be aggregated?
  #[error("MISSING KEYWORD: The identifier in a {0} loop must be followed by {1} not {2}")]
  MissingKwd(TokenKind, TokenKind, TokenKind,),
  #[error("NO NAME: A function declaration must be followed by an identifier, not {0}")]
  NoNameFn(TokenKind,),
  #[error("NO NAME: A function call must be followed by an identifier, not {0} (ln {1} col {2})")]
  NoNameCall(TokenKind, u16, u16,),
  // Can these be aggregated?
  #[error("NOT REGISTER OR IDENTITY: {0} (ln {1} col {2}) is not a register or an identifier.")]
  NotRegisterOrIdent(TokenKind, u16, u16,),
  // #[error("NOT REGISTER OR IDENTITY: {0} (ln {1} col {2}) is not a register or an identifier.")]
  // NotRegister(TokenKind, u16, u16,),
  #[error("NOT RANGE: {0} (ln {1} col {2}) is not a range.")]
  NotRange(TokenKind, u16, u16,),
  // #[error("NOT BOOL: {0} ln {1} col {2} is not a boolean.")]
  // NotBool(TokenKind, u16, u16,),
  #[error(
    "INVALID CONDITION: A condition must be either a Gt, Geq, Lt, Leq, or a Bool token not a {0} token."
  )]
  NotEquality(TokenKind,),
  #[error("NOT FUNCTION: Expected identity to be a function; {0} is not a function.")]
  NotFunction(Ty,),
  #[error("UNAVAILABLE FUNCTION NAME: The name {0} is already in use.")]
  UnavailableFunctionName(&'e str,),
  #[error(
    "UNREGISTERED EXTERNAL CALL: The name {0} (ln {1} col {2}) is not associated with a registered external function call."
  )]
  UnregistedSyscall(&'e str, u16, u16,),
}
