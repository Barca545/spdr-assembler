use crate::{
  tokenizer::{Location, TokenKind},
  Ty,
};
use thiserror::Error;

#[derive(Debug, Error,)]
pub enum ASMError<'e,> {
  #[error("UNRECOGNIZED TOKEN: '{0}' {1} is not a legal token.")]
  UnrecognizedToken(String, Location,),
  #[error("NOT AN OPCODE: {0} {1} cannot be used as the basis of an opcode.")]
  NotAnOpcode(TokenKind, Location,),
  #[error("UNDECLARED Identifier: {0} {1} is not declared as an identifier before use.")]
  UndeclaredIdentifier(&'e str, Location,),
  #[error("INVALID COMPARISON OPERATOR: {0} {1} is not a valid comparison operator.")]
  InvalidComparison(TokenKind, Location,),
  #[error("INVALID IMMEDIATE TYPE: Immediate value must be a boolean or a number not {0} {1}.")]
  InvalidImmediateType(TokenKind, Location,),
  #[error("MISSING EQUALS IN VAR DECLARATION: A variable declaration must be followed by \"=\" not {0}")]
  NoEquals(TokenKind,),
  // Can these be aggregated?
  #[error("MISSING KEYWORD: The identifier in a {0} loop must be followed by {1} not {2}")]
  MissingKwd(TokenKind, TokenKind, TokenKind,),
  #[error("MISSING LOOP VARIABLE: For loops must have a loop variable. The loop defined here {0} is followed by {1}.")]
  MissingLoopVar(Location, TokenKind,),
  #[error("MISSING FUNCTION NAME: A function declaration must be followed by an identifier, not {0}.")]
  MissingFnName(TokenKind,),
  #[error("NO NAME: A function call must be followed by an identifier, not {0} {1}")]
  NoNameCall(TokenKind, Location,),
  // Can these be aggregated?
  #[error("NOT REGISTER OR IDENTITY: {0} {1} is not a register or an identifier.")]
  NotRegisterOrIdent(TokenKind, Location,),
  #[error("NOT RANGE: {0} {1} is not a range.")]
  NotRange(TokenKind, Location,),
  #[error(
    "INVALID CONDITION: A condition must be either a Gt, Geq, Lt, Leq, or a Bool token not a {0} token."
  )]
  NotEquality(TokenKind,),
  #[error("NOT FUNCTION: Expected identity to be a function; {0} is not a function.")]
  NotFunction(Ty,),
  #[error("UNAVAILABLE FUNCTION NAME: The name {0} is already in use.")]
  UnavailableFunctionName(&'e str,),
  #[error(
    "UNREGISTERED EXTERNAL CALL: The name {0} {1} is not associated with a registered external function call."
  )]
  UnregistedSyscall(&'e str, Location,),
}

impl<'e,> ASMError<'e,> {
  pub fn loc(&self,) -> Location {
    match self {
      ASMError::UnrecognizedToken(_, loc,) => *loc,
      ASMError::NotAnOpcode(_, loc,) => *loc,
      ASMError::UndeclaredIdentifier(_, loc,) => *loc,
      ASMError::InvalidImmediateType(_, loc,) => *loc,
      ASMError::InvalidComparison(_, loc,) => *loc,
      ASMError::NoEquals(_,) => todo!(),
      ASMError::MissingKwd(_, _, _,) => todo!(),
      ASMError::MissingFnName(_,) => todo!(),
      ASMError::NoNameCall(_, loc,) => *loc,
      ASMError::NotRegisterOrIdent(_, loc,) => *loc,
      ASMError::NotRange(_, loc,) => *loc,
      ASMError::NotEquality(_,) => todo!(),
      ASMError::NotFunction(_,) => todo!(),
      ASMError::UnavailableFunctionName(_,) => todo!(),
      ASMError::UnregistedSyscall(_, loc,) => *loc,
      ASMError::MissingLoopVar(loc, _,) => *loc,
    }
  }
}
