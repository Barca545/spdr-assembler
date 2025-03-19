use std::{
  collections::HashMap,
  fmt::{Debug, Display},
};

#[derive(Debug, Clone,)]
pub struct SymbolTable {
  /// An array of tables mapping symbols to [`VarDecl`]s.
  tables:Vec<HashMap<u32, VarDecl,>,>,
}

impl SymbolTable {
  pub(crate) fn new() -> Self {
    SymbolTable {
      tables:vec![HashMap::new()],
    }
  }

  /// Enter a new scope.
  pub(crate) fn enter_scope(&mut self,) {
    self.tables.push(HashMap::new(),);
  }

  pub(crate) fn exit_scope(&mut self,) {
    self.tables.pop();
  }

  /// Add a new symbol to the current scope.
  pub(crate) fn add_symbol(&mut self, sym:u32, decl:VarDecl,) {
    // TODO: Should error if the symbol has already been declared in this scope.
    // Either that or name reassignment on declaration so shadowing works.
    // Once this is done the code in compile_block currently performing a similar
    // check should be removed.
    self.tables.last_mut().unwrap().insert(sym, decl,);
  }

  /// Looks for an symbol's [`VarDecl`]. Traverses the stack of tables until the
  /// top is reached.
  pub(crate) fn lookup(&self, sym:&u32,) -> Option<&VarDecl,> {
    // TODO: Figure out if reversing here is actually more efficient. It feels like
    // it should be since the assumption is the symbol is more likely to be in a
    // nearby scope.
    self.tables.iter().rev().find_map(|table| table.get(sym,),)
  }

  #[cfg(test)]
  pub(crate) fn tables(&self,) -> &Vec<HashMap<u32, VarDecl,>,> {
    &self.tables
  }
}

#[derive(Debug, Clone, Copy, PartialEq,)]
//JUMP AND JNZ will never take a Register as an arg.
pub enum Ty {
  /// Registers hold the index of their assigned register
  Register(u8,),
  /// Labels hold the index number the label references.
  Label(usize,),
  /// Functions hold the function's address as a `[u8;4]`;
  Function([u8; 4],),
  /// Functions hold the index the VM where stores them in its collection of
  /// external functions.
  ExternalFunction(u8,),
}

impl Display for Ty {
  fn fmt(&self, f:&mut std::fmt::Formatter<'_,>,) -> std::fmt::Result {
    match self {
      Ty::Register(v,) => write!(f, "Reg({})", v),
      Ty::Label(v,) => write!(f, "Label({})", v),
      Ty::Function(ptr,) => write!(f, "Function(patch_index: {:?}", ptr,),
      Ty::ExternalFunction(idx,) => write!(f, "ExternalFunction({idx})"),
    }
  }
}

#[derive(Clone, Copy, PartialEq,)]
/// A Symbol Table entry. Contains information about identities in the source
/// code.
pub(crate) struct VarDecl {
  pub(crate) ty:Ty,
}

impl Display for VarDecl {
  fn fmt(&self, f:&mut std::fmt::Formatter<'_,>,) -> std::fmt::Result {
    write!(f, "VarDecl(ty: {})", self.ty)
  }
}

impl Debug for VarDecl {
  fn fmt(&self, f:&mut std::fmt::Formatter<'_,>,) -> std::fmt::Result {
    Display::fmt(&self, f,)
  }
}

impl VarDecl {
  pub(crate) fn new(ty:Ty,) -> Self {
    Self { ty, }
  }
}
