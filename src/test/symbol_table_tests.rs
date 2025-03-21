use crate::symbol_table::{SymbolTable, Ty, VarDecl};

// Test the lookup will keep searching until the symbol is found or the top is
// reached
#[test]
fn lookup_travels_to_top() {
  let mut table = SymbolTable::new();
  let sym = 0;

  // Add a variable declaration to the table
  table.add_symbol(sym, VarDecl::new(Ty::Register(15,),),);

  // Go 3 scopes deep
  table.enter_scope();
  table.enter_scope();
  table.enter_scope();

  let decl = table.lookup(&sym,).unwrap();

  // Confirm decl is the correct value
  assert_eq!(decl, &VarDecl::new(Ty::Register(15,),));

  // Confirm value is in the top scope and the other scopes are empty
  assert_eq!(table.tables()[0].get(&sym).unwrap(), decl);
  assert_eq!(table.tables()[1].len(), 0);
  assert_eq!(table.tables()[2].len(), 0);
  assert_eq!(table.tables()[3].len(), 0);
}

// Test the lookup will return the most recent declaration of a variable
#[test]
#[rustfmt::skip]
fn lookup_uses_closest_symbol() {
  let mut table = SymbolTable::new();
  let sym = 0;

  // Add a variable declaration to the table
  table.add_symbol(sym, VarDecl::new(Ty::Register(15,),),);

  // Go 2 scopes deep
  table.enter_scope();
  table.enter_scope();

  // Add the variable to the table with a different value
  table.add_symbol(sym, VarDecl::new(Ty::Register(8,),),);

  // Go 1 more scope deeper
  table.enter_scope();

  // Confirm the value for decl found is the closest one and not the earliest
  // declaration
  assert_eq!(table.lookup(&sym,).unwrap(), &VarDecl::new(Ty::Register(8,),));

  // Confirm both decls are in the table
  assert_eq!(table.tables()[0].get(&sym).unwrap(), &VarDecl::new(Ty::Register(15,),));
  assert_eq!(table.tables()[1].len(), 0);
  assert_eq!(table.tables()[2].get(&sym).unwrap(), &VarDecl::new(Ty::Register(8,),));
  assert_eq!(table.tables()[3].len(), 0);

  // Exit return to scope 1
  table.exit_scope();
  table.exit_scope();

  // Confirm the value for decl found is the closest one and not the earliest
  // declaration
  assert_eq!(table.lookup(&sym,).unwrap(), &VarDecl::new(Ty::Register(15,),));

  // Confirm both decls are in the table
  assert_eq!(table.tables()[0].get(&sym).unwrap(), &VarDecl::new(Ty::Register(15,),));
  assert_eq!(table.tables()[1].len(), 0);

}
