use crate::patch::{Patch, PatchData, Region};
use spdr_isa::program::Program;

#[test]
fn patch_works_for_multiple_regions() {
  let mut program = Program::new();
  let mut patch_1 = Patch::new();
  let mut patch_2 = Patch::new();

  // Reserve the regiosn
  patch_1.reserve_region(&mut program,);
  patch_2.reserve_region(&mut program,);
  patch_1.reserve_region(&mut program,);
  patch_2.reserve_region(&mut program,);
  patch_2.reserve_region(&mut program,);

  // Update the addresses
  patch_1.update_address(5,).unwrap();
  patch_2.update_address(1,).unwrap();

  // Patch both program's regions
  patch_2.patch(&mut program,);
  patch_1.patch(&mut program,);

  // Check the content is correct
  assert!(matches!(patch_1.content, PatchData::Address([5, 0, 0, 0,])));
  assert!(matches!(patch_2.content, PatchData::Address([1, 0, 0, 0,])));

  // Check the program is correct
  assert_eq!(
    program.as_slice(),
    [5, 0, 0, 0, 1, 0, 0, 0, 5, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0,]
  );
}

#[test]
#[should_panic = "Cannot update a Patch's contents if it is already occupied."]
fn updating_occupied_patchdata_fails() {
  let mut patch = Patch {
    content:PatchData::Empty,
    regions:vec![Region { start:0, end:4, }],
  };
  patch.update_address(5,).unwrap();
  patch.update_address(0,).unwrap();

  assert!(matches!(patch.content, PatchData::Address([0, 0, 160, 64,])))
}
