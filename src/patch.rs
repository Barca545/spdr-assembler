use crate::Compiler;
use eyre::Result;
use spdr_isa::program::Program;
use thiserror::Error;

#[derive(Debug, Error,)]
enum PatchErr {
  #[error("\x1b[93mPATCH OCCUPIED:\x1b[0m Cannot update a Patch's contents if it is already occupied.")]
  Occupied,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash,)]
///A replacement for [`Range`](std::ops::Range) which implements [`Copy`].
pub struct Region {
  /// The lower bound of the range (inclusive).
  pub start:usize,
  /// The upper bound of the range (exclusive).
  pub end:usize,
}

#[derive(Debug, Clone, Copy,)]
/// Data a [`Patch`] will place in a [`Program`].
enum PatchData {
  /// The index in the [`Program`] a `Call` instruction will target.
  Address([u8; 4],),
  Empty,
}

#[derive(Debug, Clone,)]
pub struct Patch {
  /// Type of data to insert into the regions.
  content:PatchData,
  /// Area of the code to replace with the concrete target of the patch.
  regions:Vec<Region,>,
}

impl Patch {
  pub(super) fn new() -> Self {
    Patch {
      content:PatchData::Empty,
      regions:Vec::new(),
    }
  }

  /// Reserves a [`Region`] at the end of a [`Program`] for the `Patch` to
  /// update when the `patch` method is called. Pads the reserved `Region` with
  /// zeroes.
  pub fn reserve_region(&mut self, program:&mut Program,) {
    self.regions.push(Region {
      start:program.len(),
      end:program.len() + 4,
    },);
    program.extend_from_slice(&[0; 4],);
  }

  pub fn update_address(&mut self, addr:usize,) -> Result<(),> {
    match self.content {
      PatchData::Empty => {
        self.content = PatchData::Address((addr as u32).to_le_bytes(),);
        Ok((),)
      }
      _ => Err(PatchErr::Occupied.into(),),
    }
  }

  /// Replace all the regions of a program a [`Patch`] references with the
  /// address they correspond to. Error if the `Patch` does not have a
  /// corresponding address.
  pub(super) fn patch(&self, program:&mut Program,) {
    let addr = match self.content {
      PatchData::Address(addr,) => addr,
      PatchData::Empty => panic!("A Patch must have an address before patch can be called."),
    };

    for region in &self.regions {
      program.as_mut_slice()[region.start..region.end].copy_from_slice(&addr,);
    }
  }
}

/// This is for handling linking and function defining/calling  
impl<'tcx,> Compiler<'tcx,> {
  // Binary layout
  // 0-4: Jump to `main`
  // 5-offset: function definitions
  // offset+: main function

  /// Return the next available address a function can be stored.
  pub(super) fn next_function_pointer(&self,) -> usize {
    // Add 4 to account for the displacement caused by the offset information at the
    // binary's beginning
    self.main.len() + 5
  }
}

#[cfg(test)]
mod test {
  use super::PatchData;
  use crate::patch::{Patch, Region};
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
}
