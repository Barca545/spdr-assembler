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
pub(crate) enum PatchData {
  /// The index in the [`Program`] a `Call` instruction will target.
  Address([u8; 4],),
  Empty,
}

#[derive(Debug, Clone,)]
pub(crate) struct Patch {
  /// Type of data to insert into the regions.
  pub(crate) content:PatchData,
  /// Area of the code to replace with the concrete target of the patch.
  pub(crate) regions:Vec<Region,>,
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
