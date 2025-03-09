use crate::Compiler;
use eyre::Result;
use spdr_isa::program::Program;
use thiserror::Error;

// Refactor:
// - The patch reserve only needs to take in the program and not the len
//   separate from the program. I need to wait to get it working to see if it
//   truly over needs program.len()
// - Add an optional content section to the patches which I will use for
//   functions

#[derive(Debug, Error,)]
enum PatchErr {
  #[error("Cannot update a Patch's contents if it is already occupied.")]
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

#[derive(Debug, Clone,)]
/// Data a [`Patch`] will place in a [`Program`].
enum PatchData {
  /// The index in the [`Program`] a `Call` instruction will target.
  FunctionPointer([u8; 4],),
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
      regions:vec![],
    }
  }

  #[cfg(test)]
  pub fn regions(&self,) -> Vec<Region,> {
    self.regions.clone()
  }

  /// Reserves a [`Region`] at the end of a [`Program`] for the `Patch` to
  /// update when the `patch` method is called. Pads the reserved `Region` with
  /// zeroes.
  fn reserve_region(&mut self, program:&mut Program,) {
    self.regions.push(Region {
      start:program.len(),
      end:program.len() + 4,
    },);
    program.extend_from_slice(&[0; 4],);
  }

  pub fn update_address(&mut self, addr:usize,) -> Result<(),> {
    match self.content {
      PatchData::Empty => {
        self.content = PatchData::FunctionPointer((addr as f32).to_le_bytes(),);
        Ok((),)
      }
      _ => Err(PatchErr::Occupied.into(),),
      // _ => panic!("Cannot update a Patch's contents if it is already occupied."),
    }
  }

  /// Replace all the regions of a program a [`Patch`] references with the
  /// address they correspond to. Error if the `Patch` does not have a
  /// corresponding address.
  pub(super) fn patch(&self, program:&mut Program,) {
    let addr = match self.content {
      PatchData::FunctionPointer(addr,) => addr,
      PatchData::Empty => panic!("A Patch must have an address before patch can be called."),
    };

    for region in &self.regions {
      program.as_mut_slice()[region.start..region.end].copy_from_slice(&addr,);
    }
  }
}

#[derive(Debug, Clone,)]
pub struct JumpTarget {
  /// Region holding the target
  pub region:Region,
  /// Value of the target in relation to `main` pre-linking
  pub value:Option<usize,>,
}

#[derive(Debug, Clone,)]
pub struct Linker {
  pub inner:Vec<Patch,>,
  pub jmp_targets:Vec<JumpTarget,>,
}

impl Linker {
  pub fn new() -> Self {
    Linker {
      inner:Vec::new(),
      jmp_targets:Vec::new(),
    }
  }

  /// Reserve a new region at the current end of the [`Program`] for patching.
  /// Returns the new [`Patch`]'s location in [`Linker`].
  /// `patch_site` is the location in the program to patch.
  pub fn reserve(&mut self,) -> usize {
    // Insert the index into the vec of replacements to make
    // If the index is at the start of the program the index is zero
    self.inner.push(Patch {
      content:PatchData::Empty,
      regions:vec![],
    },);

    // Return the index of the desired replacement
    self.inner.len() - 1
  }

  /// Add a new region to an existing [`Patch`].
  ///
  /// Use when `target` is shared with an existing patch.
  ///
  /// This works in conjunction with the [`Compiler`](crate::Compiler)'s
  /// `SymbolTable` which will map reserved indices to identifiers for
  /// function calls.
  /// `patch_site` is the location in the program to patch.
  pub fn insert_patch_site(&mut self, patch_idx:usize, program:&mut Program,) {
    // Add the index to the vector of indices which need to be replaced by the
    // lookahead value when it is found
    self.inner[patch_idx].reserve_region(program,);
  }

  /// Register a jump site for the `Linker` to correct during linking.
  /// Return the index of the site in `jmp_targets`.
  pub fn register_jump_site(&mut self, main:&mut Program,) -> usize {
    // Record the region that needs updating during linking
    let start = main.len();
    let region = Region {
      start, end:start + 4,
    };

    self.jmp_targets.push(JumpTarget { region, value:None, },);

    // Pad the region with 0s
    main.extend_from_slice(&[0; 4],);

    self.jmp_targets.len() - 1
  }

  pub fn update_jump_site(&mut self, site_idx:usize, value:usize,) {
    self.jmp_targets[site_idx].value = Some(value,)
  }

  /// Provide a concrete value for a function pointer.
  /// - `patch_idx`: The location of the replacment in the [Linker] struct.
  /// - `ptr`: The location of the function's definition in the binary.
  pub fn update_function_pointer(&mut self, patch_idx:usize, ptr:usize,) -> Result<(),> {
    // Store the value of the function pointer
    self.inner[patch_idx].update_address(ptr,)
  }

  /// Replace all patch regions in the [`Program`] with their target values.
  pub fn link(&mut self, main:&mut Program, lib:&Program,) {
    // Patch all function pointers
    for patch in &mut self.inner {
      patch.patch(main,);
    }

    // For every jump address, increment them by the size of the `lib` + 5
    let offset = lib.len() as f32 + 5.0;
    for target in &self.jmp_targets {
      let addr = match target.value {
        Some(val,) => val as f32 + offset,
        None => panic!("Must assign all JumpTarget values before linking"),
      };

      main.as_mut_slice()[target.region.start..target.region.end].copy_from_slice(&addr.to_le_bytes(),);
    }
  }
}

/// This is for handling linking and function defining/calling  
impl<'tcx,> Compiler<'tcx,> {
  // Binary layout
  // 0-4: Offset of `main`
  // 5-offset: function definitions
  // offset+: main function

  /// Return the next available address a function can be stored.
  pub(super) fn next_function_pointer(&self,) -> usize {
    // Add 4 to account for the displacement caused by the offset information at the
    // binary's beginning
    self.lib.len() + 5
  }

  /// Store the body of a function in `lib`.
  pub(super) fn store_function(&mut self, body:Program,) {
    // Store the function in `lib`
    self.lib.extend_from_slice(body.as_slice(),);
  }

  /// Return an option containing a function's pointer.
  pub(super) fn get_function_pointer(&self, patch_idx:&usize,) -> Option<[u8; 4],> {
    // Get the Patch from the linker
    match self.linker.inner[*patch_idx].content {
      // Get the binary address
      PatchData::FunctionPointer(ptr,) => Some(ptr,),
      _ => None,
    }
  }
}

#[cfg(test)]
mod test {
  use super::{Linker, PatchData};
  use crate::defered_patch::{Patch, Region};
  use spdr_isa::program::Program;

  #[test]
  fn deferred_patches_patch_test() {
    let mut main = Program::from(vec![33, 33, 33, 33],);
    let lib = Program::from(vec![33, 4, 6],);
    let mut linker = Linker::new();

    let target = 8;
    let site_idx = linker.register_jump_site(&mut main,);
    linker.update_jump_site(site_idx, target,);

    // Confirm the region was added and main was padded
    assert_eq!(main.as_slice(), &[33, 33, 33, 33, 0, 0, 0, 0]);
    assert_eq!(linker.jmp_targets[0].region, Region { start:4, end:8, });
    assert_eq!(linker.jmp_targets[0].value.unwrap(), 8);

    linker.link(&mut main, &lib,);

    let correct_target_1 = (target + lib.len() + 5) as f32;
    assert_eq!(main.as_slice()[4..8], correct_target_1.to_le_bytes());

    // // Prepare 2 patches for the program
    // let patch_index_1 = patches.reserve();
    // patches.insert_patch_site(patch_index_1, &mut program,);
    // let patch_index_2 = patches.reserve();
    // patches.insert_patch_site(patch_index_2, &mut program,);

    // // Check the regions are correct for both patches
    // assert_eq!(
    //   patches.inner[patch_index_1].regions,
    //   vec![Region { start:0, end:4 },]
    // );
    // assert_eq!(
    //   patches.inner[patch_index_2].regions,
    //   vec![Region { start:4, end:8 },]
    // );

    // // Prepare a new patch to the same target as the first one
    // patches.insert_patch_site(patch_index_1, &mut program,);

    // // Check the regions are correct for both patches
    // assert_eq!(
    //   patches.inner[patch_index_1].regions,
    //   vec![Region { start:0, end:4 }, Region { start:8, end:12 }]
    // );
    // assert_eq!(
    //   patches.inner[patch_index_2].regions,
    //   vec![Region { start:4, end:8 },]
    // );

    // // Update the target values for both sites
    // patches.update_function_pointer(patch_index_1, 1,);

    // assert_eq!(
    //   patches.inner[patch_index_1].content.unwrap_target(),
    //   [0, 0, 128, 63,]
    // );

    // patches.link(&mut program,);

    // assert_eq!(
    //   program.as_slice(),
    //   [0u8, 0, 128, 63, 0, 0, 64, 65, 0, 0, 128, 63, 33, 33, 33]
    // );
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

    assert!(matches!(
      patch.content,
      PatchData::FunctionPointer([0, 0, 160, 64,])
    ))
  }

  impl PatchData {
    fn unwrap_target(&self,) -> [u8; 4] {
      match self {
        PatchData::FunctionPointer(target,) => *target,
        _ => panic!(),
      }
    }
  }
}
