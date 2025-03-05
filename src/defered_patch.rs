use spdr_isa::program::Program;
use std::cell::OnceCell;

// Refactor:
// - Possible the patch reserve only needs to take in the program and not the
//   len separate from the program. I need to wait to get it working to see if
//   it truly over needs program.len()

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash,)]
///A replacement for [`Range`](std::ops::Range) which implements [`Copy`].
pub struct Region {
  /// The lower bound of the range (inclusive).
  pub start:usize,
  /// The upper bound of the range (exclusive).
  pub end:usize,
}

#[derive(Debug,)]
pub struct Patch {
  target:OnceCell<[u8; 4],>,
  /// Area of the code to replace with the concrete target of the patch.
  regions:Vec<Region,>,
}

impl Patch {
  fn new(idx:usize,) -> Self {
    Patch {
      target:OnceCell::new(),
      regions:vec![Region {
        start:idx,
        end:idx + 4,
      }],
    }
  }

  fn insert_index(&mut self, idx:usize,) {
    self.regions.push(Region {
      start:idx,
      end:idx + 4,
    },);
  }

  fn update_target(&mut self, target:[u8; 4],) {
    self.target.set(target,).unwrap();
  }
}

#[derive(Debug,)]
pub struct DeferredPatches {
  inner:Vec<Patch,>,
}

impl DeferredPatches {
  pub fn new() -> Self {
    DeferredPatches { inner:Vec::new(), }
  }

  /// Reserve a new region at the current end of the [`Program`] for patching.
  /// Returns the new [`Patch`]'s location in [`DeferredPatches`].
  /// `patch_site` is the location in the program to patch.
  pub fn reserve(&mut self, patch_site:usize, program:&mut Program,) -> usize {
    // Insert the index into the vec of replacements to make
    // If the index is at the start of the program the index is zero
    self.inner.push(Patch::new(patch_site,),);

    // Pad the program
    program.extend_from_slice(&[0; 4],);

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
  pub fn insert_patch_site(&mut self, patch_idx:usize, patch_site:usize, program:&mut Program,) {
    // Add the index to the vector of indices which need to be replaced by the
    // lookahead value when it is found
    self.inner[patch_idx].insert_index(patch_site,);

    // Pad the program
    program.extend_from_slice(&[0; 4],);
  }

  /// Provide a concrete value for a replacement.
  /// - `patch_idx` is the location of the replacment in the [DeferredPatches]
  ///   struct.
  /// - `target` is the value to be stored in the target [`Program`] region.
  pub fn update_target(&mut self, patch_idx:usize, target:usize,) {
    self.inner[patch_idx].update_target((target as f32).to_le_bytes(),);
  }

  /// Replace all patch regions in the [`Program`] with their target values.
  pub fn patch(&mut self, program:&mut Program,) {
    for (patch_index, patch,) in &mut self.inner.iter().enumerate() {
      // Get the target
      // Fetching it outside is more efficent than recalculating + prevents the issue
      // where `take`-ing from the OnceCell causes it to deinit for future indices
      let target = patch.target.get().expect(&format!(
        "Only call `replace` after finding all patch targets. {} does not have a target.",
        patch_index
      ),);
      for region in &patch.regions {
        // Replace the reserved bytes in the program with the real value of the
        // target index
        program.as_mut_slice()[region.start..region.end].copy_from_slice(target,);
      }
    }
  }
}

#[cfg(test)]
mod test {
  use super::DeferredPatches;
  use spdr_isa::program::Program;

  #[test]
  fn deferred_patches_patch_test() {
    let mut program = Program::new();
    let mut patches = DeferredPatches::new();

    // Prepare 2 patches for the program
    let patch_index_1 = patches.reserve(program.len(), &mut program,);
    let patch_index_2 = patches.reserve(program.len(), &mut program,);

    // Prepare a new patch to the same target as the first one
    patches.insert_patch_site(patch_index_1, program.len(), &mut program,);

    // Update the target values for both sites
    patches.update_target(patch_index_1, 15,);
    patches.update_target(patch_index_2, 43,);

    patches.patch(&mut program,);

    assert_eq!(program.as_slice(), [0u8, 0, 112, 65, 0, 0, 44, 66, 0, 0, 112, 65]);
  }

  #[test]
  fn t() {
    dbg!(15f32.to_le_bytes());
  }
}
