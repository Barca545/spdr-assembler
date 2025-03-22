use std::{
  fs,
  path::{Path, PathBuf},
};

use eyre::eyre;

use crate::errors::ErrorPrinter;

#[derive(Debug, Clone,)]
// Path is optional because the input may not be a file. (such as with
// tests or IDE commands)
pub struct SourceFile {
  src:String,
  // Needed so links to the file can print.
  path:Option<PathBuf,>,
}

impl SourceFile {
  /// Opens a new sourcefile from the given path.
  pub fn new_from_path<P,>(path:P,) -> Self
  where P: AsRef<Path,> {
    SourceFile::from(path,)
  }

  /// Creates a new SourceFile from a string of spdr assembly.
  pub fn new_from_str<S:ToString,>(src:S,) -> Self {
    SourceFile {
      src:src.to_string(),
      path:None,
    }
  }

  /// Returns the source code as a string slice.
  pub fn source_str(&self,) -> &str {
    &self.src
  }

  /// Returns the path.
  pub fn path(&self,) -> &Option<PathBuf,> {
    &self.path
  }
}

impl<P:AsRef<Path,>,> From<P,> for SourceFile {
  fn from(path:P,) -> Self {
    let src = match fs::read_to_string(&path,) {
      Ok(src,) => src,
      Err(_,) => {
        ErrorPrinter::graceful_exit_early(eyre!("{} is not a valid path.", path.as_ref().to_str().unwrap()),)
      }
    };
    let path = Some(PathBuf::from(path.as_ref(),),);
    SourceFile { src, path, }
  }
}
