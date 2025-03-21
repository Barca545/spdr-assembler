use std::{
  fs,
  path::{Path, PathBuf},
};

#[derive(Debug, Clone,)]
// Name and path are optional because the input may not be a file. (such as with
// tests or IDE commands)
pub struct SourceFile {
  src:String,
  // Needed so links to the file can print.
  path:Option<PathBuf,>,
}

impl SourceFile {
  /// Opens a new sourcefile from the given path.
  pub fn new_from_path<P,>(path:P,) -> Self
  where
    P: AsRef<Path,>,
    PathBuf: From<P,>,
  {
    SourceFile::from(path,)
  }

  /// Creates a new SourceFile from a string of spdr assembly.
  pub fn new_from_raw<S:ToString,>(src:S,) -> Self {
    SourceFile {
      src:src.to_string(),
      path:None,
    }
  }

  /// Returns the source code as a string slice.
  pub fn source_str(&self,) -> &str {
    &self.src
  }

  pub fn path(&self,) -> &Option<PathBuf,> {
    &self.path
  }
}

impl<P,> From<P,> for SourceFile
where
  P: AsRef<Path,>,
  PathBuf: From<P,>,
{
  fn from(path:P,) -> Self {
    let src:String = fs::read_to_string(&path,).unwrap();
    let path = Some(PathBuf::from(path,),);
    SourceFile { src, path, }
  }
}
