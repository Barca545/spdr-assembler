use eyre::Result;
use pico_args::Arguments;
use serde::{Deserialize, Serialize};
use std::{ffi::OsStr, fs, path::PathBuf};

/// Help message for the Assembler. Loosely modeled on [docopt](http://docopt.org/).
const HELP:&str = "\
USAGE:
  spdr-assembler [OPTIONS] --path PATH [INPUT]

FLAGS:
  -h, --help                   Prints help information.
  -v, --version                Prints assembler version information.
  -d, --defaults               Display any assember defaults.


OPTIONS:
  --name STRING                Declares the name of the file.
  --input PATH                 Specifies the path of the file to compile. 
  --header PATH                Sets a header file for a compilation run.   
  --output PATH                Sets a specific output path [default: exe root directory].
  --update-output PATH         Updates the default output path.


ARGS:
  <INPUT>
";

const CONFIG_FILE_PATH:&str = "./src/config.toml";

/// Arguments to a run of the Assembler.
#[derive(Debug,)]
pub struct AppArgs {
  /// User provided filename.
  pub(crate) name:String,
  /// User provided path to the source code.
  pub(crate) path:PathBuf,
  /// A header file describing any external functions the source code can call.
  pub(crate) header:Option<PathBuf,>,
  /// Folder to place the compiled binary.
  pub(crate) output:PathBuf,
}

#[derive(Debug, Deserialize, Serialize,)]
struct Package {
  /// Name of the assembler. This will not change.
  name:String,
  /// The version of the assembler uses [semver](https://semver.org/).
  version:String,
}

/// Configuration information about the current assembler.
#[derive(Debug, Deserialize, Serialize,)]
struct Information {
  /// Default folder to place the compiled binary.
  output:PathBuf,
}

/// Represents a `config.toml` file.
#[derive(Debug, Deserialize, Serialize,)]
struct Config {
  package:Package,
  information:Information,
}

/// Build [`AppArgs`] from Arguments the user passed via the CLI.
pub fn parse_arguments() -> Result<AppArgs,> {
  let mut pargs = Arguments::from_env();

  // Get the config file
  let mut config = toml::from_str::<Config,>(&fs::read_to_string(CONFIG_FILE_PATH,).unwrap(),).unwrap();

  // Help has a higher priority and should be handled separately.
  if pargs.contains(["-h", "--help",],) {
    print!("{}", HELP);
    std::process::exit(0,);
  }
  else if pargs.contains(["-d", "--defaults",],) {
    std::process::exit(0,);
  }
  else if pargs.contains(["-v", "--version",],) {
    print!("{}", config.package.version);
    std::process::exit(0,);
  }

  // If there's a command to update the default output, update the output before
  // completing any other actions
  // TODO: Should this be a flag?
  if let Some(output,) = pargs
    .opt_value_from_os_str("--update-output", parse_path,)
    .unwrap()
  {
    // Update Config.toml
    config.information.output = output;

    // Save config
    // TODO: There is probably a more efficient way to overwrite one line instead of
    // resaving the whole file
    fs::write(CONFIG_FILE_PATH, toml::to_string(&config,).unwrap(),).unwrap();

    // Because the first arg is always the name of the program that will still be in
    // the list of args. Therefore the min len is 1 not 0
    // TODO: Is there a more robust way of doing this than just checking for 1
    if pargs.clone().finish().len() == 1 {
      std::process::exit(0,);
    }
  }

  // Get the path. Print the error then print the HELP message if getting the path
  // fails.
  // TODO: Print the HELP message too, atm this will only print the error message
  let path = pargs
    .opt_value_from_os_str("--path", parse_path,)
    .unwrap()
    .unwrap();
  let name = pargs.value_from_str("--name",).unwrap();

  let header = pargs.opt_value_from_os_str("--header", parse_path,)?;

  // If no output is provided, use the default from the config.toml
  let output = pargs
    .value_from_str("--output",)
    .unwrap_or(PathBuf::from(config.information.output,),);

  Ok(AppArgs {
    path,
    name,
    header,
    output,
  },)
}

fn parse_path(s:&OsStr,) -> Result<PathBuf,> {
  Ok(s.into(),)
}

#[cfg(test)]
mod test {
  use super::{Config, CONFIG_FILE_PATH};
  use std::{fs, path::PathBuf};

  #[test]
  fn update_config_file() {
    // Get the config file
    let mut config = toml::from_str::<Config,>(&fs::read_to_string(CONFIG_FILE_PATH,).unwrap(),).unwrap();

    let old_output = config.information.output;

    // Update Config.toml
    config.information.output =
      PathBuf::from("C:\\Users\\user\\Documents\\Hobbies\\Coding\\spdr-assembler\\src\\test",);

    // Save config
    fs::write(CONFIG_FILE_PATH, toml::to_string(&config,).unwrap(),).unwrap();

    // Reload and assert it changed
    let mut config = toml::from_str::<Config,>(&fs::read_to_string(CONFIG_FILE_PATH,).unwrap(),).unwrap();

    assert_eq!(
      config.information.output,
      PathBuf::from("C:\\Users\\user\\Documents\\Hobbies\\Coding\\spdr-assembler\\src\\test",)
    );

    // Reset the file
    config.information.output = old_output;
    fs::write(CONFIG_FILE_PATH, toml::to_string(&config,).unwrap(),).unwrap();
  }
}
