use eyre::Result;
use pico_args::Arguments;
use serde::{Deserialize, Serialize};
use std::{ffi::OsStr, fs, path::PathBuf};

use crate::errors::ErrorPrinter;

/// Help message for the Assembler. Loosely modeled on [docopt](http://docopt.org/).
const HELP:&str = "\
USAGE:
  spdr-assembler [OPTIONS] --path PATH [INPUT]

FLAGS:
  -h, --help                   Prints help information.
  -v, --version                Prints assembler version information.
  -d, --defaults               Display any assember defaults.
  -p, --print                  Prints the output assembly when completed.


OPTIONS:
  --name STRING                Declares the name of the file.
  --input PATH                 Specify the file to assemble. 
  --str STRING                 Provide a string of spdr macroassembly to the Assembler.
  --header PATH                Specify a header file.  
  --output PATH                Specify an output path.
  --update-output PATH         Updates the default output path.
";

pub(crate) const CONFIG_FILE_PATH:&str = "./src/config.toml";

/// Arguments to a run of the Assembler.
#[derive(Debug,)]
pub struct AppArgs {
  /// User provided filename.
  pub(crate) name:String,
  /// User provided path to the source code.
  pub(crate) path:Option<PathBuf,>,
  /// User provided ASM string.
  pub(crate) str:Option<String,>,
  /// A header file describing any external functions the source code can call.
  pub(crate) header:Option<PathBuf,>,
  /// Folder to place the compiled binary.
  pub(crate) output:PathBuf,
}

#[derive(Debug, Deserialize, Serialize,)]
pub(crate) struct Package {
  /// Name of the assembler. This will not change.
  pub(crate) name:String,
  /// The version of the assembler uses [semver](https://semver.org/).
  pub(crate) version:String,
}

// TODO: Needs better name
/// Configuration information about the current assembler.
#[derive(Debug, Deserialize, Serialize,)]
pub(crate) struct Information {
  /// Default folder to place the compiled binary.
  pub(crate) output:PathBuf,
}

/// Represents a `config.toml` file.
#[derive(Debug, Deserialize, Serialize,)]
pub(crate) struct Config {
  pub(crate) package:Package,
  pub(crate) information:Information,
}

/// Build [`AppArgs`] from Arguments the user passed via the CLI.
pub fn parse_arguments() -> Result<AppArgs,> {
  let mut pargs = Arguments::from_env();

  // Get the config file
  let raw_config = match fs::read_to_string(CONFIG_FILE_PATH,) {
    Ok(config,) => config,
    Err(_,) => {
      ErrorPrinter::graceful_exit_early(format!("config.toml was not found in {}", CONFIG_FILE_PATH),)
    }
  };
  let mut config = toml::from_str::<Config,>(&raw_config,).unwrap();

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
  let path = match pargs.opt_value_from_os_str("--path", parse_path,) {
    Ok(path,) => path,
    Err(err,) => {
      println!("{}", HELP);
      ErrorPrinter::graceful_exit_early(err,);
    }
  };

  // Also print the HELP message if this fails
  let str = match pargs.opt_value_from_str("--str",) {
    Ok(str,) => str,
    Err(err,) => {
      println!("{}", HELP);
      ErrorPrinter::graceful_exit_early(err,);
    }
  };

  let name = pargs.value_from_str("--name",).unwrap();

  let header = pargs.opt_value_from_os_str("--header", parse_path,)?;

  // If no output is provided, use the default from the config.toml
  let output = pargs
    .value_from_str("--output",)
    .unwrap_or(PathBuf::from(config.information.output,),);

  Ok(AppArgs {
    str,
    path,
    name,
    header,
    output,
  },)
}

fn parse_path(s:&OsStr,) -> Result<PathBuf,> {
  Ok(s.into(),)
}
