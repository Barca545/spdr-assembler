use crate::cli_integration::Config;
use std::{fs, path::PathBuf};

const TEST_CONFIG_FILE_PATH:&str = "./src/test/test_config.toml";

#[test]
fn update_config_file() {
  // Get the config file
  let mut config = toml::from_str::<Config,>(&fs::read_to_string(TEST_CONFIG_FILE_PATH,).unwrap(),).unwrap();

  let old_output = config.information.output;

  // Update Config.toml
  config.information.output =
    PathBuf::from("C:/Users/User/Documents/Hobbies/Coding/spdr-assembler/src/test",);

  // Save config
  fs::write(TEST_CONFIG_FILE_PATH, toml::to_string(&config,).unwrap(),).unwrap();

  // Reload and assert it changed
  let mut config = toml::from_str::<Config,>(&fs::read_to_string(TEST_CONFIG_FILE_PATH,).unwrap(),).unwrap();

  assert_eq!(
    config.information.output,
    PathBuf::from("C:/Users/User/Documents/Hobbies/Coding/spdr-assembler/src/test",)
  );

  // Reset the file
  config.information.output = old_output;
  fs::write(TEST_CONFIG_FILE_PATH, toml::to_string(&config,).unwrap(),).unwrap();
}
