use std::env::current_dir;
use std::fmt;
use std::fs::{File, read_dir};
use std::io::Read;
use std::path::{Path, PathBuf};
use toml::Value;
use toml::de::Error as TomlError;

fn main() {
  if let Ok(pwd) = current_dir() {
    match find_manifest(pwd) {
      Ok(toml) => println!("found manifest!\n{:?}", toml),
      Err(e) => eprintln!("{}", e)
    }
  } else {
    eprintln!("it seems like you’re running this command from nowhere good…");
  }
}

const MANIFEST_NAME: &str = "Cargo.toml";

#[derive(Debug)]
enum FindManifestError {
  CannotFindManifest,
  CannotOpenManifest(PathBuf),
  TomlError(TomlError)
}

impl fmt::Display for FindManifestError {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    match *self {
      FindManifestError::CannotFindManifest => f.write_str("cannot find manifest"),
      FindManifestError::CannotOpenManifest(ref path) =>
        write!(f, "cannot open manifest at path {}", path.display()),
      FindManifestError::TomlError(ref e) => write!(f, "TOML error: {}", e)
    }
  }
}

/// Get the TOML-formatted manifest by looking up the current directory; if not found, go to the
/// parent directory and recursively retry until one is found… eventually.
fn find_manifest<P>(dir: P) -> Result<Value, FindManifestError> where P: AsRef<Path> {
  let dir = dir.as_ref();

  if let Ok(mut dir_entry) = read_dir(dir) {
    if let Some(file_entry) = dir_entry.find(
      |entry| {
        match entry {
          Ok(entry) if entry.file_name() == MANIFEST_NAME => true,
          _ => false
        }
      }) {
      let path = file_entry.unwrap().path();
      let mut file = File::open(&path).map_err(|_| FindManifestError::CannotOpenManifest(path))?;
      let mut file_str = String::new();

      let _ = file.read_to_string(&mut file_str);
      file_str.parse().map_err(FindManifestError::TomlError)
    } else {
      // try to the parent
      if let Some(parent) = dir.parent() {
        find_manifest(parent)
      } else {
        Err(FindManifestError::CannotFindManifest)
      }
    }
  } else {
    Err(FindManifestError::CannotFindManifest)
  }
}
