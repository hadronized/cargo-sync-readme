//! # `cargo sync-readme`
//!
//! **A plugin that generates a Markdown section in your README based on your Rust documentation.**
//!
//! ## How does this work?
//!
//! Basically, this tool provides you with a simple mechanism to synchronize your front page
//! documentation from your `lib.rs` or `main.rs` with a place in your *readme* file. In order to do
//! so, this command will parse your inner documentation (i.e. `//!`) on `lib.rs` or `main.rs` and will
//! output it in your *readme* file at specific markers.
//!
//! ## The markers
//!
//! Because you might want a specific *readme* file that adds some more information to the documentation
//! from your Rust code, this tool allows you to select a place where to put the documentation. This is
//! done with three markers:
//!
//!   - `<!-- cargo-sync-readme -->`: that annotation must be placed in your *readme* file where you
//!     want the Rust documentation to be included and synchronized.
//!   - `<!-- cargo-sync-readme start -->`: that annotation is automatically inserted by the command to
//!     delimit the beginning of the synchronized documentation.
//!   - `<!-- cargo-sync-readme end -->`: that annotation is automatically inserted by the command to
//!     delimit the ending of the synchronized documentation.
//!
//! **You only have to use the former marker (i.e. `<!-- cargo-sync-readme -->`).** The rest of the
//! markers will be handled automatically for you by the tool.
//!
//! > Okay, but I want to change the place of the documentation now.
//!
//! When you have already put the synchronized documentation in your *readme* but want to change its
//! location, all you have to do is remove everything in between the start and end annotations
//! (annotations included) and place the `<!-- cargo-sync-readme -->` annotation wherever you want your
//! synchronized documentation to appear.
//!
//! ## How should I use this?
//!
//! First, this tool will respect what you put in your `Cargo.toml`. There is a special field called
//! `readme` that gives the name / path of the document you want to be used as *readme* file.
//! `cargo sync-readme` will operate on that file.
//!
//! > Disclaimer: even though crates.io’s documentation and manifest format doesn’t explicitly state the
//! > type of this file, **`cargo sync-readme` assumes it’s Markdown.** If you want a support for
//! > another file type, please open an issue or a PR: those are warmly welcomed — and if you live in
//! > Paris, I offer you a Kwak or a Chouffe! ♥
//!
//! Once you have put the annotation in your *readme* file, just run the command without argument to
//! perform the synchronization:
//!
//! ```
//! cargo sync-readme
//! ```
//!
//! This will effectively update your *readme* file with the main documentation from your Rust code
//! (either a `lib.rs` or `main.rs`, depending on the type of your crate).
//!
//! ## Q/A and troubleshooting
//!
//! ### Are workspace crates supported?
//!
//! Not yet! If you have ideas how the tool should behave with them, please contribute with an issue or
//! a PR!

use std::env::current_dir;
use std::fmt;
use std::fs::{File, read_dir};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process;
use structopt::StructOpt;
use toml::Value;
use toml::de::Error as TomlError;

const MANIFEST_NAME: &str = "Cargo.toml";
const MARKER: &str = "<!-- cargo-sync-readme -->\n";
const MARKER_START: &str = "<!-- cargo-sync-readme start -->\n";
const MARKER_END: &str = "<!-- cargo-sync-readme end -->\n";

#[derive(Debug, StructOpt)]
#[structopt(name = "cargo-sync-readme")]
enum CLIOpt {
  #[structopt(
    name = "sync-readme",
    about = "Generate a Markdown section in your README based on your Rust documentation.",
  )]
  SyncReadme
}

fn main() {
  let _cli_opt = CLIOpt::from_args();

  if let Ok(pwd) = current_dir() {
    match find_manifest(pwd) {
      Ok(ref manifest) => {
        let entry_point = get_entry_point(manifest);

        if let Some(entry_point) = entry_point {
          let doc = extract_inner_doc(entry_point);
          let readme_path = get_readme(manifest);

          match transform_readme(&readme_path, doc) {
            Ok(new_readme) => {
              let mut file = File::create(readme_path).unwrap();
              let _ = file.write_all(new_readme.as_bytes());
            }

            Err(e) => eprintln!("{}", e)
          }
        } else {
          eprintln!("Cannot find entrypoint (default to src/lib.rs or src/main.rs).");
          process::exit(1);
        }
      }

      Err(e) => {
        eprintln!("{}", e);
        process::exit(1);
      }
    }
  } else {
    eprintln!("It seems like you’re running this command from nowhere good…");
    process::exit(1);
  }
}


#[derive(Debug)]
enum FindManifestError {
  CannotFindManifest,
  CannotOpenManifest(PathBuf),
  TomlError(TomlError)
}

impl fmt::Display for FindManifestError {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    match *self {
      FindManifestError::CannotFindManifest => f.write_str("Cannot find manifest (Cargo.toml)."),
      FindManifestError::CannotOpenManifest(ref path) =>
        write!(f, "Cannot open manifest at path {}.", path.display()),
      FindManifestError::TomlError(ref e) => write!(f, "TOML error: {}.", e)
    }
  }
}

#[derive(Debug)]
struct Manifest {
  toml: Value,
  parent_dir: PathBuf
}

impl Manifest {
  fn new(toml: Value, path: PathBuf) -> Self {
    Manifest { toml, parent_dir: path.parent().unwrap().to_owned() }
  }
}

/// Get the TOML-formatted manifest by looking up the current directory; if not found, go to the
/// parent directory and recursively retry until one is found… eventually.
fn find_manifest<P>(dir: P) -> Result<Manifest, FindManifestError> where P: AsRef<Path> {
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
      let mut file = File::open(&path).map_err(|_| FindManifestError::CannotOpenManifest(path.clone()))?;
      let mut file_str = String::new();

      let _ = file.read_to_string(&mut file_str);
      let toml = file_str.parse().map_err(FindManifestError::TomlError)?;

      Ok(Manifest::new(toml, path))
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

/// Get the path to the file we want to take the documentation from.
fn get_entry_point(manifest: &Manifest) -> Option<PathBuf> {
  match get_entry_point_from_manifest(&manifest.toml) {
    Some(ep) => Some(ep.into()),
    None => {
      // we need to guess whether it’s a lib or a binary crate
      let lib_path = manifest.parent_dir.join("src/lib.rs");

      if lib_path.is_file() {
        Some(lib_path)
      } else {
        let main_path = manifest.parent_dir.join("src/main.rs");

        if main_path.is_file() {
          Some(main_path)
        } else {
          None
        }
      }
    }
  }
}

fn get_entry_point_from_manifest(toml: &Value) -> Option<String> {
  toml.get("lib").or(toml.get("bin"))
    .and_then(|v| v.get("path"))
    .and_then(Value::as_str)
    .map(|s| s.to_owned())
}

/// Open a file and get its main inner documentation (//!).
fn extract_inner_doc<P>(path: P) -> String where P: AsRef<Path> {
  let mut file = File::open(path.as_ref()).unwrap();
  let mut content = String::new();

  let _ = file.read_to_string(&mut content);

  content.lines()
    .skip_while(|l| !l.starts_with("//!"))
    .take_while(|l| l.starts_with("//!"))
    .map(|l| format!("{}\n", l.trim_start_matches("//!")))
    .collect()
}

/// Extract the path to the readme file from the manifest.
fn get_readme(manifest: &Manifest) -> PathBuf {
  let readme = manifest.toml
    .get("package")
    .and_then(|p| p.get("readme"))
    .and_then(Value::as_str)
    //.map(|s| s.to_owned())
    .unwrap_or("README.md");
  manifest.parent_dir.join(readme)
}

#[derive(Debug)]
enum TransformError {
  CannotReadReadme(PathBuf),
  MissingOrIllFormadMarkers
}

impl fmt::Display for TransformError {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    match *self {
      TransformError::CannotReadReadme(ref path) => write!(f, "Cannot read README at {}.", path.display()),
      TransformError::MissingOrIllFormadMarkers => f.write_str("Markers not found or ill-formed; check your file again."),
    }
  }
}

/// Read a readme file and return its content with the documentation injected, if any.
fn transform_readme<P, S>(path: P, new_readme: S) -> Result<String, TransformError> where P: AsRef<Path>, S: AsRef<str> {
  let path = path.as_ref();
  let new_readme = new_readme.as_ref();
  let mut file = File::open(path).map_err(|_| TransformError::CannotReadReadme(path.to_owned()))?;
  let mut content = String::new();

  let _ = file.read_to_string(&mut content);

  if let Some(marker_offset) = content.find(MARKER) {
    // try to look for the sync marker (first time using the tool)
    let first_part = &content[0 .. marker_offset];
    let second_part = &content[marker_offset + MARKER.len() ..];

    Ok(format!("{}{}\n{}\n{}{}", first_part, MARKER_START, new_readme, MARKER_END, second_part))
  } else {
    // try to look for the start and end markers (already used the tool)
    let marker_start_offset = content.find(MARKER_START);
    let marker_end_offset = content.find(MARKER_END);

    match (marker_start_offset, marker_end_offset) {
      (Some(start), Some(end)) => {
        let first_part = &content[0 .. start];
        let second_part = &content[end + MARKER_END.len() ..];

        Ok(format!("{}{}\n{}\n{}{}", first_part, MARKER_START, new_readme, MARKER_END, second_part))
      },

      _ => Err(TransformError::MissingOrIllFormadMarkers)
    }
  }
}
