//! Library used to implement the cargo-sync-readme binary.

use regex::RegexBuilder;
use std::fmt;
use std::fs::{File, read_dir};
use std::io::Read;
use std::path::{Path, PathBuf};
use toml::Value;
use toml::de::Error as TomlError;

const MANIFEST_NAME: &str   = "Cargo.toml";
const MARKER: &str          = "<!-- cargo-sync-readme -->";
const MARKER_START: &str    = "<!-- cargo-sync-readme start -->";
const MARKER_END: &str      = "<!-- cargo-sync-readme end -->";
const MARKER_RE: &str       = "^<!-- cargo-sync-readme -->$";
const MARKER_START_RE: &str = "^<!-- cargo-sync-readme start -->$";
const MARKER_END_RE: &str   = "^<!-- cargo-sync-readme end -->$";

/// Common Markdown code-block state.
///
/// This type helps track which state we are currently in when parsing code-blocks. It can either
/// be none or a code-block with either backticks (`) or tildes (~).
#[derive(Debug)]
enum CodeBlockState {
  None,
  InWithBackticks,
  InWithTildes
}

#[derive(Debug)]
pub enum FindManifestError {
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
pub struct Manifest {
  pub toml: Value,
  pub parent_dir: PathBuf
}

impl Manifest {
  fn new(toml: Value, path: PathBuf) -> Self {
    Manifest { toml, parent_dir: path.parent().unwrap().to_owned() }
  }

  /// Get the TOML-formatted manifest by looking up the current directory; if not found, go to the
  /// parent directory and recursively retry until one is found… eventually.
  pub fn find_manifest<P>(dir: P) -> Result<Self, FindManifestError> where P: AsRef<Path> {
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
          Self::find_manifest(parent)
        } else {
          Err(FindManifestError::CannotFindManifest)
        }
      }
    } else {
      Err(FindManifestError::CannotFindManifest)
    }
  }

  /// Get the path to the file we want to take the documentation from.
  pub fn entry_point(&self) -> Option<PathBuf> {
    match self.entry_point_from_toml() {
      Some(ep) => Some(ep.into()),
      None => {
        // we need to guess whether it’s a lib or a binary crate
        let lib_path = self.parent_dir.join("src/lib.rs");

        if lib_path.is_file() {
          Some(lib_path)
        } else {
          let main_path = self.parent_dir.join("src/main.rs");

          if main_path.is_file() {
            Some(main_path)
          } else {
            None
          }
        }
      }
    }
  }

  /// Extract the path to the readme file from the manifest.
  pub fn readme(&self) -> PathBuf {
    let readme = self.toml
      .get("package")
      .and_then(|p| p.get("readme"))
      .and_then(Value::as_str)
      //.map(|s| s.to_owned())
      .unwrap_or("README.md");

    self.parent_dir.join(readme)
  }

  fn entry_point_from_toml(&self) -> Option<String> {
    self.toml.get("lib").or(self.toml.get("bin"))
      .and_then(|v| v.get("path"))
      .and_then(Value::as_str)
      .map(|s| s.to_owned())
  }
}


/// Open a file and get its main inner documentation (//!), applying filters if needed.
pub fn extract_inner_doc<P>(path: P, strip_hidden_doc: bool) -> String where P: AsRef<Path> {
  let mut file = File::open(path.as_ref()).unwrap();
  let mut content = String::new();
  let mut codeblock_st = CodeBlockState::None;

  let _ = file.read_to_string(&mut content);

  let lines: Vec<_> = content
    .lines()
    .skip_while(|l| !l.starts_with("//!"))
    .take_while(|l| l.starts_with("//!"))
    .map(|l| format!("{}\n", l.trim_start_matches("//!")))
    .collect();

  // find the minimal offset of all lines for which the first character is not a space
  let offset = lines
    .iter()
    .flat_map(|line| line.find(|c: char| !c.is_whitespace()))
    .min()
    .unwrap_or(0);

  // trim by the given offset to remove the introduced space by the Rust doc
  lines
    .iter()
    .map(|line| if line == "\n" { line } else { &line[offset..] })
    .filter(|l| {
      if strip_hidden_doc {
        strip_hidden_doc_tests(&mut codeblock_st, l)
      } else {
        true
      }
    })
    .collect()
}

#[derive(Debug)]
pub enum TransformError {
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

/// Open and read a README file.
pub fn read_readme<P>(path: P) -> Result<String, TransformError> where P: AsRef<Path> {
  let path = path.as_ref();
  let mut file = File::open(path).map_err(|_| TransformError::CannotReadReadme(path.to_owned()))?;
  let mut content = String::new();

  let _ = file.read_to_string(&mut content);

  Ok(content)
}

/// Transform a readme file and return its content with the documentation injected, if any.
///
/// Perform any required other transformations if asked by the user.
pub fn transform_readme<C, R>(
  content: C,
  new_readme: R,
) -> Result<String, TransformError>
where C: AsRef<str>,
      R: AsRef<str> {
  let content = content.as_ref();
  let new_readme = new_readme.as_ref();

  let mut marker_re_builder = RegexBuilder::new(MARKER_RE);
  marker_re_builder.multi_line(true);
  let marker_re = marker_re_builder.build().unwrap();

  if let Some(marker_match) = marker_re.find(&content) {
    // try to look for the sync marker (first time using the tool)
    let marker_offset = marker_match.start();
    let first_part = &content[0 .. marker_offset];
    let second_part = &content[marker_offset + MARKER.len() ..];

    Ok(reformat_with_markers(first_part, new_readme, second_part))
  } else {
    // try to look for the start and end markers (already used the tool)
    let mut marker_start_re_builder = RegexBuilder::new(MARKER_START_RE);
    marker_start_re_builder.multi_line(true);
    let marker_start_re = marker_start_re_builder.build().unwrap();
    let mut marker_end_re_builder = RegexBuilder::new(MARKER_END_RE);
    marker_end_re_builder.multi_line(true);
    let marker_end_re = marker_end_re_builder.build().unwrap();

    let marker_start = marker_start_re.find(&content);
    let marker_end = marker_end_re.find(&content);

    match (marker_start, marker_end) {
      (Some(start_match), Some(end_match)) => {
        let start_offset = start_match.start();
        let end_offset = end_match.end();
        let first_part = &content[0 .. start_offset];
        let second_part = &content[end_offset ..];

        Ok(reformat_with_markers(first_part, new_readme, second_part))
      },

      _ => Err(TransformError::MissingOrIllFormadMarkers)
    }
  }
}

// Reformat the README by inserting the documentation between the start and end markers.
fn reformat_with_markers(first_part: &str, doc: &str, second_part: &str) -> String {
  format!("{}{}\n\n{}\n{}{}", first_part, MARKER_START, doc, MARKER_END, second_part)
}

/// Strip hidden documentation tests from a readme.
fn strip_hidden_doc_tests(st: &mut CodeBlockState, line: &str) -> bool {
  match st {
    CodeBlockState::None => {
      // if we’re not currently in a code-block, check if we need to open one; in all cases,
      // we don’t want to filter that line out
      if line.starts_with("~~~") {
        *st = CodeBlockState::InWithTildes;
      } else if line.starts_with("```") {
        *st = CodeBlockState::InWithBackticks;
      }

      true
    }

    CodeBlockState::InWithTildes => {
      // we’re in a code-block, so filter only lines starting with a dash (#) and let others
      // go through; close the code-block if we find three tildes (~~~)
      if line.starts_with("# ") {
        false
      } else {
        if line.starts_with("~~~") {
          *st = CodeBlockState::None;
        }

        true
      }
    }

    CodeBlockState::InWithBackticks => {
      // we’re in a code-block, so filter only lines starting with a dash (#) and let others
      // go through; close the code-block if we find three backticks (```)
      if line.starts_with("# ") {
        false
      } else {
        if line.starts_with("```") {
          *st = CodeBlockState::None;
        }

        true
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn strip_dash_starting_lines() {
    let mut st = CodeBlockState::None;

    assert_eq!(strip_hidden_doc_tests(&mut st, "# okay"), true);
    assert_eq!(strip_hidden_doc_tests(&mut st, "```"), true);
    assert_eq!(strip_hidden_doc_tests(&mut st, "foo bar zoo"), true);
    assert_eq!(strip_hidden_doc_tests(&mut st, "# hello"), false);
    assert_eq!(strip_hidden_doc_tests(&mut st, "#"), true);
    assert_eq!(strip_hidden_doc_tests(&mut st, "# "), false);
    assert_eq!(strip_hidden_doc_tests(&mut st, "# ### nope"), false);
    assert_eq!(strip_hidden_doc_tests(&mut st, "~~~"), true);
    assert_eq!(strip_hidden_doc_tests(&mut st, "```"), true);
    assert_eq!(strip_hidden_doc_tests(&mut st, "# still okay"), true);
  }
}
