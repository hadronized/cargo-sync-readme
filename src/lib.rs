//! Library used to implement the cargo-sync-readme binary.

use crate::intralinks::FQIdentifier;
use regex::RegexBuilder;
use std::collections::HashSet;
use std::fmt;
use std::fs::{read_dir, File};
use std::io::Read;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use toml::de::Error as TomlError;
use toml::Value;

const MANIFEST_NAME: &str = "Cargo.toml";
const MARKER_START: &str = "<!-- cargo-sync-readme start -->";
const MARKER_END: &str = "<!-- cargo-sync-readme end -->";
const MARKER_RE: &str = "^<!-- cargo-sync-readme -->\r?$";
const MARKER_START_RE: &str = "^<!-- cargo-sync-readme start -->\r?$";
const MARKER_END_RE: &str = "^<!-- cargo-sync-readme end -->\r?$";
const RUST_LANG_ANNOTATION: &str = "rust";

pub mod intralinks;

/// Common Markdown code-block state.
///
/// This type helps track which state we are currently in when parsing code-blocks. It can either
/// be none or a code-block with either backticks (`) or tildes (~).
#[derive(Debug, PartialEq)]
enum CodeBlockState {
  None,
  InWithBackticks,
  InWithTildes,
}

#[derive(Debug)]
pub enum FindManifestError {
  CannotFindManifest,
  CannotOpenManifest(PathBuf),
  TomlError(TomlError),
}

impl fmt::Display for FindManifestError {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    match *self {
      FindManifestError::CannotFindManifest => f.write_str("Cannot find manifest (Cargo.toml)."),
      FindManifestError::CannotOpenManifest(ref path) => {
        write!(f, "Cannot open manifest at path {}.", path.display())
      }
      FindManifestError::TomlError(ref e) => write!(f, "TOML error: {}.", e),
    }
  }
}

#[derive(Debug)]
pub struct Manifest {
  pub toml: Value,
  pub parent_dir: PathBuf,
}

impl Manifest {
  fn new<P>(toml: Value, path: P) -> Self
  where
    P: AsRef<Path>,
  {
    Manifest {
      toml,
      parent_dir: path.as_ref().parent().unwrap().to_owned(),
    }
  }

  pub fn load<P>(path: P) -> Result<Self, FindManifestError>
  where
    P: AsRef<Path>,
  {
    let path = path.as_ref();
    let mut file =
      File::open(&path).map_err(|_| FindManifestError::CannotOpenManifest(path.to_owned()))?;
    let mut file_str = String::new();
    let _ = file.read_to_string(&mut file_str);
    let toml = file_str.parse().map_err(FindManifestError::TomlError)?;

    Ok(Manifest::new(toml, path))
  }

  /// Get the TOML-formatted manifest by looking up the current directory; if not found, go to the
  /// parent directory and recursively retry until one is found… eventually.
  pub fn find_manifest<P>(dir: P) -> Result<Self, FindManifestError>
  where
    P: AsRef<Path>,
  {
    let dir = dir.as_ref();

    if let Ok(mut dir_entry) = read_dir(dir) {
      if let Some(file_entry) = dir_entry.find(|entry| match entry {
        Ok(entry) if entry.file_name() == MANIFEST_NAME => true,
        _ => false,
      }) {
        let path = file_entry.unwrap().path();

        Manifest::load(path)
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

  /// Extract the path to the readme file from the manifest.
  pub fn crate_name(&self) -> Option<&str> {
    self
      .toml
      .get("package")
      .and_then(|p| p.get("name"))
      .and_then(Value::as_str)
  }

  /// Get the path to the file we want to take the documentation from.
  pub fn entry_point(&self, prefer_doc_from: Option<PreferDocFrom>) -> Option<PathBuf> {
    match self.entry_point_from_toml(prefer_doc_from) {
      Some(ep) => Some(ep.into()),
      None => {
        // we need to guess whether it’s a lib or a binary crate
        let lib_path = self.parent_dir.join("src/lib.rs");
        let main_path = self.parent_dir.join("src/main.rs");

        match (lib_path.is_file(), main_path.is_file()) {
          (true, true) => match prefer_doc_from {
            Some(PreferDocFrom::Binary) => Some(main_path),
            Some(PreferDocFrom::Library) => Some(lib_path),
            _ => None,
          },

          (true, _) => Some(lib_path),
          (_, true) => Some(main_path),
          _ => None,
        }
      }
    }
  }

  /// Extract the path to the readme file from the manifest.
  pub fn readme(&self) -> PathBuf {
    let readme = self
      .toml
      .get("package")
      .and_then(|p| p.get("readme"))
      .and_then(Value::as_str)
      .unwrap_or("README.md");

    self.parent_dir.join(readme)
  }

  fn entry_point_from_toml(&self, prefer_from: Option<PreferDocFrom>) -> Option<String> {
    let lib = self.toml.get("lib");
    let bin = self.toml.get("bin");
    let preference = match prefer_from {
      Some(PreferDocFrom::Binary) => bin.clone(),
      Some(PreferDocFrom::Library) => lib.clone(),
      _ => None,
    };

    preference
      .or(lib)
      .or(bin)
      .and_then(|v| v.get("path"))
      .and_then(Value::as_str)
      .map(|s| s.to_owned())
  }
}

/// Preferences from which file the documentation should be taken if both present.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PreferDocFrom {
  Binary,
  Library,
}

impl FromStr for PreferDocFrom {
  type Err = String;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    match s {
      "bin" => Ok(PreferDocFrom::Binary),
      "lib" => Ok(PreferDocFrom::Library),
      _ => Err("not a valid preference".to_owned()),
    }
  }
}

fn load_file_to_string<P>(path: P) -> String
where
  P: AsRef<Path>,
{
  let mut file = File::open(path.as_ref()).unwrap();
  let mut content = String::new();
  let _ = file.read_to_string(&mut content);

  content
}

fn transform_inner_doc(doc: &str, show_hidden_doc: bool, crlf: bool) -> String {
  let mut codeblock_st = CodeBlockState::None;

  let lines: Vec<String> = doc
    .lines()
    .skip_while(|l| !l.trim_start().starts_with("//!"))
    .take_while(|l| l.trim_start().starts_with("//!"))
    .map(|l| {
      let l = l.trim_start().trim_start_matches("//!");
      if crlf {
        format!("{}\r\n", l)
      } else {
        format!("{}\n", l)
      }
    })
    .collect();

  // find the minimal offset of all lines for which the first character is not a space
  let offset = lines
    .iter()
    .flat_map(|line| line.find(|c: char| !c.is_whitespace()))
    .min()
    .unwrap_or(0);

  let sanitized_annotated_lines: Vec<String> = lines
    .into_iter()
    .map(|line| {
      if crlf && line == "\r\n" || line == "\n" {
        line
      } else {
        line[offset..].to_owned()
      }
    })
    .map(|line| annotate_code_blocks(&mut codeblock_st, line, crlf))
    .collect();

  sanitized_annotated_lines
    .into_iter()
    .filter(|l| {
      if show_hidden_doc {
        true
      } else {
        strip_hidden_doc_tests(&mut codeblock_st, l)
      }
    })
    .collect()
}

/// Open a file and get its main inner documentation (//!), applying filters if needed.
pub fn extract_inner_doc<P>(path: P, show_hidden_doc: bool, crlf: bool) -> String
where
  P: AsRef<Path>,
{
  let doc = load_file_to_string(path);

  transform_inner_doc(&doc, show_hidden_doc, crlf)
}

#[derive(Debug)]
pub enum TransformError {
  CannotReadReadme(PathBuf),
  IntralinkError(intralinks::IntraLinkError),
  MissingOrIllFormatMarkers,
}

impl fmt::Display for TransformError {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    match *self {
      TransformError::CannotReadReadme(ref path) => {
        write!(f, "Cannot read README at {}.", path.display())
      }
      TransformError::IntralinkError(ref err) => {
        write!(f, "Failed to process intra-links: {}", err)
      }
      TransformError::MissingOrIllFormatMarkers => {
        f.write_str("Markers not found or ill-formed; check your file again.")
      }
    }
  }
}

impl From<intralinks::IntraLinkError> for TransformError {
  fn from(err: intralinks::IntraLinkError) -> Self {
    TransformError::IntralinkError(err)
  }
}

/// Open and read a README file.
pub fn read_readme<P>(path: P) -> Result<String, TransformError>
where
  P: AsRef<Path>,
{
  let path = path.as_ref();
  let mut file = File::open(path).map_err(|_| TransformError::CannotReadReadme(path.to_owned()))?;
  let mut content = String::new();

  let _ = file.read_to_string(&mut content);

  Ok(content)
}

fn transform_doc_intralinks(
  doc: &str,
  crate_name: &str,
  entry_point: &Path,
  mut emit_warning: impl FnMut(&str),
) -> Result<String, TransformError> {
  let symbols: HashSet<FQIdentifier> = intralinks::extract_markdown_intralink_symbols(doc);
  let modules = intralinks::all_supermodules(symbols.iter());
  let symbols_type = intralinks::crate_symbols_type(
    &entry_point,
    |module| modules.contains(module),
    &mut emit_warning,
  )?;

  Ok(intralinks::rewrite_markdown_links(
    doc,
    &symbols_type,
    crate_name,
    emit_warning,
  ))
}

fn inject_doc_in_readme(content: &str, doc: &str, crlf: bool) -> Result<String, TransformError> {
  let content = content.as_ref();
  let mut marker_re_builder = RegexBuilder::new(MARKER_RE);
  marker_re_builder.multi_line(true);
  let marker_re = marker_re_builder.build().unwrap();

  if let Some(marker_match) = marker_re.find(&content) {
    // try to look for the sync marker (first time using the tool)
    let first_part = &content[0..marker_match.start()];
    let second_part = &content[if crlf {
      marker_match.end() - 1
    } else {
      marker_match.end()
    }..];

    Ok(reformat_with_markers(first_part, doc, second_part, crlf))
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
        let first_part = &content[0..start_match.start()];
        let second_part = &content[if crlf {
          end_match.end() - 1
        } else {
          end_match.end()
        }..];

        Ok(reformat_with_markers(first_part, doc, second_part, crlf))
      }

      _ => Err(TransformError::MissingOrIllFormatMarkers),
    }
  }
}

/// Transform a readme file and return its content with the documentation injected, if any.
///
/// Perform any required other transformations if asked by the user.
pub fn transform_readme<C, R, N, E>(
  content: C,
  doc: R,
  crate_name: N,
  entry_point: E,
  crlf: bool,
  emit_warning: impl FnMut(&str),
) -> Result<String, TransformError>
where
  C: AsRef<str>,
  R: AsRef<str>,
  N: AsRef<str>,
  E: AsRef<Path>,
{
  let doc = transform_doc_intralinks(
    doc.as_ref(),
    crate_name.as_ref(),
    entry_point.as_ref(),
    emit_warning,
  )?;

  inject_doc_in_readme(content.as_ref(), &doc, crlf)
}

// Reformat the README by inserting the documentation between the start and end markers.
//
// The crlf` parameter is used to insert a '\r' before '\n'.
fn reformat_with_markers(first_part: &str, doc: &str, second_part: &str, crlf: bool) -> String {
  if crlf {
    format!(
      "{}{}\r\n\r\n{}\r\n{}{}",
      first_part, MARKER_START, doc, MARKER_END, second_part
    )
  } else {
    format!(
      "{}{}\n\n{}\n{}{}",
      first_part, MARKER_START, doc, MARKER_END, second_part
    )
  }
}

fn annotate_code_blocks(st: &mut CodeBlockState, line: String, crlf: bool) -> String {
  match st {
    CodeBlockState::None => {
      if line.starts_with("~~~") {
        *st = CodeBlockState::InWithTildes;
      } else if line.starts_with("```") {
        *st = CodeBlockState::InWithBackticks;
      }

      if crlf && line.ends_with("```\r\n") {
        line.replace("\r\n", &format!("{}\r\n", RUST_LANG_ANNOTATION))
      } else if !crlf && line.ends_with("```\n") {
        line.replace("\n", &format!("{}\n", RUST_LANG_ANNOTATION))
      } else {
        line
      }
    }

    CodeBlockState::InWithTildes => {
      if line.starts_with("~~~") {
        *st = CodeBlockState::None;
      }

      line
    }

    CodeBlockState::InWithBackticks => {
      if line.starts_with("```") {
        *st = CodeBlockState::None;
      }

      line
    }
  }
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
      if line.starts_with("# ") || line.trim_end() == "#" {
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
      if line.starts_with("# ") || line.trim_end() == "#" {
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
    assert_eq!(strip_hidden_doc_tests(&mut st, "#foo"), true);
    assert_eq!(strip_hidden_doc_tests(&mut st, "#"), false);
    assert_eq!(strip_hidden_doc_tests(&mut st, "# "), false);
    assert_eq!(strip_hidden_doc_tests(&mut st, "# ### nope"), false);
    assert_eq!(strip_hidden_doc_tests(&mut st, "~~~"), true);
    assert_eq!(strip_hidden_doc_tests(&mut st, "```"), true);
    assert_eq!(strip_hidden_doc_tests(&mut st, "# still okay"), true);
  }

  #[test]
  fn simple_transform() {
    let doc = "Test! <3";
    let readme = "Foo\n<!-- cargo-sync-readme -->\nbar\nzoo";
    let output = inject_doc_in_readme(readme, doc, false);

    assert_eq!(
      output.ok().unwrap(),
      "Foo\n<!-- cargo-sync-readme start -->\n\nTest! <3\n<!-- cargo-sync-readme end -->\nbar\nzoo"
    );
  }

  #[test]
  fn windows_line_endings() {
    let doc = "Test! <3";
    let readme = "Foo\r\n<!-- cargo-sync-readme -->\r\nbar\r\nzoo";
    let output = inject_doc_in_readme(readme, doc, true);

    assert_eq!(output.ok().unwrap(), "Foo\r\n<!-- cargo-sync-readme start -->\r\n\r\nTest! <3\r\n<!-- cargo-sync-readme end -->\r\nbar\r\nzoo");
  }

  #[test]
  fn annotate_default_code_blocks() {
    let doc = "//!```\n//!fn add(a: u8, b: u8) -> u8 { a + b }\n//!```";
    let output = transform_inner_doc(doc, false, false);

    assert_eq!(
      output,
      "```rust\nfn add(a: u8, b: u8) -> u8 { a + b }\n```\n".to_owned()
    );
  }

  #[test]
  fn annotate_default_code_blocks_windows() {
    let doc = "//!```\r\n//!fn add(a: u8, b: u8) -> u8 { a + b }\r\n//!```";
    let output = transform_inner_doc(doc, false, true);

    assert_eq!(
      output,
      "```rust\r\nfn add(a: u8, b: u8) -> u8 { a + b }\r\n```\r\n".to_owned()
    );
  }

  #[test]
  fn does_not_annotate_annotated_code_blocks() {
    let doc = "//!```text\n//!echo Hello, World!\n//!```";
    let output = transform_inner_doc(doc, false, false);

    assert_eq!(output, "```text\necho Hello, World!\n```\n".to_owned());
  }

  #[test]
  fn does_not_annotate_annotated_code_blocks_windows() {
    let doc = "//!```text\r\n//!echo Hello, World!\r\n//!```";
    let output = transform_inner_doc(doc, false, true);

    assert_eq!(
      output,
      "```text\r\necho Hello, World!\r\n```\r\n".to_owned()
    );
  }
}
