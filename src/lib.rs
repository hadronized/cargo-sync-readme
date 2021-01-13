//! Library used to implement the cargo-sync-readme binary.

// #![deny(missing_docs)]

pub mod intralinks;

use crate::intralinks::{FQIdentifier, IntraLinkError};
use regex::RegexBuilder;
use std::{
  collections::HashSet,
  fmt,
  fs::{self, read_dir, File},
  io::{self, Read},
  path::{Path, PathBuf},
  str::FromStr,
};
use toml::{de::Error as TomlError, Value};

/// Name of the manifest containing the project metadata.
pub const MANIFEST_NAME: &str = "Cargo.toml";

/// Start marker in the README file.
pub const MARKER_START: &str = "<!-- cargo-sync-readme start -->";

/// End marker in the README file.
pub const MARKER_END: &str = "<!-- cargo-sync-readme end -->";

/// Regular expression to find the initial marker.
pub const MARKER_RE: &str = "^<!-- cargo-sync-readme -->\r?$";

/// Regular expression to find the start marker.
pub const MARKER_START_RE: &str = "^<!-- cargo-sync-readme start -->\r?$";

/// Regular expression to find the end marker.
pub const MARKER_END_RE: &str = "^<!-- cargo-sync-readme end -->\r?$";

/// Common Markdown code-block state.
///
/// This type helps track which state we are currently in when parsing code-blocks. It can either
/// be none or a code-block with either backticks (`) or tildes (~).
#[derive(Debug, PartialEq)]
enum CodeBlockState {
  /// Not currently in a code block.
  None,
  /// Currently in a code block started (and that will end) with three backticks.
  InWithBackticks,
  /// Currently in a code block started (and that will end) with three tilds.
  InWithTildes,
}

/// Possible error that might happen while looking for the project manifest.
#[derive(Debug)]
pub enum FindManifestError {
  /// No manifest exists in the directory where the search was started, nor in any of its parent directories.
  CannotFindManifest,
  /// Cannot open the manifest.
  CannotOpenManifest(PathBuf),
  /// Cannot parse the manifest.
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

/// The project manifest.
///
/// This type is used internally to retrieve various metadata on your project. The most important information for us
/// is the `readme` field, which allows us to know which file we need to synchronize.
#[derive(Debug)]
pub struct Manifest {
  /// Deserialized manifest.
  pub toml: Value,
  /// Path on the file system where the manifest exists.
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

  /// Load a manifest from the file system.
  pub fn load(path: impl AsRef<Path>) -> Result<Self, FindManifestError> {
    let path = path.as_ref();
    let mut file =
      File::open(&path).map_err(|_| FindManifestError::CannotOpenManifest(path.to_owned()))?;
    let mut file_str = String::new();
    let _ = file.read_to_string(&mut file_str);
    let toml = file_str.parse().map_err(FindManifestError::TomlError)?;

    Ok(Manifest::new(toml, path))
  }

  /// Get the TOML-formatted manifest by searching the current directory; if not found, go to the
  /// parent directory and recursively retry until one is found… eventually.
  pub fn find_manifest(dir: impl AsRef<Path>) -> Result<Self, FindManifestError> {
    let dir = dir.as_ref();

    // check the input directory
    if let Ok(mut dir_entry) = read_dir(dir) {
      // if we find the manifest file, load it
      if let Some(file_entry) = dir_entry.find(|entry| match entry {
        Ok(entry) if entry.file_name() == MANIFEST_NAME => true,
        _ => false,
      }) {
        let path = file_entry.unwrap().path();

        Manifest::load(path)
      } else {
        // go to the parent and retry there
        if let Some(parent) = dir.parent() {
          Self::find_manifest(parent)
        } else {
          // if there’s no parent, we exhausted the file system tree; hard error
          Err(FindManifestError::CannotFindManifest)
        }
      }
    } else {
      // the current directory cannot be read; hard error
      Err(FindManifestError::CannotFindManifest)
    }
  }

  /// Extract the path to the crate name from the manifest.
  pub fn crate_name(&self) -> Option<&str> {
    self
      .toml
      .get("package")
      .and_then(|p| p.get("name"))
      .and_then(Value::as_str)
  }

  /// Extract the path to the readme file from the manifest.
  ///
  /// If the readme doesn’t exist, assume `README.md`.
  pub fn readme(&self) -> PathBuf {
    let readme = self
      .toml
      .get("package")
      .and_then(|p| p.get("readme"))
      .and_then(Value::as_str)
      .unwrap_or("README.md");

    self.parent_dir.join(readme)
  }

  /// Get the path to the Rust file we want to take the documentation from.
  pub fn entry_point(&self, prefer_doc_from: Option<PreferDocFrom>) -> Option<PathBuf> {
    // check first whether the information is in the manifest; if it’s not, we can check manually on the file system
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

  /// Get the path to the Rust file to extract documentation from based on the manifest.
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
  /// Take the documentation from the binary entry-point.
  ///
  /// Most of the time, this file will be `src/main.rs`.
  Binary,

  /// Take the documentation from the library entry-point.
  ///
  /// Most of the time, this file will be `src/lib.rs`.
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

/// Apply a series of transformation on the inner documentation of the entry point to adapt it to being embedded in a
/// README.
///
/// This function will perform a bunch of transformations, such as – non-comprehensive list:
///
/// - Removing the `//!` annotations at the beginning of the lines.
/// - Respecting the options of showing or hiding hidden Rust code (e.g. `# Something like this`).
/// - Map correctly the code block languages used to respect doctest annotations.
/// - Etc. etc.
fn transform_inner_doc(doc: &str, show_hidden_doc: bool, crlf: bool) -> String {
  // trim the module’s lines’ beginnings and extract the module’s documentation; this one starts at the first line
  // starting with `//!` and ends when a line doesn’t start with `//!` — note that we do not support any kind of other
  // annotations so far
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

  // find the minimal offset of all lines for which the first character is not a space; that offset will be used later
  // to preserve indentation in Rust code (so we don’t have to trim and lose all indentation levels)
  let offset = lines
    .iter()
    .flat_map(|line| line.find(|c: char| !c.is_whitespace()))
    .min()
    .unwrap_or(0);

  // cut the beginning of the each line and annotate code blocks
  let mut codeblock_st = CodeBlockState::None;
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

  // finally, eventually show hidden documentation if asked
  if show_hidden_doc {
    sanitized_annotated_lines.into_iter().collect()
  } else {
    sanitized_annotated_lines
      .into_iter()
      .filter(|l| strip_hidden_doc_tests(&mut codeblock_st, l))
      .collect()
  }
}

/// Errors that might happen while transforming documentation.
#[derive(Debug)]
pub enum TransformError {
  /// Cannot read the Rust entry-point file containing the inner documentation.
  CannotReadEntryPoint(PathBuf, io::Error),
  /// Cannot read the README file.
  CannotReadReadme(PathBuf, io::Error),
  /// Intra-link error which occurred while transforming the readme documentation.
  IntralinkError(intralinks::IntraLinkError),
  /// Initial, start and/or end markers missing and/or ill-formatted.
  MissingOrIllFormedMarkers,
}

impl fmt::Display for TransformError {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    match *self {
      TransformError::CannotReadEntryPoint(ref path, ref err) => {
        write!(f, "Cannot read entry-point at {}: {}", path.display(), err)
      }

      TransformError::CannotReadReadme(ref path, ref err) => {
        write!(f, "Cannot read README at {}: {}", path.display(), err)
      }

      TransformError::IntralinkError(ref err) => {
        write!(f, "Failed to process intra-links: {}", err)
      }

      TransformError::MissingOrIllFormedMarkers => {
        f.write_str("Markers not found or ill-formed; check your file again")
      }
    }
  }
}

impl From<IntraLinkError> for TransformError {
  fn from(err: IntraLinkError) -> Self {
    TransformError::IntralinkError(err)
  }
}

/// Open a Rust file and get its main inner documentation (//!), applying filters if needed.
pub fn extract_inner_doc(
  path: impl AsRef<Path>,
  show_hidden_doc: bool,
  crlf: bool,
) -> Result<String, TransformError> {
  let path = path.as_ref();
  let doc_path = fs::read_to_string(path)
    .map_err(|e| TransformError::CannotReadEntryPoint(path.to_owned(), e))?;
  let transformed = transform_inner_doc(&doc_path, show_hidden_doc, crlf);

  Ok(transformed)
}

/// Open and read a README file.
pub fn read_readme(path: impl AsRef<Path>) -> Result<String, TransformError> {
  let path = path.as_ref();
  fs::read_to_string(path).map_err(|e| TransformError::CannotReadReadme(path.to_owned(), e))
}

/// Rewrite intralinks found in the Markdown README.
fn transform_doc_intralinks(
  doc: &str,
  crate_name: &str,
  entry_point: &Path,
) -> Result<WithWarnings<String>, TransformError> {
  let symbols: HashSet<FQIdentifier> = intralinks::extract_markdown_intralink_symbols(doc);
  let mut warnings = Vec::new();
  let symbols_type = intralinks::crate_symbols_type(&entry_point, &symbols, &mut warnings)?;

  Ok(intralinks::rewrite_markdown_links(
    doc,
    &symbols_type,
    crate_name,
    warnings,
  ))
}

/// Look for the markers in the README and inject the transformed documentation at the right place.
fn inject_doc_in_readme(content: &str, doc: &str, crlf: bool) -> Result<String, TransformError> {
  let content = content.as_ref();
  let mut marker_re_builder = RegexBuilder::new(MARKER_RE);
  marker_re_builder.multi_line(true);
  let marker_re = marker_re_builder.build().unwrap();

  if let Some(marker_match) = marker_re.find(&content) {
    // try to look for the sync marker (first time using the tool)
    let first_part = &content[0..marker_match.start()];
    let second_part_off = if crlf {
      marker_match.end() - 1
    } else {
      marker_match.end()
    };
    let second_part = &content[second_part_off..];

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
        let second_part_off = if crlf {
          end_match.end() - 1
        } else {
          end_match.end()
        };
        let second_part = &content[second_part_off..];

        Ok(reformat_with_markers(first_part, doc, second_part, crlf))
      }

      _ => Err(TransformError::MissingOrIllFormedMarkers),
    }
  }
}

/// An object with warnings accumulated while creating this object.
pub struct WithWarnings<A> {
  pub value: A,
  pub warnings: Vec<String>,
}

impl<A> WithWarnings<A> {
  pub fn new(value: A, warnings: Vec<String>) -> Self {
    Self { value, warnings }
  }
}

/// Transform a readme and return its content with the documentation injected, if any.
///
/// Perform any required other transformations if asked by the user.
pub fn transform_readme(
  content: impl AsRef<str>,
  readme: impl AsRef<str>,
  crate_name: impl AsRef<str>,
  entry_point: impl AsRef<Path>,
  crlf: bool,
) -> Result<WithWarnings<String>, TransformError> {
  let WithWarnings {
    value: readme,
    warnings,
  } = transform_doc_intralinks(readme.as_ref(), crate_name.as_ref(), entry_point.as_ref())?;

  let injected_readme = inject_doc_in_readme(content.as_ref(), &readme, crlf)?;
  let readme = WithWarnings::new(injected_readme, warnings);
  Ok(readme)
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

/// Annotate code blocks for lines.
///
/// This function is expected to be called while iterating sequentially on lines, as it mutates its argument to
/// accumulate the code block state. If it encounters a code block annotation, it will automatically accumulate the
/// state and transform the lines to reflect the annotations.
fn annotate_code_blocks(st: &mut CodeBlockState, line: String, crlf: bool) -> String {
  match st {
    CodeBlockState::None => {
      if line.starts_with("~~~") {
        *st = CodeBlockState::InWithTildes;
      } else if line.starts_with("```") {
        *st = CodeBlockState::InWithBackticks;
      } else {
        // not a code block annotation; skip
        return line;
      }

      // language used in the code block; e.g. ```<lang>
      // some “languages” are not really languages but doctest annotations, such as should_panic; in this case, we
      // remap them to “rust”
      if crlf && line.ends_with("\r\n") {
        let lang = remap_code_block_lang(&line[3..line.len() - 2]);
        format!("{}{}\r\n", &line[..3], lang)
      // line.replace("\r\n", &format!("{}\r\n", lang))
      } else if !crlf && line.ends_with("\n") {
        let lang = remap_code_block_lang(&line[3..line.len() - 1]);
        format!("{}{}\n", &line[..3], lang)
      // line.replace("\n", &format!("{}\n", lang))
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

/// Map a code block language to its target code block language.
///
/// Most of the time, this function will be the identity function, but some language are doctest attributes that need
/// to be remapped to the correct language (most of the time, it will be rust).
fn remap_code_block_lang(lang: &str) -> &str {
  match lang {
    // no lang is Rust by default; the rest are doctest attributes
    "" | "ignore" | "should_panic" | "no_run" | "compile_fail" | "edition2015" | "edition2018" => {
      "rust"
    }

    _ => lang,
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
