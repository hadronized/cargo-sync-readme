//! Tooling to manipulate intralinks by parsing Rust code.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Range;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use syn::Ident;
use syn::Item;

use crate::WithWarnings;

#[derive(Debug)]
pub enum IntraLinkError {
  IOError(std::io::Error),
  ParseError(syn::Error),
  LoadStdLibError(String),
}

impl fmt::Display for IntraLinkError {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    match self {
      IntraLinkError::IOError(err) => write!(f, "IO error: {}", err),
      IntraLinkError::ParseError(err) => write!(f, "Failed to parse rust file: {}", err),
      IntraLinkError::LoadStdLibError(msg) => write!(f, "Failed to load standard library: {}", msg),
    }
  }
}

impl From<std::io::Error> for IntraLinkError {
  fn from(err: std::io::Error) -> Self {
    IntraLinkError::IOError(err)
  }
}

impl From<syn::Error> for IntraLinkError {
  fn from(err: syn::Error) -> Self {
    IntraLinkError::ParseError(err)
  }
}

fn file_ast<P: AsRef<Path>>(filepath: P) -> Result<syn::File, IntraLinkError> {
  let src = std::fs::read_to_string(filepath)?;

  Ok(syn::parse_file(&src)?)
}

/// Determines the module filename, which can be `<module>.rs` or `<module>/mod.rs`.
fn module_filename(dir: &Path, module: &Ident) -> Option<PathBuf> {
  let mod_file = dir.join(format!("{}.rs", module));

  if mod_file.is_file() {
    return Some(mod_file);
  }

  let mod_file = dir.join(module.to_string()).join("mod.rs");

  if mod_file.is_file() {
    return Some(mod_file);
  }

  None
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum FQIdentifierAnchor {
  Root,
  Crate,
}

/// Fully qualified identifier.
#[derive(Clone, Debug)]
pub struct FQIdentifier {
  pub anchor: FQIdentifierAnchor,

  /// This path vector can be shared and can end after the identifier we are representing.
  /// This allow us to have a faster implementation for `FQIdentifier::all_ancestors()`.
  path_shared: Rc<Vec<String>>,
  path_end: usize,
}

impl FQIdentifier {
  fn new(anchor: FQIdentifierAnchor) -> FQIdentifier {
    FQIdentifier {
      anchor,
      path_shared: Rc::new(Vec::new()),
      path_end: 0,
    }
  }

  fn root(crate_name: &str) -> FQIdentifier {
    FQIdentifier::new(FQIdentifierAnchor::Root).join(crate_name)
  }

  fn from_string(s: &str) -> Option<FQIdentifier> {
    let anchor;
    let rest;

    if s == "::" {
      return Some(FQIdentifier::new(FQIdentifierAnchor::Root));
    } else if s.starts_with("::") {
      anchor = FQIdentifierAnchor::Root;
      rest = &s[2..];
    } else if s == "crate" {
      return Some(FQIdentifier::new(FQIdentifierAnchor::Crate));
    } else if s.starts_with("crate::") {
      anchor = FQIdentifierAnchor::Crate;
      rest = &s[7..];
    } else {
      return None;
    }

    if rest.is_empty() {
      return None;
    }

    let path: Rc<Vec<String>> = Rc::new(rest.split("::").map(str::to_owned).collect());

    Some(FQIdentifier {
      anchor,
      path_end: path.len(),
      path_shared: path,
    })
  }

  fn path(&self) -> &[String] {
    &self.path_shared[0..self.path_end]
  }

  fn parent(mut self) -> Option<FQIdentifier> {
    match self.path_end {
      0 => None,
      _ => {
        self.path_end -= 1;
        Some(self)
      }
    }
  }

  fn join(mut self, s: &str) -> FQIdentifier {
    Rc::make_mut(&mut self.path_shared).push(s.to_string());
    self.path_end += 1;
    self
  }

  fn all_ancestors(&self) -> impl Iterator<Item = FQIdentifier> {
    let first_ancestor = self.clone().parent();

    std::iter::successors(first_ancestor, |ancestor| ancestor.clone().parent())
  }
}

impl PartialEq for FQIdentifier {
  fn eq(&self, other: &Self) -> bool {
    self.anchor == other.anchor && self.path() == other.path()
  }
}

impl Eq for FQIdentifier {}

impl Hash for FQIdentifier {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.anchor.hash(state);
    self.path().hash(state);
  }
}

impl fmt::Display for FQIdentifier {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
    match self.anchor {
      FQIdentifierAnchor::Root => (),
      FQIdentifierAnchor::Crate => f.write_str("crate")?,
    }

    for s in self.path().iter() {
      f.write_str("::")?;
      f.write_str(&s)?;
    }

    Ok(())
  }
}

fn is_cfg_test(attribute: &syn::Attribute) -> bool {
  let test_attribute: syn::Attribute = syn::parse_quote!(#[cfg(test)]);

  *attribute == test_attribute
}

fn traverse_module(
  ast: &Vec<Item>,
  dir: &Path,
  mod_symbol: FQIdentifier,
  asts: &mut HashMap<FQIdentifier, Vec<Item>>,
  explore_module: &impl Fn(&FQIdentifier) -> bool,
  warnings: &mut Vec<String>,
) -> Result<(), IntraLinkError> {
  if !explore_module(&mod_symbol) {
    return Ok(());
  }

  // Conditional compilation can create multiple module definitions, e.g.
  //
  // ```
  // #[cfg(foo)]
  // mod a {}
  // #[cfg(not(foo))]
  // mod a {}
  // ```
  //
  // We choose to consider the first one only.
  match asts.contains_key(&mod_symbol) {
    true => return Ok(()),
    false => asts.insert(mod_symbol.clone(), ast.clone()),
  };

  for item in ast.iter() {
    if let Item::Mod(module) = item {
      // If a module is gated by `#[cfg(test)]` we skip it.  This happens sometimes in the
      // standard library, and we want to explore the correct, non-test, module.
      if module.attrs.iter().any(is_cfg_test) {
        continue;
      }

      let child_module_symbol: FQIdentifier = mod_symbol.clone().join(&module.ident.to_string());

      match &module.content {
        Some((_, items)) => {
          traverse_module(
            &items,
            dir,
            child_module_symbol,
            asts,
            explore_module,
            warnings,
          )?;
        }
        None if explore_module(&child_module_symbol) => match module_filename(dir, &module.ident) {
          None => warnings.push(format!(
            "Unable to find module file for module {} in directory {:?}",
            child_module_symbol, dir
          )),
          Some(mod_filename) => traverse_file(
            mod_filename,
            child_module_symbol,
            asts,
            explore_module,
            warnings,
          )?,
        },
        None => (),
      }
    }
  }

  Ok(())
}

fn traverse_file<P: AsRef<Path>>(
  file: P,
  mod_symbol: FQIdentifier,
  asts: &mut HashMap<FQIdentifier, Vec<Item>>,
  explore_module: &impl Fn(&FQIdentifier) -> bool,
  warnings: &mut Vec<String>,
) -> Result<(), IntraLinkError> {
  let dir: &Path = file.as_ref().parent().expect(&format!(
    "failed to get directory of \"{:?}\"",
    file.as_ref()
  ));
  let ast: syn::File = file_ast(&file)?;

  traverse_module(&ast.items, dir, mod_symbol, asts, explore_module, warnings)
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SymbolType {
  Crate,
  Struct,
  Trait,
  Enum,
  Union,
  Type,
  Mod,
  Macro,
  Const,
  Fn,
  Static,
}

fn symbols_type(asts: &HashMap<FQIdentifier, Vec<Item>>) -> HashMap<FQIdentifier, SymbolType> {
  let mut symbols_type: HashMap<FQIdentifier, SymbolType> = HashMap::new();

  for (mod_symbol, ast) in asts.iter() {
    if *mod_symbol == FQIdentifier::new(FQIdentifierAnchor::Crate) {
      symbols_type.insert(
        FQIdentifier::new(FQIdentifierAnchor::Crate),
        SymbolType::Crate,
      );
    }

    for item in ast {
      let mut symb_type: Option<(String, SymbolType)> = None;

      match item {
        Item::Enum(e) => {
          symb_type = Some((e.ident.to_string(), SymbolType::Enum));
        }
        Item::Struct(s) => {
          symb_type = Some((s.ident.to_string(), SymbolType::Struct));
        }
        Item::Trait(t) => {
          symb_type = Some((t.ident.to_string(), SymbolType::Trait));
        }
        Item::Union(u) => {
          symb_type = Some((u.ident.to_string(), SymbolType::Union));
        }
        Item::Type(t) => {
          symb_type = Some((t.ident.to_string(), SymbolType::Type));
        }
        Item::Mod(m) => {
          symb_type = Some((m.ident.to_string(), SymbolType::Mod));
        }
        Item::Macro(syn::ItemMacro {
          ident: Some(ident), ..
        }) => {
          symb_type = Some((ident.to_string(), SymbolType::Macro));
        }
        Item::Macro2(m) => {
          symb_type = Some((m.ident.to_string(), SymbolType::Macro));
        }
        Item::Const(c) => {
          symb_type = Some((c.ident.to_string(), SymbolType::Const));
        }
        Item::Fn(f) => {
          symb_type = Some((f.sig.ident.to_string(), SymbolType::Fn));
        }
        Item::Static(s) => {
          symb_type = Some((s.ident.to_string(), SymbolType::Static));
        }

        _ => (),
      }

      if let Some((ident, typ)) = symb_type {
        symbols_type.insert(mod_symbol.clone().join(&ident), typ);
      }
    }
  }

  symbols_type
}

pub fn crate_symbols_type<P: AsRef<Path>>(
  entry_point: P,
  symbols: &HashSet<FQIdentifier>,
  warnings: &mut Vec<String>,
) -> Result<HashMap<FQIdentifier, SymbolType>, IntraLinkError> {
  let modules = all_supermodules(symbols.iter());
  let mut asts: HashMap<FQIdentifier, Vec<Item>> = HashMap::new();

  // Only load standard library information if needed.
  let std_lib_crates = match references_standard_library(&symbols) {
    true => get_standard_libraries()?,
    false => Vec::new(),
  };

  for Crate { name, entrypoint } in std_lib_crates {
    traverse_file(
      entrypoint,
      FQIdentifier::root(&name),
      &mut asts,
      &|module| modules.contains(module),
      warnings,
    )?;
  }

  traverse_file(
    entry_point,
    FQIdentifier::new(FQIdentifierAnchor::Crate),
    &mut asts,
    &|module| modules.contains(module),
    warnings,
  )?;

  Ok(symbols_type(&asts))
}

/// Create a set with all supermodules in `symbols`.  For instance, if `symbols` is
/// `{crate::foo::bar::baz, crate::baz::mumble}` it will return
/// `{crate, crate::foo, crate::foo::bar, crate::baz}`.
fn all_supermodules<'a>(symbols: impl Iterator<Item = &'a FQIdentifier>) -> HashSet<FQIdentifier> {
  symbols
    .into_iter()
    .flat_map(|s| s.all_ancestors())
    .collect()
}

#[derive(Eq, PartialEq, Debug)]
struct MarkdownInlineLink {
  text: String,
  link: String,
}

fn split_link_fragment(link: &str) -> (&str, &str) {
  match link.find('#') {
    None => (link, ""),
    Some(i) => link.split_at(i),
  }
}

fn markdown_inline_link_iterator<'a>(
  source: &'a str,
) -> impl Iterator<Item = (Span, MarkdownInlineLink)> + 'a {
  use pulldown_cmark::*;

  fn escape_markdown(str: &str, escape_chars: &str) -> String {
    let mut s = String::new();

    for c in str.chars() {
      match escape_chars.contains(c) {
        true => {
          s.push('\\');
          s.push(c);
        }
        false => s.push(c),
      }
    }

    s
  }

  let parser = Parser::new_ext(source, Options::all());
  let mut in_link = false;
  let mut text = String::new();

  parser
    .into_offset_iter()
    .filter_map(move |(event, range)| match event {
      Event::Start(Tag::Link(LinkType::Inline, ..)) => {
        in_link = true;
        None
      }
      Event::End(Tag::Link(LinkType::Inline, link, ..)) => {
        in_link = false;

        let t: String = escape_markdown(&std::mem::take(&mut text), r"\[]");
        let l: String = escape_markdown(link.as_ref(), r"\()");

        Some((range.into(), MarkdownInlineLink { text: t, link: l }))
      }
      Event::Text(s) if in_link => {
        text.push_str(&s);
        None
      }
      Event::Code(s) if in_link => {
        text.push('`');
        text.push_str(&s);
        text.push('`');
        None
      }
      _ => None,
    })
}

#[derive(Eq, PartialEq, Debug)]
pub struct Span {
  pub start: usize,
  pub end: usize,
}

impl From<Range<usize>> for Span {
  fn from(range: Range<usize>) -> Self {
    Span {
      start: range.start,
      end: range.end,
    }
  }
}

pub fn extract_markdown_intralink_symbols(doc: &str) -> HashSet<FQIdentifier> {
  let mut symbols = HashSet::new();

  for (_, MarkdownInlineLink { link, .. }) in markdown_inline_link_iterator(doc) {
    let (link, _) = split_link_fragment(&link);

    if let Some(symbol) = FQIdentifier::from_string(&link) {
      symbols.insert(symbol);
    }
  }

  symbols
}

fn documentation_url(symbol: &FQIdentifier, typ: SymbolType, crate_name: &str) -> String {
  let mut link = match symbol.anchor {
    FQIdentifierAnchor::Root => format!("https://doc.rust-lang.org/stable/"),
    FQIdentifierAnchor::Crate => format!("https://docs.rs/{}/latest/{}/", crate_name, crate_name),
  };

  if SymbolType::Crate == typ {
    return link;
  }

  for s in symbol.path().iter().rev().skip(1).rev() {
    link.push_str(s);
    link.push('/');
  }

  let name = symbol
    .path()
    .last()
    .expect(&format!("failed to get last component of {}", symbol));

  match typ {
    SymbolType::Crate => unreachable!(),
    SymbolType::Struct => link.push_str(&format!("struct.{}.html", name)),
    SymbolType::Trait => link.push_str(&format!("trait.{}.html", name)),
    SymbolType::Enum => link.push_str(&format!("enum.{}.html", name)),
    SymbolType::Union => link.push_str(&format!("union.{}.html", name)),
    SymbolType::Type => link.push_str(&format!("type.{}.html", name)),
    SymbolType::Mod => link.push_str(&format!("{}/", name)),
    SymbolType::Macro => link.push_str(&format!("macro.{}.html", name)),
    SymbolType::Const => link.push_str(&format!("const.{}.html", name)),
    SymbolType::Fn => link.push_str(&format!("fn.{}.html", name)),
    SymbolType::Static => link.push_str(&format!("static.{}.html", name)),
  }

  link
}

pub fn rewrite_markdown_links(
  doc: &str,
  symbols_type: &HashMap<FQIdentifier, SymbolType>,
  crate_name: &str,
  mut warnings: Vec<String>,
) -> WithWarnings<String> {
  let mut new_doc = String::with_capacity(doc.len());
  let mut last_span = Span { start: 0, end: 0 };

  for (span, link) in markdown_inline_link_iterator(doc) {
    new_doc.push_str(&doc[last_span.end..span.start]);

    let MarkdownInlineLink { text, link } = link;
    let (link, fragment): (&str, &str) = split_link_fragment(&link);

    match FQIdentifier::from_string(&link) {
      Some(symbol) if symbols_type.contains_key(&symbol) => {
        let typ = symbols_type[&symbol];
        let new_link = documentation_url(&symbol, typ, crate_name);

        new_doc.push_str(&format!("[{}]({}{})", text, new_link, fragment));
      }

      r => {
        if let Some(symbol) = r {
          warnings.push(format!("Could not find definition of `{}`.", symbol));
        }

        new_doc.push_str(&format!("[{}]({}{})", text, link, fragment));
      }
    }

    last_span = span;
  }

  new_doc.push_str(&doc[last_span.end..]);

  WithWarnings::new(new_doc, warnings)
}

fn get_rustc_sysroot_libraries_dir() -> Result<PathBuf, IntraLinkError> {
  use std::process::*;

  let output = Command::new("rustc")
    .args(&["--print=sysroot"])
    .output()
    .map_err(|e| IntraLinkError::LoadStdLibError(format!("failed to run rustc: {}", e)))?;

  let s = String::from_utf8(output.stdout).expect("unexpected output from rustc");
  let sysroot = PathBuf::from(s.trim());
  let src_path = sysroot
    .join("lib")
    .join("rustlib")
    .join("src")
    .join("rust")
    .join("library");

  match src_path.is_dir() {
    false => Err(IntraLinkError::LoadStdLibError(format!(
      "Cannot find rust standard library in \"{:?}\"",
      src_path
    ))),
    true => Ok(src_path),
  }
}

#[derive(Debug)]
struct Crate {
  name: String,
  entrypoint: PathBuf,
}

fn references_standard_library(symbols: &HashSet<FQIdentifier>) -> bool {
  // The only way to reference standard libraries that we support is with a intra-link of form `::⋯`.
  symbols
    .iter()
    .any(|symbol| symbol.anchor == FQIdentifierAnchor::Root)
}

fn get_standard_libraries() -> Result<Vec<Crate>, IntraLinkError> {
  let libraries_dir = get_rustc_sysroot_libraries_dir()?;
  let mut std_libs = Vec::with_capacity(32);

  for entry in std::fs::read_dir(&libraries_dir)? {
    let entry = entry?;
    let path = entry.path();
    let cargo_manifest = path.join("Cargo.toml");
    let lib_entrypoint = path.join("src").join("lib.rs");

    if cargo_manifest.is_file() && lib_entrypoint.is_file() {
      let crate_name = super::Manifest::load(&cargo_manifest)
        .map_err(|e| {
          IntraLinkError::LoadStdLibError(format!(
            "failed to load manifest in \"{:?}\": {}",
            cargo_manifest, e
          ))
        })?
        .crate_name()
        .ok_or_else(|| {
          IntraLinkError::LoadStdLibError(format!(
            "cannot get crate name from \"{:?}\"",
            cargo_manifest
          ))
        })?
        .to_owned();
      let crate_info = Crate {
        name: crate_name.to_owned(),
        entrypoint: lib_entrypoint,
      };

      std_libs.push(crate_info);
    }
  }

  Ok(std_libs)
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_markdown_link_iterator() {
    let markdown = "A [some text] [another](http://foo.com), [another][one]";

    let mut iter = markdown_inline_link_iterator(&markdown);
    let (Span { start, end }, link) = iter.next().unwrap();
    assert_eq!(
      link,
      MarkdownInlineLink {
        text: "another".to_owned(),
        link: "http://foo.com".to_owned(),
      }
    );
    assert_eq!(&markdown[start..end], "[another](http://foo.com)");

    assert_eq!(iter.next(), None);

    let markdown = "[another](http://foo.com)[another][one]";
    let mut iter = markdown_inline_link_iterator(&markdown);

    let (Span { start, end }, link) = iter.next().unwrap();
    assert_eq!(
      link,
      MarkdownInlineLink {
        text: "another".to_owned(),
        link: "http://foo.com".to_owned(),
      }
    );
    assert_eq!(&markdown[start..end], "[another](http://foo.com)");

    assert_eq!(iter.next(), None);

    let markdown = "A [some [text]], [another [text] (foo)](http://foo.com/foo(bar)), [another [] one][foo[]bar]";
    let mut iter = markdown_inline_link_iterator(&markdown);

    let (Span { start, end }, link) = iter.next().unwrap();
    assert_eq!(
      link,
      MarkdownInlineLink {
        text: r"another \[text\] (foo)".to_owned(),
        link: r"http://foo.com/foo\(bar\)".to_owned(),
      }
    );
    assert_eq!(
      &markdown[start..end],
      "[another [text] (foo)](http://foo.com/foo(bar))"
    );

    assert_eq!(iter.next(), None);

    let markdown = "A [some \\]text], [another](http://foo.\\(com\\)), [another\\]][one\\]]";
    let mut iter = markdown_inline_link_iterator(&markdown);

    let (Span { start, end }, link) = iter.next().unwrap();
    assert_eq!(
      link,
      MarkdownInlineLink {
        text: "another".to_owned(),
        link: r"http://foo.\(com\)".to_owned(),
      }
    );
    assert_eq!(&markdown[start..end], r"[another](http://foo.\(com\))");

    assert_eq!(iter.next(), None);

    let markdown = "A `this is no link [link](http://foo.com)`";
    let mut iter = markdown_inline_link_iterator(&markdown);

    assert_eq!(iter.next(), None);

    let markdown = "A\n```\nthis is no link [link](http://foo.com)\n```";
    let mut iter = markdown_inline_link_iterator(&markdown);

    assert_eq!(iter.next(), None);

    let markdown = "A [link with `code`!](http://foo.com)!";
    let mut iter = markdown_inline_link_iterator(&markdown);

    let (Span { start, end }, link) = iter.next().unwrap();
    assert_eq!(
      link,
      MarkdownInlineLink {
        text: "link with `code`!".to_owned(),
        link: "http://foo.com".to_owned(),
      }
    );
    assert_eq!(&markdown[start..end], "[link with `code`!](http://foo.com)");

    assert_eq!(iter.next(), None);
  }

  #[test]
  fn test_all_supermodules() {
    let symbols = [
      FQIdentifier::from_string("crate::foo::bar::baz").unwrap(),
      FQIdentifier::from_string("crate::baz::mumble").unwrap(),
    ];
    let expected: HashSet<FQIdentifier> = [
      FQIdentifier::from_string("crate").unwrap(),
      FQIdentifier::from_string("crate::foo").unwrap(),
      FQIdentifier::from_string("crate::foo::bar").unwrap(),
      FQIdentifier::from_string("crate::baz").unwrap(),
    ]
    .iter()
    .cloned()
    .collect();

    assert_eq!(all_supermodules(symbols.iter()), expected);
  }

  #[test]
  fn test_traverse_module_and_symbols_type() {
    let mut asts: HashMap<FQIdentifier, Vec<Item>> = HashMap::new();
    let module_skip: FQIdentifier = FQIdentifier::from_string("crate::skip").unwrap();

    let source = "
        struct AStruct {}

        mod skip {
          struct Skip {}
        }

        mod a {
          mod b {
            trait ATrait {}
          }

          struct FooStruct {}
        }
        ";

    let mut warnings = Vec::new();
    traverse_module(
      &syn::parse_file(&source).unwrap().items,
      &PathBuf::new(),
      FQIdentifier::new(FQIdentifierAnchor::Crate),
      &mut asts,
      &|m| *m != module_skip,
      &mut warnings,
    )
    .ok()
    .unwrap();

    let symbols_type: HashMap<FQIdentifier, SymbolType> = symbols_type(&asts);
    let expected: HashMap<FQIdentifier, SymbolType> = [
      (
        FQIdentifier::from_string("crate").unwrap(),
        SymbolType::Crate,
      ),
      (
        FQIdentifier::from_string("crate::AStruct").unwrap(),
        SymbolType::Struct,
      ),
      (
        FQIdentifier::from_string("crate::skip").unwrap(),
        SymbolType::Mod,
      ),
      (
        FQIdentifier::from_string("crate::a").unwrap(),
        SymbolType::Mod,
      ),
      (
        FQIdentifier::from_string("crate::a::b").unwrap(),
        SymbolType::Mod,
      ),
      (
        FQIdentifier::from_string("crate::a::b::ATrait").unwrap(),
        SymbolType::Trait,
      ),
      (
        FQIdentifier::from_string("crate::a::FooStruct").unwrap(),
        SymbolType::Struct,
      ),
    ]
    .iter()
    .cloned()
    .collect();

    assert_eq!(symbols_type, expected)
  }

  #[test]
  fn test_symbols_type_with_mod_under_cfg_test() {
    let mut asts: HashMap<FQIdentifier, Vec<Item>> = HashMap::new();

    let source = "
        #[cfg(not(test))]
        mod a {
          struct MyStruct {}
        }

        #[cfg(test)]
        mod a {
          struct MyStructTest {}
        }

        #[cfg(test)]
        mod b {
          struct MyStructTest {}
        }

        #[cfg(not(test))]
        mod b {
          struct MyStruct {}
        }
        ";

    let mut warnings = Vec::new();
    traverse_module(
      &syn::parse_file(&source).unwrap().items,
      &PathBuf::new(),
      FQIdentifier::new(FQIdentifierAnchor::Crate),
      &mut asts,
      &|_| true,
      &mut warnings,
    )
    .ok()
    .unwrap();

    let symbols_type: HashMap<FQIdentifier, SymbolType> = symbols_type(&asts);
    let expected: HashMap<FQIdentifier, SymbolType> = [
      (
        FQIdentifier::from_string("crate").unwrap(),
        SymbolType::Crate,
      ),
      (
        FQIdentifier::from_string("crate::a").unwrap(),
        SymbolType::Mod,
      ),
      (
        FQIdentifier::from_string("crate::a::MyStruct").unwrap(),
        SymbolType::Struct,
      ),
      (
        FQIdentifier::from_string("crate::b").unwrap(),
        SymbolType::Mod,
      ),
      (
        FQIdentifier::from_string("crate::b::MyStruct").unwrap(),
        SymbolType::Struct,
      ),
    ]
    .iter()
    .cloned()
    .collect();

    assert_eq!(symbols_type, expected)
  }

  #[test]
  fn test_symbols_type_multiple_module_first_wins() {
    let mut asts: HashMap<FQIdentifier, Vec<Item>> = HashMap::new();

    let source = "
        #[cfg(not(foo))]
        mod a {
          struct MyStruct {}
        }

        #[cfg(foo)]
        mod a {
          struct Skip {}
        }
        ";

    let mut warnings = Vec::new();
    traverse_module(
      &syn::parse_file(&source).unwrap().items,
      &PathBuf::new(),
      FQIdentifier::new(FQIdentifierAnchor::Crate),
      &mut asts,
      &|_| true,
      &mut warnings,
    )
    .ok()
    .unwrap();

    let symbols_type: HashMap<FQIdentifier, SymbolType> = symbols_type(&asts);
    let expected: HashMap<FQIdentifier, SymbolType> = [
      (
        FQIdentifier::from_string("crate").unwrap(),
        SymbolType::Crate,
      ),
      (
        FQIdentifier::from_string("crate::a").unwrap(),
        SymbolType::Mod,
      ),
      (
        FQIdentifier::from_string("crate::a::MyStruct").unwrap(),
        SymbolType::Struct,
      ),
    ]
    .iter()
    .cloned()
    .collect();

    assert_eq!(symbols_type, expected)
  }

  #[test]
  fn test_traverse_module_expore_lazily() {
    let symbols: HashSet<FQIdentifier> = [FQIdentifier::from_string("crate::module").unwrap()]
      .iter()
      .cloned()
      .collect();
    let modules = all_supermodules(symbols.iter());

    let mut asts: HashMap<FQIdentifier, Vec<Item>> = HashMap::new();

    let source = "
        mod module {
          struct Foo {}
        }
        ";

    let mut warnings = Vec::new();
    traverse_module(
      &syn::parse_file(&source).unwrap().items,
      &PathBuf::new(),
      FQIdentifier::new(FQIdentifierAnchor::Crate),
      &mut asts,
      &|module| modules.contains(module),
      &mut warnings,
    )
    .ok()
    .unwrap();

    let symbols_type: HashSet<FQIdentifier> = symbols_type(&asts).keys().cloned().collect();

    // We should still get `crate::module`, but nothing inside it.
    let expected: HashSet<FQIdentifier> = [
      FQIdentifier::from_string("crate").unwrap(),
      FQIdentifier::from_string("crate::module").unwrap(),
    ]
    .iter()
    .cloned()
    .collect();

    assert_eq!(symbols_type, expected);
  }

  #[test]
  fn test_documentation_url() {
    let link = documentation_url(
      &FQIdentifier::from_string("crate").unwrap(),
      SymbolType::Crate,
      "foobini",
    );
    assert_eq!(link, "https://docs.rs/foobini/latest/foobini/");

    let link = documentation_url(
      &FQIdentifier::from_string("crate::AStruct").unwrap(),
      SymbolType::Struct,
      "foobini",
    );
    assert_eq!(
      link,
      "https://docs.rs/foobini/latest/foobini/struct.AStruct.html"
    );

    let link = documentation_url(
      &FQIdentifier::from_string("crate::amodule").unwrap(),
      SymbolType::Mod,
      "foobini",
    );
    assert_eq!(link, "https://docs.rs/foobini/latest/foobini/amodule/");
  }

  #[test]
  fn test_extract_markdown_intralink_symbols() {
    let doc = "
# Foobini

This [beautiful crate](crate) is cool because it contains [modules](crate::amodule) and some
other [stuff](https://en.wikipedia.org/wiki/Stuff) as well.

Go ahead and check all the [structs in foo](crate::foo#structs).
Also check [this](::std::sync::Arc) and [this](::alloc::sync::Arc).
";

    let symbols = extract_markdown_intralink_symbols(doc);

    let expected: HashSet<FQIdentifier> = [
      FQIdentifier::from_string("crate").unwrap(),
      FQIdentifier::from_string("crate::amodule").unwrap(),
      FQIdentifier::from_string("crate::foo").unwrap(),
      FQIdentifier::from_string("::std::sync::Arc").unwrap(),
      FQIdentifier::from_string("::alloc::sync::Arc").unwrap(),
    ]
    .iter()
    .cloned()
    .collect();

    assert_eq!(symbols, expected);
  }

  #[test]
  fn test_rewrite_markdown_links() {
    let doc = r"
# Foobini

This [beautiful crate](crate) is cool because it contains [modules](crate::amodule) and some
other [stuff](https://en.wikipedia.org/wiki/Stuff) as well.

This link is [broken](crate::broken) and this is [not supported](::foo::bar), but this
should [wor\\k \[fi\]le](f\\i\(n\)e).

Go ahead and check all the [structs in foo](crate::foo#structs) specifically
[this one](crate::foo::BestStruct)
";

    let symbols_type: HashMap<FQIdentifier, SymbolType> = [
      (
        FQIdentifier::from_string("crate").unwrap(),
        SymbolType::Crate,
      ),
      (
        FQIdentifier::from_string("crate::amodule").unwrap(),
        SymbolType::Mod,
      ),
      (
        FQIdentifier::from_string("crate::foo").unwrap(),
        SymbolType::Mod,
      ),
      (
        FQIdentifier::from_string("crate::foo::BestStruct").unwrap(),
        SymbolType::Struct,
      ),
    ]
    .iter()
    .cloned()
    .collect();

    let WithWarnings {
      value: new_readme, ..
    } = rewrite_markdown_links(&doc, &symbols_type, "foobini", Vec::new());
    let expected = r"
# Foobini

This [beautiful crate](https://docs.rs/foobini/latest/foobini/) is cool because it contains [modules](https://docs.rs/foobini/latest/foobini/amodule/) and some
other [stuff](https://en.wikipedia.org/wiki/Stuff) as well.

This link is [broken](crate::broken) and this is [not supported](::foo::bar), but this
should [wor\\k \[fi\]le](f\\i\(n\)e).

Go ahead and check all the [structs in foo](https://docs.rs/foobini/latest/foobini/foo/#structs) specifically
[this one](https://docs.rs/foobini/latest/foobini/foo/struct.BestStruct.html)
";

    assert_eq!(new_readme, expected);
  }
}
