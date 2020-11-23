use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};
use std::rc::Rc;
use syn::export::fmt::Display;
use syn::export::{Debug, Formatter};
use syn::Ident;
use syn::Item;

#[derive(Debug)]
pub enum IntraLinkError {
  IOError(std::io::Error),
  ParseError(syn::Error),
  NoModuleFile(String, PathBuf),
}

impl fmt::Display for IntraLinkError {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    match self {
      IntraLinkError::IOError(err) => write!(f, "IO error: {}", err),
      IntraLinkError::ParseError(err) => write!(f, "Failed to parse rust file: {}", err),
      IntraLinkError::NoModuleFile(module, dir) => write!(
        f,
        "Unable to find module file for module {} in directory {:?}",
        module, dir
      ),
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
#[derive(Clone)]
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

impl Display for FQIdentifier {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
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

impl Debug for FQIdentifier {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    Display::fmt(self, f)
  }
}

fn traverse_module(
  ast: &Vec<Item>,
  dir: &Path,
  mod_symbol: FQIdentifier,
  asts: &mut HashMap<FQIdentifier, Vec<Item>>,
  explore_module: &impl Fn(&FQIdentifier) -> bool,
) -> Result<(), IntraLinkError> {
  if !explore_module(&mod_symbol) {
    return Ok(());
  }

  asts.insert(mod_symbol.clone(), ast.clone());

  for item in ast.iter() {
    if let Item::Mod(module) = item {
      let module_symbol: FQIdentifier = mod_symbol.clone().join(&module.ident.to_string());

      match &module.content {
        Some((_, items)) => {
          traverse_module(&items, dir, module_symbol, asts, explore_module)?;
        }
        None if explore_module(&module_symbol) => {
          let mod_filename = match module_filename(dir, &module.ident) {
            None => Err(IntraLinkError::NoModuleFile(
              module.ident.to_string(),
              dir.to_path_buf(),
            )),
            Some(f) => Ok(f),
          }?;

          traverse_file(mod_filename, module_symbol, asts, explore_module)?;
        }
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
) -> Result<(), IntraLinkError> {
  let dir: &Path = file.as_ref().parent().expect(&format!(
    "failed to get directory of \"{:?}\"",
    file.as_ref()
  ));
  let ast: syn::File = file_ast(&file)?;

  traverse_module(&ast.items, dir, mod_symbol, asts, explore_module)
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
  explore_module: impl Fn(&FQIdentifier) -> bool,
) -> Result<HashMap<FQIdentifier, SymbolType>, IntraLinkError> {
  let mut asts: HashMap<FQIdentifier, Vec<Item>> = HashMap::new();

  traverse_file(
    entry_point,
    FQIdentifier::new(FQIdentifierAnchor::Crate),
    &mut asts,
    &explore_module,
  )?;

  Ok(symbols_type(&asts))
}

/// Create a set with all supermodules in `symbols`.  For instance, if `symbols` is
/// `{crate::foo::bar::baz, crate::baz::mumble}` it will return
/// `{crate, crate::foo, crate::foo::bar, crate::baz}`.
pub fn all_supermodules<'a>(
  symbols: impl Iterator<Item = &'a FQIdentifier>,
) -> HashSet<FQIdentifier> {
  symbols
    .into_iter()
    .flat_map(|s| s.all_ancestors())
    .collect()
}

#[derive(Eq, PartialEq, Debug)]
enum MarkdownLink<'a> {
  /// Links like [ref], or [text][ref].
  Ref {
    text: Option<&'a str>,
    reference: &'a str,
  },
  /// Links like [text](link).
  Inline { text: &'a str, link: &'a str },
}

fn split_link_fragment<'a>(link: &'a str) -> (&'a str, &'a str) {
  match link.find('#') {
    None => (link, ""),
    Some(i) => link.split_at(i),
  }
}

struct MarkdownLinkIterator<'a> {
  source: &'a str,
  iter: std::iter::Enumerate<std::str::Bytes<'a>>,
}

impl<'a> MarkdownLinkIterator<'a> {
  fn new(source: &'a str) -> MarkdownLinkIterator<'a> {
    MarkdownLinkIterator {
      source,
      iter: source.bytes().enumerate(),
    }
  }
}

#[derive(Eq, PartialEq, Debug)]
pub struct Span {
  pub start: usize,
  pub end: usize,
}

impl<'a> Iterator for MarkdownLinkIterator<'a> {
  type Item = (Span, MarkdownLink<'a>);

  fn next(&mut self) -> Option<Self::Item> {
    let mut escape = 0;
    let mut state = 0;
    let mut nest_level = 0;
    let mut start: Option<usize> = None;
    let mut first_component: Option<&str> = None;

    // This works well with UTF-8 because we just look for symbols that are ASCII, which means
    // they start with a 0 bit.  In UTF-8 codepoints that start with a 0 bit are ASCII codepoints,
    // which means that when we match some specific char in the loop below we actually know for
    // sure we are dealing with the right symbol.

    while let Some((i, c)) = self.iter.next() {
      match c {
        _ if escape > 0 => escape -= 1,
        b'\\' => escape = 1,

        b'[' if state == 0 => {
          state = 1;
          start = Some(i);
        }

        b'[' if state == 1 => nest_level += 1,
        b']' if state == 1 && nest_level > 0 => nest_level -= 1,
        b']' if state == 1 => {
          state = 2;
          first_component = Some(&self.source[start.unwrap() + 1..i]);
        }

        b'(' if state == 2 => state = 3,
        b'[' if state == 2 => state = 4,
        _ if state == 2 => {
          let span = Span {
            start: start.unwrap(),
            end: i,
          };
          return Some((
            span,
            MarkdownLink::Ref {
              text: None,
              reference: first_component.unwrap(),
            },
          ));
        }

        b'(' if state == 3 => nest_level += 1,
        b')' if state == 3 && nest_level > 0 => nest_level -= 1,
        b')' if state == 3 => {
          let span = Span {
            start: start.unwrap(),
            end: i + 1,
          };
          let text = first_component.unwrap();
          let link = &self.source[start.unwrap() + text.len() + 3..i];
          return Some((span, MarkdownLink::Inline { text, link }));
        }

        b'[' if state == 4 => nest_level += 1,
        b']' if state == 4 && nest_level > 0 => nest_level -= 1,
        b']' if state == 4 => {
          let span = Span {
            start: start.unwrap(),
            end: i + 1,
          };
          let text = first_component.unwrap();
          let reference = &self.source[start.unwrap() + text.len() + 3..i];
          return Some((
            span,
            MarkdownLink::Ref {
              text: Some(text),
              reference,
            },
          ));
        }

        _ => (),
      }
    }

    None
  }
}

pub fn extract_markdown_intralink_symbols(doc: &str) -> HashSet<FQIdentifier> {
  let mut symbols = HashSet::new();

  for (_, link) in MarkdownLinkIterator::new(doc) {
    if let MarkdownLink::Inline { link, .. } = link {
      let (link, _) = split_link_fragment(link);

      if let Some(symbol) = FQIdentifier::from_string(&link) {
        if let FQIdentifierAnchor::Crate = symbol.anchor {
          symbols.insert(symbol);
        }
      }
    }
  }

  symbols
}

fn documentation_url(symbol: &FQIdentifier, typ: SymbolType, crate_name: &str) -> String {
  let mut link = format!("https://docs.rs/{}/latest/{}/", crate_name, crate_name);

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
  mut emit_warning: impl FnMut(&str),
) -> String {
  let mut new_doc = String::with_capacity(doc.len());
  let mut last_span = Span { start: 0, end: 0 };

  for (span, link) in MarkdownLinkIterator::new(doc) {
    new_doc.push_str(&doc[last_span.end..span.start]);

    match link {
      MarkdownLink::Ref {
        text: None,
        reference,
      } => new_doc.push_str(&format!("[{}]", reference)),
      MarkdownLink::Ref {
        text: Some(t),
        reference,
      } => new_doc.push_str(&format!("[{}][{}]", t, reference)),
      MarkdownLink::Inline { text, link } => {
        let (link, fragment): (&str, &str) = split_link_fragment(link);

        match FQIdentifier::from_string(&link) {
          Some(symbol) if symbols_type.contains_key(&symbol) => {
            let typ = symbols_type[&symbol];
            let new_link = documentation_url(&symbol, typ, crate_name);

            new_doc.push_str(&format!("[{}]({}{})", text, new_link, fragment));
          }
          r => {
            if let Some(symbol) = r {
              match symbol.anchor {
                FQIdentifierAnchor::Root => {
                  emit_warning(&format!(
                    "Absolute intra-links are not yet supported.  Skipping `{}`.",
                    symbol
                  ));
                }
                FQIdentifierAnchor::Crate => {
                  emit_warning(&format!("Could not find `{}` in the code.", symbol));
                }
              }
            }

            new_doc.push_str(&format!("[{}]({}{})", text, link, fragment));
          }
        }
      }
    }

    last_span = span;
  }

  new_doc.push_str(&doc[last_span.end..]);

  new_doc
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_markdown_link_iterator() {
    let markdown = "A [some text] [another](http://foo.com), [another][one]";

    let mut iter = MarkdownLinkIterator::new(&markdown);

    let (Span { start, end }, link) = iter.next().unwrap();
    assert_eq!(
      link,
      MarkdownLink::Ref {
        text: None,
        reference: &"some text"
      }
    );
    assert_eq!(&markdown[start..end], "[some text]");

    let (Span { start, end }, link) = iter.next().unwrap();
    assert_eq!(
      link,
      MarkdownLink::Inline {
        text: &"another",
        link: &"http://foo.com"
      }
    );
    assert_eq!(&markdown[start..end], "[another](http://foo.com)");

    let (Span { start, end }, link) = iter.next().unwrap();
    assert_eq!(
      link,
      MarkdownLink::Ref {
        text: Some(&"another"),
        reference: &"one"
      }
    );
    assert_eq!(&markdown[start..end], "[another][one]");

    assert_eq!(iter.next(), None);

    let markdown = "[another](http://foo.com)[another][one]";

    let mut iter = MarkdownLinkIterator::new(&markdown);

    let (Span { start, end }, link) = iter.next().unwrap();
    assert_eq!(
      link,
      MarkdownLink::Inline {
        text: &"another",
        link: &"http://foo.com"
      }
    );
    assert_eq!(&markdown[start..end], "[another](http://foo.com)");

    let (Span { start, end }, link) = iter.next().unwrap();
    assert_eq!(
      link,
      MarkdownLink::Ref {
        text: Some(&"another"),
        reference: &"one"
      }
    );
    assert_eq!(&markdown[start..end], "[another][one]");

    assert_eq!(iter.next(), None);

    let markdown = "A [some [text]], [another [text] (foo)](http://foo.com/foo(bar)), [another [] one][foo[]bar]";

    let mut iter = MarkdownLinkIterator::new(&markdown);

    let (Span { start, end }, link) = iter.next().unwrap();
    assert_eq!(
      link,
      MarkdownLink::Ref {
        text: None,
        reference: &"some [text]"
      }
    );
    assert_eq!(&markdown[start..end], "[some [text]]");

    let (Span { start, end }, link) = iter.next().unwrap();
    assert_eq!(
      link,
      MarkdownLink::Inline {
        text: &"another [text] (foo)",
        link: &"http://foo.com/foo(bar)"
      }
    );
    assert_eq!(
      &markdown[start..end],
      "[another [text] (foo)](http://foo.com/foo(bar))"
    );

    let (Span { start, end }, link) = iter.next().unwrap();
    assert_eq!(
      link,
      MarkdownLink::Ref {
        text: Some(&"another [] one"),
        reference: &"foo[]bar"
      }
    );
    assert_eq!(&markdown[start..end], "[another [] one][foo[]bar]");

    assert_eq!(iter.next(), None);

    let markdown = "A [some \\]text], [another](http://foo.com\\)), [another\\]][one\\]]";

    let mut iter = MarkdownLinkIterator::new(&markdown);

    let (Span { start, end }, link) = iter.next().unwrap();
    assert_eq!(
      link,
      MarkdownLink::Ref {
        text: None,
        reference: &"some \\]text"
      }
    );
    assert_eq!(&markdown[start..end], "[some \\]text]");

    let (Span { start, end }, link) = iter.next().unwrap();
    assert_eq!(
      link,
      MarkdownLink::Inline {
        text: &"another",
        link: &"http://foo.com\\)"
      }
    );
    assert_eq!(&markdown[start..end], "[another](http://foo.com\\))");

    let (Span { start, end }, link) = iter.next().unwrap();
    assert_eq!(
      link,
      MarkdownLink::Ref {
        text: Some(&"another\\]"),
        reference: &"one\\]"
      }
    );
    assert_eq!(&markdown[start..end], "[another\\]][one\\]]");

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

    traverse_module(
      &syn::parse_file(&source).unwrap().items,
      &PathBuf::new(),
      FQIdentifier::new(FQIdentifierAnchor::Crate),
      &mut asts,
      &|m| *m != module_skip,
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

    traverse_module(
      &syn::parse_file(&source).unwrap().items,
      &PathBuf::new(),
      FQIdentifier::new(FQIdentifierAnchor::Crate),
      &mut asts,
      &|module| modules.contains(module),
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

        This [this crate](crate) is cool because it contains [modules](crate::amodule) and some
        other [stuff](https://en.wikipedia.org/wiki/Stuff) as well.

        Go ahead and check all the [structs in foo](crate::foo#structs)
        ";

    let symbols = extract_markdown_intralink_symbols(doc);

    let expected: HashSet<FQIdentifier> = [
      FQIdentifier::from_string("crate").unwrap(),
      FQIdentifier::from_string("crate::amodule").unwrap(),
      FQIdentifier::from_string("crate::foo").unwrap(),
    ]
    .iter()
    .cloned()
    .collect();

    assert_eq!(symbols, expected);
  }

  #[test]
  fn test_rewrite_markdown_links() {
    let doc = "
        # Foobini

        This [this crate](crate) is cool because it contains [modules](crate::amodule) and some
        other [stuff](https://en.wikipedia.org/wiki/Stuff) as well.

        This link is [broken](crate::broken) and this is [not supported](::foo::bar).

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

    let new_readme = rewrite_markdown_links(&doc, &symbols_type, "foobini", |_| ());
    let expected = "
        # Foobini

        This [this crate](https://docs.rs/foobini/latest/foobini/) is cool because it contains [modules](https://docs.rs/foobini/latest/foobini/amodule/) and some
        other [stuff](https://en.wikipedia.org/wiki/Stuff) as well.

        This link is [broken](crate::broken) and this is [not supported](::foo::bar).

        Go ahead and check all the [structs in foo](https://docs.rs/foobini/latest/foobini/foo/#structs) specifically
        [this one](https://docs.rs/foobini/latest/foobini/foo/struct.BestStruct.html)
        ";

    assert_eq!(new_readme, expected);
  }
}
