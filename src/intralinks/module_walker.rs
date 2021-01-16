use std::fmt;
use std::path::{Path, PathBuf};

use syn::Ident;
use syn::Item;

use super::FQIdentifier;

#[derive(Debug)]
pub enum ModuleWalkError {
  IOError(std::io::Error),
  ParseError(syn::Error),
}

impl fmt::Display for ModuleWalkError {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    match self {
      ModuleWalkError::IOError(err) => write!(f, "IO error: {}", err),
      ModuleWalkError::ParseError(err) => write!(f, "Failed to parse rust file: {}", err),
    }
  }
}

impl From<std::io::Error> for ModuleWalkError {
  fn from(err: std::io::Error) -> Self {
    ModuleWalkError::IOError(err)
  }
}

impl From<syn::Error> for ModuleWalkError {
  fn from(err: syn::Error) -> Self {
    ModuleWalkError::ParseError(err)
  }
}

fn file_ast<P: AsRef<Path>>(filepath: P) -> Result<syn::File, ModuleWalkError> {
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

pub fn walk_module_items(
  ast: &Vec<Item>,
  dir: &Path,
  mod_symbol: FQIdentifier,
  visit: &mut impl FnMut(&FQIdentifier, &Item),
  explore_module: &mut impl FnMut(&FQIdentifier, &syn::ItemMod) -> bool,
  warnings: &mut Vec<String>,
) -> Result<(), ModuleWalkError> {
  for item in ast.iter() {
    visit(&mod_symbol, item);

    if let Item::Mod(module) = item {
      let child_module_symbol: FQIdentifier = mod_symbol.clone().join(&module.ident.to_string());

      if explore_module(&child_module_symbol, module) {
        match &module.content {
          Some((_, items)) => {
            walk_module_items(
              &items,
              dir,
              child_module_symbol,
              visit,
              explore_module,
              warnings,
            )?;
          }
          None => match module_filename(dir, &module.ident) {
            None => warnings.push(format!(
              "Unable to find module file for module {} in directory \"{}\"",
              child_module_symbol,
              dir.display()
            )),
            Some(mod_filename) => walk_module_file(
              mod_filename,
              child_module_symbol,
              visit,
              explore_module,
              warnings,
            )?,
          },
        }
      }
    }
  }

  Ok(())
}

pub fn walk_module_file<P: AsRef<Path>>(
  file: P,
  mod_symbol: FQIdentifier,
  visit: &mut impl FnMut(&FQIdentifier, &Item),
  explore_module: &mut impl FnMut(&FQIdentifier, &syn::ItemMod) -> bool,
  warnings: &mut Vec<String>,
) -> Result<(), ModuleWalkError> {
  let dir: &Path = file.as_ref().parent().expect(&format!(
    "failed to get directory of \"{}\"",
    file.as_ref().display()
  ));
  let ast: syn::File = file_ast(&file)?;

  walk_module_items(&ast.items, dir, mod_symbol, visit, explore_module, warnings)
}
