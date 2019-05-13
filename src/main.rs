//! # `cargo sync-readme`
//!
//! **A plugin that generates a Markdown section in your README based on your Rust documentation.**
//!
//! ## How does this work?
//!
//! Basically, this tool provides you with a simple mechanism to synchronize your front page
//! documentation from your `lib.rs` or `main.rs` with a place in your *readme* file. In order to do
//! so, this command will parse your inner documentation (i.e. `//!`) on `lib.rs` or `main.rs` and
//! will output it in your *readme* file at specific markers.
//!
//! ## The markers
//!
//! Because you might want a specific *readme* file that adds some more information to the
//! documentation from your Rust code, this tool allows you to select a place where to put the
//! documentation. This is done with three markers:
//!
//!   - `<!-- cargo-sync-readme -->`: that annotation must be placed in your *readme* file where you
//!     want the Rust documentation to be included and synchronized.
//!   - `<!-- cargo-sync-readme start -->`: that annotation is automatically inserted by the command
//!     to delimit the beginning of the synchronized documentation.
//!   - `<!-- cargo-sync-readme end -->`: that annotation is automatically inserted by the command
//!     to delimit the ending of the synchronized documentation.
//!
//! **You only have to use the former marker (i.e. `<!-- cargo-sync-readme -->`).** The rest of the
//! markers will be handled automatically for you by the tool.
//!
//! > Okay, but I want to change the place of the documentation now.
//!
//! When you have already put the synchronized documentation in your *readme* but want to change its
//! location, all you have to do is remove everything in between the start and end annotations
//! (annotations included) and place the `<!-- cargo-sync-readme -->` annotation wherever you want
//! your synchronized documentation to appear.
//!
//! ## How should I use this?
//!
//! First, this tool will respect what you put in your `Cargo.toml`. There is a special field called
//! `readme` that gives the name / path of the document you want to be used as *readme* file.
//! `cargo sync-readme` will operate on that file.
//!
//! > Disclaimer: even though crates.io’s documentation and manifest format doesn’t explicitly state
//! > the type of this file, **`cargo sync-readme` assumes it’s Markdown.** If you want a support
//! > for another file type, please open an issue or a PR: those are warmly welcomed — and if you
//! > live in Paris, I offer you a Kwak or a Chouffe! ♥
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
//! ## Switches and options
//!
//! The command has several options and flags you can use to customize the experience (a bit like a
//! Disneyland Parc experience, but less exciting).
//!
//!   - `-z` or `--strip-hidden-doc`: this flag will perform a special transformation on your
//!     documentation when copying into the region you’ve selected in your *readme*. All
//!     ignored / hidden lines (the ones starting with a dash in code block in Rust doc) will simply
//!     be dropped. This might be wanted if you want your *readme* documentation to look like the
//!     one on docs.rs, where the hidden lines don’t show up.
//!   - `-f` or `--prefer-doc-from`: this option allows you to override the place where to get the
//!     documentation from. This might be wanted to override the default behavior that reads from
//!     the Cargo.toml manifest, the autodetection based on files or when you have both a binary
//!     and library setup (in which case this option is mandatory).
//!   - `--crlf`: this flag makes the tool’s newlines behaves according to CRLF. It will not change
//!     the already present newlines but expect your document to be formatted with CRLF. If it’s
//!     not then you will get punched in the face by a squirrel driving a motorcycle. Sorry. Also,
//!     it will generate newlines with CRLF.
//!
//! ## Q/A and troubleshooting
//!
//! ### Are workspace crates supported?
//!
//! Not yet! If you have ideas how the tool should behave with them, please contribute with an issue or
//! a PR!
//!
//! ### There are ugly lines starting with a dash (#) in the generated Rust code (examples)!
//!
//! This is likely to be the hidden documentation feature from `rustdoc`. To fix this problem,
//! re-run with:
//!
//! ```
//! cargo sync-readme -z
//! ```

use std::env::current_dir;
use std::fs::File;
use std::io::Write;
use std::process;
use structopt::StructOpt;

use cargo_sync_readme::{
  Manifest, PreferDocFrom, extract_inner_doc, read_readme, transform_readme
};

#[derive(Debug, StructOpt)]
#[structopt(name = "cargo-sync-readme")]
enum CliOpt {
  #[structopt(
    name = "sync-readme",
    about = "Generate a Markdown section in your README based on your Rust documentation.",
  )]
  SyncReadme {
    #[structopt(
      short = "z",
      long = "strip-hidden-doc",
      help = "Strip Rust hidden documentation lines in the generated README.",
    )]
    strip_hidden_doc: bool,

    #[structopt(
      short = "f",
      long = "prefer-doc-from",
      help = "Set to either `bin` or `lib` to instruct sync-readme which file it should read documentation from.",
    )]
    prefer_doc_from: Option<PreferDocFrom>,

    #[structopt(
      long = "crlf",
      help = "Generate documentation with CRLF for Windows-style line endings. This will not affect the already present newlines.",
    )]
    crlf: bool,
  }
}

const CANNOT_FIND_ENTRY_POINT_ERR_STR: &str = "\
Cannot find entry point (default to src/lib.rs or src/main.rs). This is likely to be due to a
special configuration in your Cargo.toml manifest file or you’re just missing the entry point
files.

If you’re in the special situation where your crate defines both a binary and a library, you should
consider using the -f option to hint sync-readme which file it should read the documentation from.";

fn main() {
  let cli_opt = CliOpt::from_args();
  let CliOpt::SyncReadme { strip_hidden_doc, prefer_doc_from, crlf } = cli_opt;

  if let Ok(pwd) = current_dir() {
    match Manifest::find_manifest(pwd) {
      Ok(ref manifest) => {
        let entry_point = manifest.entry_point(prefer_doc_from);

        if let Some(entry_point) = entry_point {
          let doc = extract_inner_doc(entry_point, strip_hidden_doc, crlf);
          let readme_path = manifest.readme();

          match read_readme(&readme_path).and_then(|readme| transform_readme(&readme, doc, crlf)) {
            Ok(new_readme) => {
              let mut file = File::create(readme_path).unwrap();
              let _ = file.write_all(new_readme.as_bytes());
            }

            Err(e) => eprintln!("{}", e)
          }
        } else {
          eprintln!("{}", CANNOT_FIND_ENTRY_POINT_ERR_STR);
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

