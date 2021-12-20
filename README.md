<!-- cargo-sync-readme start -->

# `cargo sync-readme`

**A plugin that generates a Markdown section in your README based on your Rust documentation.**

## How does this work?

Basically, this tool provides you with a simple mechanism to synchronize your front page
documentation from your `lib.rs` or `main.rs` with a place in your *readme* file. In order to do
so, this command will parse your inner documentation (i.e. `//!`) on `lib.rs` or `main.rs` and
will output it in your *readme* file at specific markers.

## Installation

```bash
cargo install cargo-sync-readme
```

## The markers

Because you might want a specific *readme* file that adds some more information to the
documentation from your Rust code, this tool allows you to select a place where to put the
documentation. This is done with three markers:

- `<!-- cargo-sync-readme -->`: that annotation must be placed in your *readme* file where you
  want the Rust documentation to be included and synchronized.
- `<!-- cargo-sync-readme start -->`: that annotation is automatically inserted by the command
  to delimit the beginning of the synchronized documentation.
- `<!-- cargo-sync-readme end -->`: that annotation is automatically inserted by the command
  to delimit the ending of the synchronized documentation.

**You only have to use the former marker (i.e. `<!-- cargo-sync-readme -->`).** The rest of the
markers will be handled automatically for you by the tool.

> Okay, but I want to change the place of the documentation now.

When you have already put the synchronized documentation in your *readme* but want to change its
location, all you have to do is remove everything in between the start and end annotations
(annotations included) and place the `<!-- cargo-sync-readme -->` annotation wherever you want
your synchronized documentation to appear.

## How should I use this?

First, this tool will respect what you put in your `Cargo.toml`. There is a special field called
`readme` that gives the name / path of the document you want to use as *readme* file.
`cargo sync-readme` will operate on that file.

> Disclaimer: even though crates.io’s documentation and manifest format doesn’t explicitly state
> the type of this file, **`cargo sync-readme` assumes it’s Markdown.** If you want a support
> for another file type, please open an issue or a PR: those are warmly welcomed — and if you
> live in Paris, I offer you a Kwak or a Chouffe! ♥

Once you have put the annotation in your *readme* file, just run the command without argument to
perform the synchronization:

```text
cargo sync-readme
```

This will effectively update your *readme* file with the main documentation from your Rust code
(either a `lib.rs` or `main.rs`, depending on the type of your crate).

## Intra-link support

> This feature is new and lacks testing.

This tool rewrites intra-links so they point at the corresponding place in
[docs.rs](https://docs.rs). The intra-links must be of the form `[⋯](crate::⋯)`.

The regular shortcut notation (using `[foo]: crate::foo` at the end of your Markdown document
and using `[foo]` everywhere else) is not currently supported.

Links to the standard library are also supported, and they must be of the form
`[⋯](::<crate>::⋯)`, where `<crate>` is a crate that is part of the standard library, such as
`std`, `core`, or `alloc`.

Please note that there are some limitations to intra-link support. To create the links we have
to parse the source code to find out the class of the symbol being referenced (whether it is a
`struct`, `trait`, etc). That necessarily imposes some restrictions, for instance, we will not
expand macros so symbols defined in macros will not be linkable.

## Switches and options

The command has several options and flags you can use to customize the experience (a bit like a
Disneyland Parc experience, but less exciting).

- `-z` or `--show-hidden-doc`: this flag will disable a special transformation on your
  documentation when copying into the region you’ve selected in your *readme*. All
  ignored / hidden lines (the ones starting with a dash in code block in Rust doc) will simply
  be dropped by default. This might be wanted if you want your *readme* documentation to look
  like the one on docs.rs, where the hidden lines don’t show up. If you don’t, use this flag
  to disable this behavior.
- `-f` or `--prefer-doc-from`: this option allows you to override the place where to get the
  documentation from. This might be wanted to override the default behavior that reads from
  the Cargo.toml manifest, the autodetection based on files or when you have both a binary
  and library setup (in which case this option is mandatory).
- `--crlf`: this flag makes the tool’s newlines behaves according to CRLF. It will not change
  the already present newlines but expect your document to be formatted with CRLF. If it’s
  not then you will get punched in the face by a squirrel driving a motorcycle. Sorry. Also,
  it will generate newlines with CRLF.
- `-c --check`: check whether the *readme* is synchronized.

## Q/A and troubleshooting

### Are workspace crates supported?

Not yet! If you have ideas how the tool should behave with them, please contribute with an issue or
a PR!

<!-- cargo-sync-readme end -->
