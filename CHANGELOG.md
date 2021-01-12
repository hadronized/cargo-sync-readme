# 1.1

> Tue Jan 12, 2021

## Minor changes

- Add support for intralinks in the generated documentation in the README. This allows to point correctly to the right 
  docs.rs link while visiting the README of the project you used `cargo sync-readme` on.

## Patch changes

- Fix a bug where hidden code was not removed when the commented line was empty.
- Bump `regex` to `1.4.3`.
- Bump `struct-opt` to `0.3.21`.
- Bump `toml` to `0.5.8`.
- Bump `syn` to `1.0.56`.
- Bump `itertools` to `0.10`.

# 1.0

> Sun Apr 26th 2020

## Major changes

- The meaning of the triple backtick (\`) or triple tilde (~) has changed. By default now, not
  putting any _language_ annotation assumes Rust — as this is taken from a `lib.rs` or `main.rs`.
  The generated README content will then have annotation like:
  ~~~
  ```rust
  // content here
  ```
  ~~~
  If you would like to use something else, you can use a language of your choice: it will not be
  transformed to Rust:
  ~~~
  ```text
  // content here
  ```
  ~~~

## Minor changes

- Bump `regex` from `1.1.6` to `1.3.7`.
- Bump `toml` from `0.5.5` to `0.5.6`.
- Add CI scripts and dependabot.
- Binary dependencies are now optional if one is interested into only building the library.

# 0.2.1

> Wed August 7th 2019

- Fix a bug that would drop `//!` lines starting with whites.

# 0.2

> Sun May 19th 2019

- Change the meaning of the `-z` flag. Stripping hidden Rust doc lines is now enabled by default,
  as it is a better logical default. `-z` disable stripping and will show the hidden lines.
- Introduce the `-c --check` switch that will make the tool behave in a *dry run* by checking
  whether the *readme* file is correctly synchronized.

# 0.1.5

> Tue May 14th 2019

- Change the handling of newlines and internal algorithms to look for markers.
- Add the `--crlf` switch to treat newlines as CRLF.
- Add the `-f --prefer-doc-from` option. This allows people to select which file the documentation
  should be picked from. It can either be `bin` for binary (i.e. by default, `src/main.rs`) or
  `lib` for library (`src/lib.rs`). The regular ways works (Cargo.toml file parsing and/or file
  detection). This option should be useful when you have a crate with both a binary and library.

# 0.1.4

> Tue May 7th 2019

- Fix a bug with the dash (ignore doc test with `-z`) that would prevent `#![…]` for instance to
  be copied.

# 0.1.3

> Thu May 2nd 2019

- Add the `-z` switch to strip hidden lines in Rust documentation (those starting with a dash
  `#`).

# 0.1.2

> Mon Mar 4th 2019

- Fix a trim bug that would cause the synchronized documentation to be completely aligned on the
  left-most side.

# 0.1.1

> Mon Feb 25th 2019

- Fix the `cargo` subcommand incompatibility. You should now be able to run `cargo sync-readme`.

# 0.1

> Mon Feb 25th 2019

- Initial revision.
