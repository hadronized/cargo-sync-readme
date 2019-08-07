## 0.2.1

> Wed August 7th 2019

  - Fix a bug that would drop `//!` lines starting with whites.

# 0.2

> Sun May 19th 2019

  - Change the meaning of the `-z` flag. Stripping hidden Rust doc lines is now enabled by default,
    as it is a better logical default. `-z` disable stripping and will show the hidden lines.
  - Introduce the `-c --check` switch that will make the tool behave in a *dry run* by checking
    whether the *readme* file is correctly synchronized.

## 0.1.5

> Tue May 14th 2019

  - Change the handling of newlines and internal algorithms to look for markers.
  - Add the `--crlf` switch to treat newlines as CRLF.
  - Add the `-f --prefer-doc-from` option. This allows people to select which file the documentation
    should be picked from. It can either be `bin` for binary (i.e. by default, `src/main.rs`) or
    `lib` for library (`src/lib.rs`). The regular ways works (Cargo.toml file parsing and/or file
    detection). This option should be useful when you have a crate with both a binary and library.

## 0.1.4

> Tue May 7th 2019

  - Fix a bug with the dash (ignore doc test with `-z`) that would prevent `#![…]` for instance to
    be copied.

## 0.1.3

> Thu May 2nd 2019

  - Add the `-z` switch to strip hidden lines in Rust documentation (those starting with a dash
    `#`).

## 0.1.2

> Mon Mar 4th 2019

  - Fix a trim bug that would cause the synchronized documentation to be completely aligned on the
    left-most side.

## 0.1.1

> Mon Feb 25th 2019

  - Fix the `cargo` subcommand incompatibility. You should now be able to run `cargo sync-readme`.

# 0.1

> Mon Feb 25th 2019

  - Initial revision.
