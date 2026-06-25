# cargo-dequalify

A Rust refactoring tool that rewrites fully-qualified function calls into imported short names.

Before:

```rust
fn main() {
    tokio::task::spawn(async {});
    std::fs::read_to_string("foo");
}
```

After:

```rust
use std::fs::read_to_string;
use tokio::task::spawn;

fn main() {
    spawn(async {});
    read_to_string("foo");
}
```

## Installation

```console
$ cargo install --git https://github.com/0x6b/cargo-dequalify
```

## Usage

```console
$ cargo dequalify --help
Rewrite fully-qualified Rust call paths into imported short names

Usage: cargo-dequalify [OPTIONS] [PATH]

Arguments:
  [PATH]  Optional path to a package or workspace root. Defaults to current dir [default: .]

Options:
  -w, --write                        Actually modify files (default: dry-run mode)
      --allow-dirty                  Allow running --write on a dirty git working directory
      --ignore-roots <IGNORE_ROOTS>  Comma-separated list of top-level roots to ignore (e.g. "std,core,alloc")
  -f, --fmt [<TOOLCHAIN>]            Run cargo fmt after writing changes. Optionally specify a toolchain (e.g.,
                                     --fmt=nightly)
  -h, --help                         Print help
  -V, --version                      Print version
```

Rust files marked with `linguist-generated` or `linguist-generated=true` in the workspace root `.gitattributes` are skipped. When `--fmt` is used, those files are also added to rustfmt's temporary `ignore` list. That formatting ignore support is a nightly rustfmt feature, so use `--fmt=nightly` if generated files should also be protected during formatting.

## Conflict Handling

When the short name would conflict with an existing import or local definition, the tool imports the parent module instead:

```rust
fn spawn() {}

fn main() {
    tokio::task::spawn(async {});
}
```

Becomes:

```rust
use tokio::task;

fn spawn() {}

fn main() {
    task::spawn(async {});
}
```

If the parent module name also conflicts, it goes up another level. If no valid import level exists (would result in same-as-original), the path is left unchanged.

## Limitations

- Skips type-associated functions when the type is the leading segment (e.g., `Vec::new()`, `String::from()`). For `module::Type::method()`, the module path is shortened instead (imports `module::Type`, keeps `Type::method()`).
- Skips `Self::` paths
- Skips primitive type methods (e.g., `str::len()`)
- Only descends into the arguments of formatting macros (`println!`, `format!`, `write!`, `panic!`, log macros, etc.). Qualified paths inside other macro invocations (`vec![...]`, `tokio::select!{...}`, `assert!`, `matches!`, …) are left unchanged.
- Skips paths whose non-last segments carry turbofish generics (e.g., `parser::<YAML>::parse`); these would lose their generics if rewritten.

## License

MIT. See [LICENSE](LICENSE) for detail.
