pub(super) const PRIMITIVES: &[&str] = &[
    "bool", "char", "str", "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64",
    "u128", "usize", "f32", "f64",
];

/// Names from the 2021/2024 edition prelude that can appear in a
/// type-position path. Used to detect when a top-level identifier already
/// refers to a prelude item, so we avoid generating an import that would
/// shadow it.
pub(super) const PRELUDE: &[&str] = &[
    // types
    "Box",
    "Option",
    "Result",
    "String",
    "Vec",
    // variant constructors that may appear as paths
    "Some",
    "None",
    "Ok",
    "Err",
    // traits in the 2021 prelude
    "Clone",
    "Copy",
    "Default",
    "Drop",
    "Eq",
    "Fn",
    "FnMut",
    "FnOnce",
    "From",
    "Hash",
    "Into",
    "IntoIterator",
    "Iterator",
    "Ord",
    "PartialEq",
    "PartialOrd",
    "Send",
    "Sized",
    "Sync",
    "ToOwned",
    "ToString",
    "TryFrom",
    "TryInto",
    "Unpin",
    "AsMut",
    "AsRef",
    "DoubleEndedIterator",
    "Extend",
    "ExactSizeIterator",
    // additions in the 2024 edition prelude
    "Future",
    "IntoFuture",
];

/// Maximum chain length followed when resolving a `use` alias to its
/// terminal target. Aliases resolve in O(chain) time and real codebases
/// rarely exceed two or three hops; this bound only fires on cycles.
pub(super) const MAX_RESOLVE_DEPTH: usize = 20;

/// Spaces per indentation level when reconstructing a module's indent
/// string from its scope depth. Used as a fallback when the module body
/// is empty so we still emit visually plausible imports.
pub(super) const DEFAULT_INDENT_WIDTH: usize = 4;

pub(super) const FMT_MACROS: &[&str] = &[
    "println",
    "print",
    "eprintln",
    "eprint",
    "format",
    "format_args",
    "write",
    "writeln",
    "panic",
    "unreachable",
    "todo",
    "unimplemented",
    "trace",
    "debug",
    "info",
    "warn",
    "error",
];
