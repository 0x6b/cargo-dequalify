pub(super) struct Lines<'a> {
    starts: Vec<usize>,
    src: &'a str,
}

impl<'a> Lines<'a> {
    pub(super) fn new(src: &'a str) -> Self {
        let starts = std::iter::once(0)
            .chain(
                src.char_indices()
                    .filter_map(|(i, c)| (c == '\n').then_some(i + 1)),
            )
            .collect();
        Self { starts, src }
    }

    /// Convert a 1-indexed line and 0-indexed UTF-8 *character* column
    /// (as produced by `proc_macro2::LineColumn`) to a byte offset.
    pub(super) fn to_byte(&self, line: usize, col: usize) -> Option<usize> {
        if line == 0 || line > self.starts.len() {
            return None;
        }
        let line_start = self.starts[line - 1];
        let line_end = if line < self.starts.len() {
            self.starts[line] - 1 // strip the trailing '\n'
        } else {
            self.src.len()
        };
        let line_str = self.src.get(line_start..line_end)?;
        line_str
            .char_indices()
            .nth(col)
            .map(|(b, _)| line_start + b)
            // Past the last character on the line; clamp to line end.
            .or_else(|| (col == line_str.chars().count()).then_some(line_start + line_str.len()))
    }

    pub(super) fn end(&self, line: usize) -> usize {
        if line == 0 || line > self.starts.len() {
            return 0;
        }
        if line < self.starts.len() { self.starts[line] - 1 } else { self.src.len() }
    }
}
