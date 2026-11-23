//! Assemble the ordered byte string consumed by the verified core.

use alloc::vec::Vec;

// Split the range in half so recursion depth is bounded by the bit width of
// usize, even for messages containing many empty parts. Keeping the range
// explicit also lets Aeneas translate the shared slice of shared slices.
fn append_range(parts: &[&[u8]], start: usize, end: usize, out: &mut Vec<u8>) {
    let count = end - start;
    if count == 1 {
        out.extend_from_slice(parts[start]);
    } else if count > 1 {
        let middle = start + count / 2;
        append_range(parts, start, middle, out);
        append_range(parts, middle, end, out);
    }
}

pub(crate) fn join(parts: &[&[u8]]) -> Vec<u8> {
    let mut message = Vec::new();
    append_range(parts, 0, parts.len(), &mut message);
    message
}
