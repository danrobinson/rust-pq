// Tags identify original children. A stored parent has a distinct tag, so a
// later read of an overwritten child is observable.
type V = [u32; 4];
type uint16x8_t = V;
type Head = u32;
const K: [u32; 64] = [0; 64];
#[derive(Clone, Copy)]
struct Adrs { word2: u32 }

mod arm {
    pub fn load_be(input: &[u8; 16], offset: usize) -> super::V {
        assert_eq!(offset, 0);
        [u32::from_be_bytes(input[..4].try_into().unwrap()), 0, 0, 0]
    }
}
fn vdupq_n_u32(v: u32) -> V { [v; 4] }
fn make_hdr(height: u32, index: u32) -> V { [height, index, 0, 0] }
fn make_head(state: &[u32; 8], address: Adrs) -> u32 {
    assert_eq!(state, &[17; 8]);
    address.word2
}
fn load_shared_head<const LANES: usize>(head: &u32) -> (u32, u32, u32) {
    (*head, 19, 21)
}
fn pack_short<const N: usize>(header: V, left: V, right: V) -> (V, V, V) {
    assert_eq!(N, 32);
    (header, left, right)
}
fn finish_from_r4<const LANES: usize, const BOTH: bool>(
    state: &[u32; 8], a: u32, e: u32, height: u32, header: [V; LANES],
    left: [V; LANES], right: [V; LANES], _constants: *const u32,
) -> ([V; LANES], [V; LANES]) {
    assert_eq!((a, e, *state), (19, 21, [17; 8]));
    let out = std::array::from_fn(|i| {
        assert_eq!(height, header[i][0]);
        [1000 + left[i][0], right[i][0], header[i][1], height + if BOTH { 10 } else { 0 }]
    });
    (out, [[99; 4]; LANES])
}
fn vreinterpretq_u8_u32(v: V) -> V { v }
fn vrev32q_u8(v: V) -> V { v }
unsafe fn vst1q_u8(dst: *mut u8, v: V) {
    for (j, word) in v.iter().enumerate() {
        unsafe { std::ptr::copy_nonoverlapping(word.to_be_bytes().as_ptr(), dst.add(j * 4), 4); }
    }
}
mod native {
    use super::*;
    // PROJECT_FUNCTIONS
}
fn main() {
    for n in 1..=8 {
        for first in 0..512 {
            for height in 1..=4 {
                let start: [[u8;16];16] = std::array::from_fn(|i| {
                    let mut tag = [0u8;16];
                    tag[..4].copy_from_slice(&(i as u32).to_be_bytes());
                    tag
                });
                let mut vals = start;
                native::parents_16_active(&[17;8], Adrs {word2:height}, first, &mut vals, n);
                for (j, bytes) in vals.iter().enumerate() {
                    if j >= n {
                        assert_eq!(bytes, &start[j]);
                        continue;
                    }
                    let record: [u32;4] = std::array::from_fn(|k| u32::from_be_bytes(
                        bytes[k*4..k*4+4].try_into().unwrap()));
                    assert_eq!(record, [1000+2*j as u32, 2*j as u32+1, first+j as u32,
                        height + if j < n/4*4 {10} else {0}]);
                }
            }
        }
    }
}
