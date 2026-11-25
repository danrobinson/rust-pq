#![allow(unused_unsafe)]
// Input offsets and the known-zero byte have disjoint codes.
type V = [u8; 16];
fn vrev32q_u8(x: V) -> V {
    std::array::from_fn(|i| x[i ^ 3])
}
fn vreinterpretq_u32_u8(x: V) -> V {
    x
}
fn vld1q_u8(src: &[u8]) -> V {
    src[..16].try_into().unwrap()
}
fn vld1_u8(src: &[u8]) -> [u8; 8] {
    src[..8].try_into().unwrap()
}
fn vcombine_u8(a: [u8; 8], b: [u8; 8]) -> V {
    std::array::from_fn(|i| [a, b][i / 8][i % 8])
}
fn vdup_n_u8(x: u8) -> [u8; 8] {
    assert_eq!(x, 0);
    [255; 8]
}
fn vdupq_n_u32(x: u32) -> V {
    assert_eq!(x, 0);
    [255; 16]
}
// PRODUCTION
fn run<const N: usize>() {
    let src: [u8; N] = std::array::from_fn(|i| i as u8);
    let (a, b) = unsafe { load_n::<N>(&src) };
    for v in [a, b] {
        for j in 0..16 {
            print!("{} ", v[j ^ 3]);
        }
    }
    println!();
}
fn main() {
    run::<16>();
    run::<24>();
    run::<32>();
}
