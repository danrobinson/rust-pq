// Each byte of each register is an independent symbol in little-endian memory order.
type V = [u8; 16];
fn vreinterpretq_u8_u32(x: V) -> V {
    x
}
fn vrev32q_u8(x: V) -> V {
    std::array::from_fn(|i| x[(i / 4) * 4 + 3 - i % 4])
}
fn vget_low_u8(x: V) -> [u8; 8] {
    x[..8].try_into().unwrap()
}
fn vst1q_u8(dst: &mut [u8], x: V) {
    dst[..16].copy_from_slice(&x);
}
fn vst1_u8(dst: &mut [u8], x: [u8; 8]) {
    dst[..8].copy_from_slice(&x);
}
// PRODUCTION
fn run<const N: usize>() {
    let x = std::array::from_fn(|i| i as u8);
    let xb = std::array::from_fn(|i| (i + 16) as u8);
    let mut dst = [255; N];
    unsafe { store_n::<N>(&mut dst, x, xb) };
    println!("{}", dst.map(|b| b.to_string()).join(","));
}
fn main() {
    run::<16>();
    run::<24>();
    run::<32>();
}
