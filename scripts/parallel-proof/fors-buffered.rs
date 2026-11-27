// FORS primitive effects are observed at the ABI before the oracle supplies any output.
extern "C" {
    fn proof_fors_leaves(out: *mut u8, sk: *const u8, seed: *const u8,
                         addr: *const u8, ids: *const u32, active: usize);
}

fn fors_leaves_fused<const N: usize>(sk: &[u8; N], seed: &[u8; N], addr: Adrs,
                                     ids: &[u32; WIDTH], active: usize) -> [[u8; N]; WIDTH] {
    let mut out = [[0; N]; WIDTH];
    unsafe {
        proof_fors_leaves(out.as_mut_ptr().cast(), sk.as_ptr(), seed.as_ptr(),
                          addr.full().as_ptr(), ids.as_ptr(), active);
    }
    out
}

macro_rules! export_tree {
    ($name:ident, $n:literal) => {
        #[no_mangle]
        pub extern "C" fn $name(out: &mut [u8; $n], sk: &[u8; $n], seed: &[u8; $n],
                                index: u32, height: u32, words: &[u32; 7]) {
            let addr = Adrs {
                layer: words[0], tree: (u64::from(words[1]) << 32) | u64::from(words[2]),
                typ: words[3], keypair: words[4], word2: words[5], word3: words[6],
            };
            *out = fors_subtree_horiz(sk, seed, addr, index, height);
        }
    };
}
export_tree!(tree16, 16);
export_tree!(tree24, 24);
export_tree!(tree32, 32);
