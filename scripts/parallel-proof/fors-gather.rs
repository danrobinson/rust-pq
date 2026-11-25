#![no_std]
#[path="ADDRESS_PATH"] mod address;
use address::Adrs;

fn address(w: [u32; 7]) -> Adrs {
    Adrs { layer:w[0], tree:((w[1] as u64)<<32) | w[2] as u64,
           typ:w[3], keypair:w[4], word2:w[5], word3:w[6] }
}

fn record<const N: usize>(out: &mut [u8], addresses: [Adrs;8], left: [[u8;N];8], right: [[u8;N];8]) {
    for i in 0..8 {
        let offset = i*(32+2*N);
        out[offset..offset+32].copy_from_slice(&addresses[i].full());
        out[offset+32..offset+32+N].copy_from_slice(&left[i]);
        out[offset+32+N..offset+32+2*N].copy_from_slice(&right[i]);
    }
}

macro_rules! capture {
    ($name:ident, $n:literal) => {
        #[no_mangle] pub extern "C" fn $name(out:&mut [u8; 8*(32+2*$n)],
            buf:&[[[u8;$n];16];16], scratch:&[[[u8;$n];8];2], tags:&[[u32;7];9],
            h:usize, count:usize, base:u32, lvl:u32) {
            let mut left = scratch[0];
            let mut right = scratch[1];
            let mut addrs = core::array::from_fn(|i| address(tags[i]));
            let tree_adrs = address(tags[8]);
            GATHER_BODY
            record(out,addrs,left,right);
        }
    }
}
