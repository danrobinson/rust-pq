// Pair compression is a callback that may return any digest for every row.
// Validate its preimage at the block encoder, then validate the exact routing
// of those encoded blocks through each four- or two-lane compressor call.
#![allow(dead_code, unused_unsafe)]
#[derive(Clone, Copy)]
struct Adrs {
    prefix: u32,
    index: u32,
}
impl Adrs {
    fn with_word3(self, index: u32) -> Self {
        Self { index, ..self }
    }
}
mod address {
    pub(super) use crate::Adrs;
}
static mut ENABLED: bool = false;
mod arm {
    pub fn available() -> bool {
        unsafe { super::ENABLED }
    }
}
struct Oracle<'a, const N: usize> {
    seed: &'a [u64; 8],
    prefix: u32,
    before: &'a [[u8; N]],
    live: *const [u8; N],
    sig: &'a [u8],
    indices: &'a [u32],
    answers: &'a [[u8; N]],
    a: usize,
    h: usize,
    packed: usize,
    compressed: usize,
}
static mut PROBE: *mut () = std::ptr::null_mut();
fn parent_block_512<const N: usize>(block: &mut [u8; 128], addr: Adrs, left: &[u8], right: &[u8]) {
    let p = unsafe { &mut *PROBE.cast::<Oracle<'_, N>>() };
    let t = p.packed;
    p.packed += 1;
    assert_eq!(addr.prefix, p.prefix);
    assert_eq!(addr.index, p.indices[t] / 2);
    let j = (t * (p.a + 1) + 1 + p.h) * N;
    let sibling = &p.sig[j..j + N];
    let row = unsafe { &*p.live.add(t) };
    assert_eq!(row, &p.before[t]);
    if p.indices[t] % 2 == 0 {
        assert_eq!((left.as_ptr(), left.len()), (row.as_ptr(), N));
        assert_eq!((right.as_ptr(), right.len()), (sibling.as_ptr(), N));
    } else {
        assert_eq!((left.as_ptr(), left.len()), (sibling.as_ptr(), N));
        assert_eq!((right.as_ptr(), right.len()), (row.as_ptr(), N));
    }
    // Encode an injective marker for this row at the paired-compression boundary.
    block[0] = t as u8;
}
fn grouped<const N: usize, const L: usize>(
    seed: &[u64; 8],
    bs: &[[u8; 128]; L],
    vals: &mut [[u8; N]],
) {
    let p = unsafe { &mut *PROBE.cast::<Oracle<'_, N>>() };
    assert_eq!(seed.as_ptr(), p.seed.as_ptr());
    assert_eq!(vals.len(), L);
    for i in 0..L {
        let t = p.compressed;
        p.compressed += 1;
        assert_eq!(bs[i][0] as usize, t);
        vals[i] = p.answers[t];
    }
}
fn compress_parents_4_active<const N: usize>(
    state: &[u64; 8],
    blocks: &[[u8; 128]; 4],
    vals: &mut [[u8; N]],
) {
    grouped(state, blocks, vals)
}
fn compress_parents<const N: usize>(
    state: &[u64; 8],
    blocks: &[[u8; 128]; 2],
    vals: &mut [[u8; N]],
) {
    grouped(state, blocks, vals)
}
// PRODUCTION
fn check<const N: usize, const TREES: usize, const A: usize, const BYTES: usize>() {
    let sig: [u8; BYTES] = kani::any();
    let seed = kani::any();
    let addr = Adrs {
        prefix: kani::any(),
        index: kani::any(),
    };
    let h: usize = kani::any();
    kani::assume(h < A);
    let before: [[u8; N]; TREES] = kani::any();
    let original: [u32; TREES] = kani::any();
    let answers: [[u8; N]; TREES] = kani::any();
    let mut nodes = before;
    let mut indices = original;
    let enabled: bool = kani::any();
    unsafe {
        ENABLED = enabled;
    }
    let mut p = Oracle {
        seed: &seed,
        prefix: addr.prefix,
        before: &before,
        live: nodes.as_ptr(),
        sig: &sig,
        indices: &original,
        answers: &answers,
        a: A,
        h,
        packed: 0,
        compressed: 0,
    };
    unsafe {
        PROBE = (&mut p as *mut Oracle<'_, N>).cast();
    }
    let done = path_parents_batch(&seed, addr, &mut nodes, &mut indices, &sig, A, h);
    assert_eq!(done, if enabled { TREES / 2 * 2 } else { 0 });
    assert_eq!(p.packed, done);
    assert_eq!(p.compressed, done);
    for i in 0..TREES {
        if i < done {
            assert_eq!(nodes[i], answers[i]);
            assert_eq!(indices[i], original[i] / 2);
        } else {
            assert_eq!(nodes[i], before[i]);
            assert_eq!(indices[i], original[i]);
        }
    }
}
