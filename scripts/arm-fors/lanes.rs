// The production loops run on abstract SIMD registers. The compression cut
// validates every argument and returns an independently quantified digest per row.
#![allow(non_camel_case_types, unused_unsafe)]
static K: [u32; 64] = [0; 64];
type V = [u8; 16];
type uint16x8_t = (u32, u32);
type Head = (u32, u32);
#[derive(Clone, Copy)]
struct Adrs(u32, u32);
impl Adrs {
    fn with_word2(self, w: u32) -> Self {
        Adrs(self.0, w)
    }
}
fn make_head(_: &[u32; 8], a: Adrs) -> Head {
    (a.0, a.1)
}
fn make_hdr(a: u32, b: u32) -> uint16x8_t {
    (a, b)
}
fn vdupq_n_u32(x: u32) -> V {
    assert_eq!(x, 0);
    [0; 16]
}
fn load_n<const N: usize>(s: &[u8]) -> (V, V) {
    let mut hi = [0; 16];
    hi[..N - 16].copy_from_slice(&s[16..N]);
    (std::convert::TryInto::try_into(&s[..16]).unwrap(), hi)
}
fn store_n<const N: usize>(s: &mut [u8], x: V, hi: V) {
    s[..16].copy_from_slice(&x);
    s[16..N].copy_from_slice(&hi[..N - 16]);
}
mod arm {
    pub fn load_be(s: &[u8], i: usize) -> super::V {
        std::convert::TryInto::try_into(&s[i..i + 16]).unwrap()
    }
}
// A register here contains its big-endian bytes; the complete NEON store sequence
// is one cut, and its three actual operations are source-checked by the generator.
unsafe fn store_be(dst: *mut u8, bytes: V) {
    std::ptr::copy_nonoverlapping(bytes.as_ptr(), dst, 16);
}
fn tag(a: u32, b: u32, c: u32) -> V {
    let mut r = [0; 16];
    r[..4].copy_from_slice(&a.to_be_bytes());
    r[4..8].copy_from_slice(&b.to_be_bytes());
    r[8..12].copy_from_slice(&c.to_be_bytes());
    r
}
fn load_shared_head<const L: usize>(h: &Head) -> ([V; L], [V; L], [V; L]) {
    (
        [tag(h.0, h.1, 0); L],
        [tag(h.0, h.1, 1); L],
        [tag(h.0, h.1, 2); L],
    )
}
fn pack_short<const N: usize>((h, i): uint16x8_t, x: V, y: V) -> (V, V, V) {
    (tag(h, i, N as u32), x, y)
}

struct Oracle<'a> {
    state: &'a [u32; 8],
    address_prefix: u32,
    schedule: &'a [u32],
    sig: &'a [u8],
    before: &'a [[u8; 16]],
    siblings: &'a [[u8; 16]],
    reads: usize,
    answers: &'a [[u8; 32]],
    parent: bool,
    n: usize,
    a: usize,
    level: usize,
    count: usize,
}
static mut PROBE: *mut Oracle<'static> = std::ptr::null_mut();

// Source-matched signature loads all read a distinct authentication node. Check
// the exact slice address and substitute an arbitrary 16-byte result. This
// avoids a symbolic lookup into a multi-kilobyte array while allowing every
// possible combination of signature bytes at the checked locations.
fn load_sibling(s: &[u8], start: usize) -> V {
    let p = unsafe { &mut *PROBE };
    let t = p.reads;
    p.reads += 1;
    let addr = (t * (p.a + 1) + 1 + p.level) * 16;
    assert_eq!(
        s[start..start + 16].as_ptr(),
        p.sig[addr..addr + 16].as_ptr()
    );
    p.siblings[t]
}

fn finish_from_r4<const L: usize, const HIGH: bool>(
    st: &[u32; 8],
    a1: [V; L],
    e1: [V; L],
    m0: [V; L],
    m1: [V; L],
    m2: [V; L],
    m3: [V; L],
    kp: *const u32,
) -> ([V; L], [V; L]) {
    let p = unsafe { &mut *PROBE };
    assert_eq!(kp, K.as_ptr());
    assert_eq!(st, p.state);
    let mut lo = [[0; 16]; L];
    let mut hi = [[0; 16]; L];
    for j in 0..L {
        let t = p.count;
        p.count += 1;
        let w = if p.parent { (p.level + 1) as u32 } else { 0 };
        assert_eq!(m0[j], tag(p.address_prefix, w, 0));
        assert_eq!(a1[j], tag(p.address_prefix, w, 1));
        assert_eq!(e1[j], tag(p.address_prefix, w, 2));
        let pos = p.schedule[t];
        if p.parent {
            assert_eq!(m1[j], tag(w, pos / 2, 32));
            let sibling = &p.siblings[t];
            let node = &p.before[t];
            if pos % 2 == 0 {
                assert_eq!(m2[j], *node);
                assert_eq!(m3[j], *sibling);
            } else {
                assert_eq!(m2[j], *sibling);
                assert_eq!(m3[j], *node);
            }
        } else {
            assert_eq!(m1[j], tag(0, pos, p.n as u32));
            let offset = t * (p.a + 1) * p.n;
            assert_eq!(m2[j], p.sig[offset..offset + 16]);
            assert_eq!(&m3[j][..p.n - 16], &p.sig[offset + 16..offset + p.n]);
            assert_eq!(HIGH, p.n > 16);
        }
        lo[j].copy_from_slice(&p.answers[t][..16]);
        if HIGH {
            hi[j].copy_from_slice(&p.answers[t][16..]);
        }
    }
    (lo, hi)
}

mod native {
    use super::*;
    // PRODUCTION
}

fn check<
    const N: usize,
    const TREES: usize,
    const A: usize,
    const BYTES: usize,
    const PARENT: bool,
>() {
    let signature: [u8; BYTES] = kani::any();
    let absolute: [u32; TREES] = kani::any();
    let answers: [[u8; 32]; TREES] = kani::any();
    let state = kani::any();
    let address = Adrs(kani::any(), kani::any());
    let before: [[u8; 16]; TREES] = kani::any();
    let level: usize = kani::any();
    kani::assume(level < A);
    let siblings: [[u8; 16]; TREES] = kani::any();
    let mut probe = Oracle {
        state: &state,
        address_prefix: address.0,
        schedule: &absolute,
        sig: &signature,
        before: &before,
        siblings: &siblings,
        reads: 0,
        answers: &answers,
        parent: PARENT,
        n: N,
        a: A,
        level,
        count: 0,
    };
    unsafe {
        PROBE = (&mut probe as *mut Oracle<'_>).cast();
    }
    if PARENT {
        let mut vals = before;
        let mut indices = absolute;
        native::fors_path_level_16_active(
            &state,
            address,
            &signature,
            &mut indices,
            &mut vals,
            A,
            level,
        );
        assert_eq!(probe.reads, TREES);
        for i in 0..TREES {
            assert_eq!(indices[i], absolute[i] / 2);
            assert_eq!(vals[i], answers[i][..16]);
        }
    } else {
        let mut vals = [[0; N]; TREES];
        native::fors_verify_leaves_active(&state, address, &signature, &absolute, &mut vals, A);
        for i in 0..TREES {
            assert_eq!(vals[i], answers[i][..N]);
        }
    }
    assert_eq!(probe.count, TREES);
}
