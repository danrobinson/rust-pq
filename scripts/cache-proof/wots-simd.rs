// Kani proof context for the production packed-chain loop and one signing/recovery batch.
#![allow(dead_code, unused_imports)]
extern crate alloc;
use std::convert::TryInto;

#[path = "ADDRESS_FILE"]
mod address;
use address::{Adrs, WOTS_HASH, WOTS_PK, WOTS_PRF};

const N: usize = NODE_BYTES;
const WIDTH: usize = LANE_COUNT;
const LEN: usize = 2 * N + CHECKSUM_DIGITS;
const W: u32 = W_PARAMETER;
const _: () = assert!(W == 16 && CHECKSUM_DIGITS == 3);
type States = [[u64; WIDTH]; 25];

fn arbitrary_adrs() -> Adrs {
    Adrs {
        layer: kani::any(),
        tree: kani::any(),
        typ: kani::any(),
        keypair: kani::any(),
        word2: kani::any(),
        word3: kani::any(),
    }
}

mod packed {
    use super::*;
    PACKED_FUNCTIONS
    pub(super) fn init(
        seed: &[u8; N],
        addr: Adrs,
        ids: [usize; WIDTH],
        values: &[[u8; N]; WIDTH],
    ) -> States {
        PACKED_INIT
        input
    }
    pub(super) fn step(
        mut input: States,
        mut index: [u32; WIDTH],
        end: [u32; WIDTH],
    ) -> (States, [u32; WIDTH]) {
        let offset = PACKED_OFFSET;
        PACKED_BODY
        (input, index)
    }
    pub(super) fn finish(input: States) -> [[u8; N]; WIDTH] {
        let offset = PACKED_OFFSET;
        PACKED_FINISH
    }
}

static mut CALLS: usize = 0;
static mut PRE: States = [[0; WIDTH]; 25];
static mut POST: States = [[0; WIDTH]; 25];

mod parallel {
    use super::*;
    pub fn permute(state: &mut States) {
        unsafe {
            CALLS += 1;
            PRE = *state;
            *state = POST;
        }
    }
}

// A single arbitrary iteration suffices for induction. All lanes, words, step counts and
// permutation outputs are symbolic. The Lean invariant advances exactly the active lanes.
#[kani::proof]
#[kani::unwind(34)]
fn packed_chains() {
    let input: States = kani::any();
    let index: [u32; WIDTH] = kani::any();
    let end: [u32; WIDTH] = kani::any();
    for lane in 0..WIDTH {
        kani::assume(index[lane] <= end[lane] && end[lane] < W);
    }
    let post: States = kani::any();
    unsafe {
        POST = post;
    }
    let (next, after) = packed::step(input, index, end);
    assert_eq!(unsafe { CALLS }, 1);
    let offset = N / 8 + 4;
    for lane in 0..WIDTH {
        let active = index[lane] < end[lane];
        assert_eq!(after[lane], index[lane] + u32::from(active));
        for word in 0..25 {
            let increment = if word == offset - 1 {
                let [a, b, c, d] = index[lane].to_be_bytes();
                u64::from_le_bytes([0, 0, 0, 0, a, b, c, d])
            } else {
                0
            };
            assert_eq!(unsafe { PRE[word][lane] }, input[word][lane] | increment);
            if active && (offset..offset + N / 8).contains(&word) {
                assert_eq!(next[word][lane], post[word - offset][lane]);
            } else {
                assert_eq!(next[word][lane], input[word][lane]);
            }
        }
    }
}

#[kani::proof]
#[kani::unwind(34)]
fn packed_boundary() {
    let seed = kani::any();
    let addr = arbitrary_adrs();
    let ids: [usize; WIDTH] = kani::any();
    for lane in 0..WIDTH {
        kani::assume(ids[lane] < LEN);
    }
    let values: [[u8; N]; WIDTH] = kani::any();
    let input = packed::init(&seed, addr, ids, &values);
    let state: States = kani::any();
    let result = packed::finish(state);
    let offset = N / 8 + 4;
    for lane in 0..WIDTH {
        let mut msg = [0u8; 200];
        msg[..N].copy_from_slice(&seed);
        msg[N..N + 32].copy_from_slice(&addr.with_word2(ids[lane] as u32).with_word3(0).full());
        msg[N + 32..2 * N + 32].copy_from_slice(&values[lane]);
        msg[2 * N + 32] = 0x1f;
        msg[135] = 0x80;
        for word in 0..25 {
            let expected = u64::from_le_bytes(msg[8 * word..8 * word + 8].try_into().unwrap());
            assert_eq!(input[word][lane], expected);
        }
        for byte in 0..N {
            assert_eq!(
                result[lane][byte],
                state[offset + byte / 8][lane].to_le_bytes()[byte % 8]
            );
        }
    }
}

struct BatchWatch {
    mode: bool,
    active: usize,
    ids: [usize; WIDTH],
    seed: [u8; N],
    sk: [u8; N],
    addr: Adrs,
    digits: [u32; WIDTH],
    sig: [[u8; N]; WIDTH],
    secrets: [[u8; N]; WIDTH],
    result: [[u8; N]; WIDTH],
}
static mut BATCH: Option<BatchWatch> = None;
fn same_addr(a: Adrs, b: Adrs) {
    assert_eq!(a.layer, b.layer);
    assert_eq!(a.tree, b.tree);
    assert_eq!(a.typ, b.typ);
    assert_eq!(a.keypair, b.keypair);
    assert_eq!(a.word2, b.word2);
    assert_eq!(a.word3, b.word3);
}
// Observe every table lookup. Independent per-call return values overapproximate any
// real digit or signature table, including repeated reads in the last partial batch.
struct Digits {
    count: core::cell::Cell<usize>,
    words: [u32; WIDTH],
}
struct Signature {
    count: core::cell::Cell<usize>,
    rows: [[u8; N]; WIDTH],
}
fn lookup(count: &core::cell::Cell<usize>, id: usize) -> usize {
    let lane = count.get();
    assert!(lane < WIDTH);
    unsafe {
        let b = (*core::ptr::addr_of!(BATCH)).as_ref().unwrap();
        assert_eq!(id, b.ids[lane.min(b.active - 1)]);
    }
    count.set(lane + 1);
    lane
}
impl core::ops::Index<usize> for Digits {
    type Output = u32;
    fn index(&self, id: usize) -> &u32 {
        &self.words[lookup(&self.count, id)]
    }
}
fn block(sig: &Signature, id: usize) -> [u8; N] {
    sig.rows[lookup(&sig.count, id)]
}

mod batch {
    use super::*;
    // Use the production secret-address constructor, instrumenting its short hash call.
    SECRET_FUNCTION
    fn short<const K: usize>(
        seed: &[u8; K],
        addresses: &[Adrs; WIDTH],
        values: &[[u8; K]; WIDTH],
    ) -> [[u8; K]; WIDTH] {
        unsafe {
            let b = (*core::ptr::addr_of!(BATCH)).as_ref().unwrap();
            let mut out = [[0; K]; WIDTH];
            for i in 0..WIDTH {
                assert_eq!(seed[..], b.seed[..]);
                assert_eq!(values[i][..], b.sk[..]);
                let id = b.ids[i.min(b.active - 1)];
                same_addr(
                    addresses[i],
                    b.addr
                        .with_type(WOTS_PRF)
                        .with_keypair(b.addr.keypair)
                        .with_word2(id as u32),
                );
                out[i].copy_from_slice(&b.secrets[i]);
            }
            out
        }
    }
    fn chains(
        seed: &[u8; N],
        a: Adrs,
        ids: [usize; WIDTH],
        v: &[[u8; N]; WIDTH],
        start: [u32; WIDTH],
        end: [u32; WIDTH],
    ) -> [[u8; N]; WIDTH] {
        unsafe {
            let b = (*core::ptr::addr_of!(BATCH)).as_ref().unwrap();
            same_addr(a, b.addr);
            assert_eq!(*seed, b.seed);
            for i in 0..WIDTH {
                let id = b.ids[i.min(b.active - 1)];
                assert_eq!(ids[i], id);
                if b.mode {
                    assert_eq!(v[i], b.secrets[i]);
                    assert_eq!(start[i], 0);
                    assert_eq!(end[i], b.digits[i]);
                } else {
                    assert_eq!(v[i][..], b.sig[i][..]);
                    assert_eq!(start[i], b.digits[i]);
                    assert_eq!(end[i], 15);
                }
            }
            b.result
        }
    }
    pub fn sign(
        batch: &[usize],
        sk: &[u8; N],
        seed: &[u8; N],
        addr: Adrs,
        digits: &Digits,
    ) -> [[u8; N]; WIDTH] {
        SIGN_BATCH
        values
    }
    pub fn recover(
        batch: &[usize],
        sig: &Signature,
        seed: &[u8; N],
        addr: Adrs,
        digits: &Digits,
    ) -> [[u8; N]; WIDTH] {
        RECOVER_BATCH
        values
    }
}
#[kani::proof]
#[kani::unwind(34)]
fn gather_batch() {
    let active: usize = kani::any();
    kani::assume(active > 0 && active <= WIDTH);
    let ids: [usize; WIDTH] = kani::any();
    for i in 0..active {
        kani::assume(ids[i] < LEN);
    }
    let sk = kani::any();
    let seed = kani::any();
    let addr = arbitrary_adrs();
    let words = kani::any();
    let rows = kani::any();
    let result: [[u8; N]; WIDTH] = kani::any();
    let mode: bool = kani::any();
    let secrets = kani::any();
    unsafe {
        BATCH = Some(BatchWatch {
            mode,
            active,
            ids,
            seed,
            sk,
            addr,
            digits: words,
            sig: rows,
            secrets,
            result,
        });
    }
    let digits = Digits {
        count: core::cell::Cell::new(0),
        words,
    };
    let sig = Signature {
        count: core::cell::Cell::new(0),
        rows,
    };
    let rows = if mode {
        batch::sign(&ids[..active], &sk, &seed, addr, &digits)
    } else {
        batch::recover(&ids[..active], &sig, &seed, addr, &digits)
    };
    assert_eq!(digits.count.get(), WIDTH);
    assert_eq!(sig.count.get(), if mode { 0 } else { WIDTH });
    for lane in 0..WIDTH {
        assert_eq!(rows[lane], result[lane]);
    }
}
