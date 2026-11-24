// Included in wots.rs in a checksum-verified copy of the published peer crate.
use super::{WotsParams, WotsSig};
use crate::address::{Address, WotsHash};
use crate::hashes::HashSuite;
use crate::{PkSeed, SkSeed};
use hybrid_array::{Array, ArraySize};
use zerocopy::IntoBytes;

type P = crate::PEER_TYPE;
const N: usize = PARAM_N;
const LEN: usize = 2 * N + 3;

// Keep all observer state in a single unique allocation. In Kani 0.68,
// a mutable byte initialized to zero can alias an unrelated constant byte
// in the generated GOTO model, including the BigEndian enum discriminant.
struct Transcript {
    _tag: [u8; 8],
    hash: *const (),
    secret: *const (),
    address: [u8; 32],
    row: usize,
    step: u32,
    start: u32,
    blocks: [[u8; N]; LEN],
    sig_bytes: *const u8,
    first: [u8; N],
    last: [u8; N],
    digits: [u32; LEN],
    mode: u8,
    prf_calls: usize,
    t_calls: usize,
}

static mut TRACE: Transcript = Transcript {
    _tag: *b"WOTSPROF",
    hash: core::ptr::null(),
    secret: core::ptr::null(),
    address: [0; 32],
    row: 0,
    step: 0,
    start: 0,
    blocks: [[0; N]; LEN],
    sig_bytes: core::ptr::null(),
    first: [0; N],
    last: [0; N],
    digits: [0; LEN],
    mode: 0,
    prf_calls: 0,
    t_calls: 0,
};

fn same_bytes<const W: usize>(actual: &[u8], expected: &[u8; W]) {
    assert!(actual.len() == W);
    for i in 0..W {
        assert!(actual[i] == expected[i]);
    }
}

fn address() -> WotsHash {
    let mut a = WotsHash::default();
    a.layer_adrs.set(kani::any());
    a.tree_adrs_high.set(kani::any());
    a.tree_adrs_low.set(kani::any());
    a.key_pair_adrs.set(kani::any());
    a.chain_adrs.set(kani::any());
    a.hash_adrs.set(kani::any());
    a
}

fn setup(hash: &P, a: &WotsHash) {
    unsafe {
        TRACE.hash = core::ptr::from_ref(hash).cast();
        TRACE.address = a.as_bytes().try_into().unwrap();
    }
}

pub(crate) trait Observe: HashSuite {
    fn checked_f(&self, addr: &impl Address, value: &Array<u8, Self::N>) -> Array<u8, Self::N> {
        unsafe {
            assert!(core::ptr::from_ref(self).cast::<()>() == TRACE.hash);
            let mut enc = TRACE.address;
            enc[28..32].copy_from_slice(&(TRACE.start + TRACE.step).to_be_bytes());
            same_bytes(addr.as_ref(), &enc);
            let prev = TRACE.last;
            same_bytes(value.as_slice(), &prev);
            let next: [u8; N] = kani::any();
            TRACE.last = next;
            TRACE.step += 1;
            next.as_slice().try_into().unwrap()
        }
    }

    fn checked_prf(&self, seed: &SkSeed<Self::N>, addr: &impl Address) -> Array<u8, Self::N> {
        unsafe {
            assert!(core::ptr::from_ref(self).cast::<()>() == TRACE.hash);
            assert!(core::ptr::from_ref(seed).cast::<()>() == TRACE.secret);
            assert!(TRACE.prf_calls == TRACE.row && TRACE.row < LEN);
            let mut enc = TRACE.address;
            enc[16..20].copy_from_slice(&5u32.to_be_bytes());
            enc[24..28].copy_from_slice(&(TRACE.row as u32).to_be_bytes());
            enc[28..32].fill(0);
            same_bytes(addr.as_ref(), &enc);
            let result: [u8; N] = kani::any();
            TRACE.first = result;
            TRACE.prf_calls += 1;
            result.as_slice().try_into().unwrap()
        }
    }

    fn checked_chain(
        &self,
        value: &Array<u8, Self::N>,
        start: u32,
        count: u32,
        addr: &WotsHash,
    ) -> Array<u8, Self::N> {
        unsafe {
            assert!(core::ptr::from_ref(self).cast::<()>() == TRACE.hash);
            assert!(TRACE.row < LEN);
            let mut enc = TRACE.address;
            enc[24..28].copy_from_slice(&(TRACE.row as u32).to_be_bytes());
            same_bytes(addr.as_bytes(), &enc);
            if TRACE.mode == 2 {
                assert_eq!(value.as_ptr(), TRACE.sig_bytes.add(TRACE.row * N));
            } else {
                let expected = TRACE.first;
                same_bytes(value.as_slice(), &expected);
            }
            let digit = TRACE.digits[TRACE.row];
            let expected = match TRACE.mode {
                0 => (0, 15),
                1 => (0, digit),
                _ => (digit, 15 - digit),
            };
            assert_eq!((start, count), expected);
            let result = TRACE.blocks[TRACE.row];
            TRACE.row += 1;
            result.as_slice().try_into().unwrap()
        }
    }

    fn checked_t<L: ArraySize>(
        &self,
        addr: &impl Address,
        values: &Array<Array<u8, Self::N>, L>,
    ) -> Array<u8, Self::N> {
        unsafe {
            assert!(core::ptr::from_ref(self).cast::<()>() == TRACE.hash);
            assert!(TRACE.row == LEN && values.len() == LEN && TRACE.t_calls == 0);
            let mut enc = TRACE.address;
            enc[16..20].copy_from_slice(&1u32.to_be_bytes());
            enc[24..32].fill(0);
            same_bytes(addr.as_ref(), &enc);
            for row in 0..LEN {
                let expected = TRACE.blocks[row];
                same_bytes(values[row].as_slice(), &expected);
            }
            let result: [u8; N] = kani::any();
            TRACE.last = result;
            TRACE.t_calls += 1;
            result.as_slice().try_into().unwrap()
        }
    }
}

impl<S: HashSuite> Observe for S {}

#[kani::proof]
#[kani::unwind(CHAIN_UNWIND)]
fn check_chain() {
    let p = P::new_from_pk_seed(&PkSeed(Array(kani::any::<[u8; N]>())));
    let a = address();
    setup(&p, &a);
    let x: [u8; N] = kani::any();
    let start: u32 = kani::any();
    let count: u32 = kani::any();
    kani::assume(start <= 15 && count <= 15 - start);
    unsafe {
        TRACE.start = start;
        TRACE.last = x;
    }
    let result = p.wots_chain(&Array(x), start, count, &a);
    unsafe {
        let last = TRACE.last;
        assert!(TRACE.step == count);
        same_bytes(result.as_slice(), &last);
    }
}

fn inputs(p: &P, sk: &SkSeed<<P as HashSuite>::N>, a: &WotsHash, mode: u8) {
    setup(p, a);
    unsafe {
        // Independent symbolic blocks supply the complete sequence of possible
        // chain results. Each caller must preserve every byte in row order.
        TRACE.blocks = kani::any();
        TRACE.mode = mode;
        TRACE.secret = core::ptr::from_ref(sk).cast();
    }
}

#[kani::proof]
#[kani::unwind(150)]
#[kani::stub(crate::wots::WotsParams::wots_chain, Observe::checked_chain)]
fn check_keygen() {
    let p = P::new_from_pk_seed(&PkSeed(Array(kani::any::<[u8; N]>())));
    let a = address();
    let sk = SkSeed(Array(kani::any::<[u8; N]>()));
    inputs(&p, &sk, &a, 0);
    let root = p.wots_pk_gen(&sk, &a);
    unsafe {
        let expected = TRACE.last;
        assert!(TRACE.row == LEN && TRACE.prf_calls == LEN && TRACE.t_calls == 1);
        same_bytes(root.as_slice(), &expected);
    }
}

#[kani::proof]
#[kani::unwind(150)]
#[kani::stub(crate::wots::WotsParams::wots_chain, Observe::checked_chain)]
fn check_sign() {
    let p = P::new_from_pk_seed(&PkSeed(Array(kani::any::<[u8; N]>())));
    let a = address();
    let sk = SkSeed(Array(kani::any::<[u8; N]>()));
    inputs(&p, &sk, &a, 1);
    let message: [u8; N] = kani::any();
    unsafe {
        TRACE.digits = slhdsa::wots::wots_digits(&message)
            .as_slice()
            .try_into()
            .unwrap();
    }
    let sig = p.wots_sign(&Array(message), &sk, &a);
    unsafe {
        assert!(TRACE.row == LEN && TRACE.prf_calls == LEN);
        for i in 0..LEN {
            let expected = TRACE.blocks[i];
            same_bytes(sig.0[i].as_slice(), &expected);
        }
    }
}

#[kani::proof]
#[kani::unwind(150)]
#[kani::stub(crate::wots::WotsParams::wots_chain, Observe::checked_chain)]
fn check_recover() {
    let p = P::new_from_pk_seed(&PkSeed(Array(kani::any::<[u8; N]>())));
    let a = address();
    inputs(&p, &SkSeed(Array::default()), &a, 2);
    let message: [u8; N] = kani::any();
    let bytes = kani::any::<[u8; N * LEN]>();
    let sig = unsafe { core::mem::transmute::<_, WotsSig<P>>(bytes) };
    unsafe {
        TRACE.digits = slhdsa::wots::wots_digits(&message)
            .as_slice()
            .try_into()
            .unwrap();
        TRACE.sig_bytes = sig.0[0].as_ptr();
    }
    let root = p.wots_pk_from_sig(&sig, &Array(message), &a);
    unsafe {
        let expected = TRACE.last;
        assert!(TRACE.row == LEN && TRACE.t_calls == 1);
        same_bytes(root.as_slice(), &expected);
    }
}

#[kani::proof]
#[kani::unwind(150)]
fn check_encoding() {
    let bytes = kani::any::<[u8; N * LEN]>();
    let row: usize = kani::any();
    let column: usize = kani::any();
    kani::assume(row < LEN && column < N);
    let sig = WotsSig::<P>::try_from(bytes.as_slice()).unwrap();
    assert!(sig.0[row][column] == bytes[row * N + column]);
    let mut serialized = [0u8; N * LEN];
    sig.write_to(&mut serialized);
    assert!(serialized[row * N + column] == bytes[row * N + column]);
}
