// Check the upstream XMSS path using arbitrary WOTS and binary-hash outputs.
use super::{XmssParams, XmssSig};
use crate::{
    PkSeed,
    address::{Address, WotsHash},
    hashes::HashSuite,
    wots::{WotsParams, WotsSig},
};
use crate::{SkPrf, SkSeed};
use hybrid_array::{Array, ArraySize};
use zerocopy::IntoBytes;

type Actual = crate::PEER_TYPE;
#[derive(Clone, Debug)]
struct P([u8; N]);
impl XmssParams for P {
    type HPrime = <Actual as XmssParams>::HPrime;
    fn xmss_node(
        &self,
        seed: &SkSeed<Self::N>,
        node: u32,
        height: u32,
        addr: &WotsHash,
    ) -> Array<u8, Self::N> {
        unsafe {
            let j = OBS.layer;
            if let Some(expected_height) = OBS.node_height {
                assert!(expected_height > 0 && j < 2);
                assert_eq!(height + 1, expected_height);
                assert_eq!(node, 2 * OBS.idx + j as u32);
                assert!(core::ptr::from_ref(self).cast() == OBS.hash);
                assert!(core::ptr::from_ref(seed).cast() == OBS.sig);
                let expected = OBS.address;
                assert_eq!(addr.as_bytes(), &expected);
                let value = kani::any();
                OBS.auth[j] = value;
                OBS.layer = j + 1;
                return Array(value);
            }
            assert!(j < HP && height == j as u32);
            assert!(node == ((OBS.idx >> j) ^ 1));
            assert!(core::ptr::from_ref(self).cast() == OBS.hash);
            assert!(core::ptr::from_ref(seed).cast() == OBS.sig);
            let mut expected = OBS.address;
            expected[20..24].copy_from_slice(&OBS.idx.to_be_bytes());
            assert_eq!(addr.as_bytes(), &expected);
            let sibling = kani::any();
            OBS.auth[j] = sibling;
            OBS.layer = j + 1;
            Array(sibling)
        }
    }
}
const N: usize = PARAM_N;
const HP: usize = PARAM_HP;

struct Transcript {
    node_height: Option<u32>,
    hash: *const (),
    sig: *const (),
    idx: u32,
    layer: usize,
    address: [u8; 32],
    previous: [u8; N],
    auth: [[u8; N]; HP],
}
static mut OBS: Transcript = Transcript {
    node_height: None,
    hash: core::ptr::null(),
    sig: core::ptr::null(),
    idx: 0x91b77,
    layer: usize::MAX,
    address: [0; 32],
    previous: [0; N],
    auth: [[0; N]; HP],
};

impl WotsParams for P {
    type WotsMsgLen = <Actual as WotsParams>::WotsMsgLen;
    type WotsSigLen = <Actual as WotsParams>::WotsSigLen;
    fn wots_pk_gen(&self, seed: &SkSeed<Self::N>, addr: &WotsHash) -> Array<u8, Self::N> {
        unsafe {
            assert!(OBS.node_height == Some(0) && OBS.layer == 0);
            assert!(core::ptr::from_ref(self).cast() == OBS.hash);
            assert!(core::ptr::from_ref(seed).cast() == OBS.sig);
            let mut expected = OBS.address;
            expected[20..24].copy_from_slice(&OBS.idx.to_be_bytes());
            assert_eq!(addr.as_bytes(), &expected);
            let result = kani::any();
            OBS.previous = result;
            OBS.layer = 1;
            Array(result)
        }
    }
    fn wots_sign(
        &self,
        m: &Array<u8, Self::N>,
        seed: &SkSeed<Self::N>,
        addr: &WotsHash,
    ) -> WotsSig<Self> {
        unsafe {
            assert!(OBS.layer == usize::MAX);
            assert!(core::ptr::from_ref(self).cast() == OBS.hash);
            assert!(core::ptr::from_ref(seed).cast() == OBS.sig);
            let msg = OBS.previous;
            assert_eq!(m.as_slice(), &msg);
            let mut expected = OBS.address;
            expected[20..24].copy_from_slice(&OBS.idx.to_be_bytes());
            assert_eq!(addr.as_bytes(), &expected);
            OBS.layer = 0;
            // Every bit-pattern is valid for the concrete WOTS array of bytes.
            let raw = kani::any::<[u8; WotsSig::<P>::SIZE]>();
            WOTS_OUTPUT = raw;
            core::mem::transmute(raw)
        }
    }
    fn wots_pk_from_sig(
        &self,
        sig: &WotsSig<Self>,
        m: &Array<u8, Self::N>,
        addr: &WotsHash,
    ) -> Array<u8, Self::N> {
        unsafe {
            assert!(OBS.layer == usize::MAX);
            assert!(core::ptr::from_ref(self).cast() == OBS.hash);
            assert!(core::ptr::from_ref(sig).cast() == OBS.sig);
            let previous = OBS.previous;
            assert_eq!(m.as_slice(), &previous);
            let mut expected = OBS.address;
            expected[20..24].copy_from_slice(&OBS.idx.to_be_bytes());
            assert_eq!(addr.as_bytes(), &expected);
            let output: [u8; N] = kani::any();
            OBS.previous = output;
            OBS.layer = 0;
            output.as_slice().try_into().unwrap()
        }
    }
}
impl HashSuite for P {
    type N = <Actual as HashSuite>::N;
    type M = <Actual as HashSuite>::M;
    fn new_from_pk_seed(pk: &PkSeed<Self::N>) -> Self {
        P(pk.0.0)
    }
    fn prf_msg(
        _: &SkPrf<Self::N>,
        _: &Array<u8, Self::N>,
        _: &[&[impl AsRef<[u8]>]],
    ) -> Array<u8, Self::N> {
        unreachable!()
    }
    fn h_msg(
        _: &Array<u8, Self::N>,
        _: &PkSeed<Self::N>,
        _: &Array<u8, Self::N>,
        _: &[&[impl AsRef<[u8]>]],
    ) -> Array<u8, Self::M> {
        unreachable!()
    }
    fn t<L: ArraySize>(
        &self,
        _: &impl Address,
        _: &Array<Array<u8, Self::N>, L>,
    ) -> Array<u8, Self::N> {
        unreachable!()
    }
    fn prf_sk(&self, _: &SkSeed<Self::N>, _: &impl Address) -> Array<u8, Self::N> {
        unreachable!()
    }
    fn f(&self, _: &impl Address, _: &Array<u8, Self::N>) -> Array<u8, Self::N> {
        unreachable!()
    }
    fn h(
        &self,
        addr: &impl Address,
        left: &Array<u8, Self::N>,
        right: &Array<u8, Self::N>,
    ) -> Array<u8, Self::N> {
        unsafe {
            let j = OBS.layer;
            if let Some(height) = OBS.node_height {
                assert!(height > 0 && j == 2);
                assert!(core::ptr::from_ref(self).cast() == OBS.hash);
                let mut expected = OBS.address;
                expected[16..20].copy_from_slice(&2u32.to_be_bytes());
                expected[20..24].fill(0);
                expected[24..28].copy_from_slice(&height.to_be_bytes());
                expected[28..].copy_from_slice(&OBS.idx.to_be_bytes());
                assert_eq!(addr.as_ref(), &expected);
                let [l, r] = [OBS.auth[0], OBS.auth[1]];
                assert_eq!(left.as_slice(), &l);
                assert_eq!(right.as_slice(), &r);
                let result = kani::any();
                OBS.previous = result;
                OBS.layer = 3;
                return Array(result);
            }
            assert!(j < HP);
            assert!(core::ptr::from_ref(self).cast() == OBS.hash);
            let idx = OBS.idx >> j;
            let mut expected = OBS.address;
            expected[16..20].copy_from_slice(&2u32.to_be_bytes());
            expected[20..24].fill(0);
            expected[24..28].copy_from_slice(&((j + 1) as u32).to_be_bytes());
            expected[28..].copy_from_slice(&(idx >> 1).to_be_bytes());
            assert_eq!(addr.as_ref(), &expected);
            let previous = OBS.previous;
            let sibling = OBS.auth[j];
            let (l, r) = if idx & 1 == 0 {
                (previous, sibling)
            } else {
                (sibling, previous)
            };
            assert_eq!(left.as_slice(), &l);
            assert_eq!(right.as_slice(), &r);
            let output: [u8; N] = kani::any();
            OBS.layer = j + 1;
            OBS.previous = output;
            output.as_slice().try_into().unwrap()
        }
    }
}

#[kani::proof]
#[kani::unwind(72)]
fn recover() {
    let hash = P::new_from_pk_seed(&PkSeed(Array(kani::any::<[u8; N]>())));
    let m: [u8; N] = kani::any();
    let idx: u32 = kani::any();
    let addr = arbitrary_address();
    let raw = kani::any::<[u8; XmssSig::<P>::SIZE]>();
    let sig = unsafe { core::mem::transmute::<_, XmssSig<P>>(raw) };
    unsafe {
        OBS.hash = core::ptr::from_ref(&hash).cast();
        OBS.sig = core::ptr::from_ref(&sig.sig).cast();
        OBS.idx = idx;
        OBS.address = addr.as_bytes().try_into().unwrap();
        OBS.previous = m;
        for j in 0..HP {
            OBS.auth[j].copy_from_slice(sig.auth[j].as_slice());
        }
    }
    let out = hash.xmss_pk_from_sig(idx, &sig, &Array(m), &addr);
    unsafe {
        let root = OBS.previous;
        assert!(OBS.layer == HP);
        assert_eq!(out.as_slice(), &root);
    }
}

fn arbitrary_address() -> WotsHash {
    let mut addr = WotsHash::default();
    addr.layer_adrs.set(kani::any());
    addr.tree_adrs_high.set(kani::any());
    addr.tree_adrs_low.set(kani::any());
    addr.key_pair_adrs.set(kani::any());
    addr.chain_adrs.set(kani::any());
    addr.hash_adrs.set(kani::any());
    addr
}

static mut WOTS_OUTPUT: [u8; WotsSig::<P>::SIZE] = [0x81; WotsSig::<P>::SIZE];
#[kani::proof]
#[kani::unwind(72)]
fn sign() {
    let hash = P(kani::any());
    let seed = SkSeed(Array(kani::any::<[u8; N]>()));
    let msg = kani::any::<[u8; N]>();
    let idx: u32 = kani::any();
    kani::assume(idx < 1 << HP);
    let addr = arbitrary_address();
    unsafe {
        OBS.hash = core::ptr::from_ref(&hash).cast();
        OBS.sig = core::ptr::from_ref(&seed).cast();
        OBS.address = addr.as_bytes().try_into().unwrap();
        OBS.idx = idx;
        OBS.previous = msg;
    }
    let out = hash.xmss_sign(&Array(msg), &seed, idx, &addr);
    unsafe {
        assert!(OBS.layer == HP);
        let actual: [u8; WotsSig::<P>::SIZE] = core::mem::transmute(out.sig);
        let expected = WOTS_OUTPUT;
        // The symbolic index covers every byte in the returned WOTS signature.
        let i: usize = kani::any();
        kani::assume(i < actual.len());
        assert!(actual[i] == expected[i]);
        for j in 0..HP {
            let expected = OBS.auth[j];
            assert_eq!(out.auth[j].as_slice(), &expected);
        }
    }
}

#[kani::proof]
#[kani::unwind(72)]
fn node() {
    let hash = P(kani::any());
    let seed = SkSeed(Array(kani::any::<[u8; N]>()));
    let addr = arbitrary_address();
    let height: u32 = kani::any();
    kani::assume(height <= HP as u32);
    let idx: u32 = kani::any();
    kani::assume(idx < 1 << (HP as u32 - height));
    unsafe {
        OBS.hash = core::ptr::from_ref(&hash).cast();
        OBS.sig = core::ptr::from_ref(&seed).cast();
        OBS.address = addr.as_bytes().try_into().unwrap();
        OBS.idx = idx;
        OBS.node_height = Some(height);
        OBS.layer = 0;
    }
    let out = hash.proof_one_node(&seed, idx, height, &addr);
    unsafe {
        let result = OBS.previous;
        assert_eq!(out.as_slice(), &result);
        assert!(OBS.layer == if height == 0 { 1 } else { 3 });
    }
}
