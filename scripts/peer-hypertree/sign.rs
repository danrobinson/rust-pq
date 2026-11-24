// Included in the locked peer's hypertree module; the real ht_sign is unmodified.
use super::HypertreeParams;
use crate::address::WotsHash;
use crate::hashes::HashSuite;
use crate::xmss::{XmssParams, XmssSig};
use crate::{PkSeed, SkSeed};
use hybrid_array::Array;
use zerocopy::IntoBytes;

type P = crate::PEER_TYPE;
const N: usize = PARAM_N;
const D: usize = PARAM_D;
const HP: usize = PARAM_HP;
static mut LAYER: usize = 0;
static mut RECOVERED: usize = 0;
static mut TREE: u64 = 0;
static mut LEAF: u32 = 0;
static mut PREVIOUS: [u8; N] = [0; N];
static mut SAMPLE: usize = 0;
static mut BYTES: [u8; D] = [0; D];
static mut HASH: *const () = core::ptr::null();
static mut SECRET: *const () = core::ptr::null();

fn check_args<S: XmssParams>(
    suite: &S,
    layer: usize,
    idx: u32,
    msg: &Array<u8, S::N>,
    adrs: &WotsHash,
) {
    unsafe {
        assert!(layer < D);
        let expected_tree = (u128::from(TREE) >> (HP * layer)) as u64;
        let expected_leaf = if layer == 0 {
            LEAF
        } else {
            ((TREE >> (HP * (layer - 1))) & ((1u64 << HP) - 1)) as u32
        };
        assert_eq!(idx, expected_leaf);
        let mut expected = [0u8; 32];
        expected[..4].copy_from_slice(&(layer as u32).to_be_bytes());
        expected[8..16].copy_from_slice(&expected_tree.to_be_bytes());
        assert_eq!(adrs.as_bytes(), &expected);
        let previous = PREVIOUS;
        assert_eq!(msg.as_slice(), &previous);
        assert!(core::ptr::from_ref(suite).cast::<()>() == HASH);
    }
}

trait Observe: XmssParams {
    fn checked_sign(
        &self,
        msg: &Array<u8, Self::N>,
        sk: &SkSeed<Self::N>,
        idx: u32,
        adrs: &WotsHash,
    ) -> XmssSig<Self> {
        unsafe {
            let layer = LAYER;
            assert!(layer == RECOVERED);
            check_args(self, layer, idx, msg, adrs);
            assert!(core::ptr::from_ref(sk).cast::<()>() == SECRET);
            let repr = kani::any::<[u8; XmssSig::<P>::SIZE]>();
            assert_eq!(core::mem::size_of::<XmssSig<Self>>(), repr.len());
            BYTES[layer] = repr[SAMPLE];
            LAYER = layer + 1;
            // Every bit pattern is a valid value of the concrete nested byte arrays.
            core::ptr::read_unaligned(repr.as_ptr().cast())
        }
    }

    fn checked_recover(
        &self,
        idx: u32,
        sig: &XmssSig<Self>,
        msg: &Array<u8, Self::N>,
        adrs: &WotsHash,
    ) -> Array<u8, Self::N> {
        unsafe {
            let layer = RECOVERED;
            assert!(LAYER == layer + 1);
            assert!(layer + 1 < D);
            check_args(self, layer, idx, msg, adrs);
            let byte = core::ptr::from_ref(sig).cast::<u8>().add(SAMPLE).read();
            assert_eq!(byte, BYTES[layer]);
            let next = kani::any::<[u8; N]>();
            PREVIOUS = next;
            RECOVERED = layer + 1;
            next.as_slice().try_into().unwrap()
        }
    }
}
impl<S: XmssParams> Observe for S {}

#[kani::proof]
#[kani::unwind(72)]
#[kani::stub(crate::xmss::XmssParams::xmss_sign, Observe::checked_sign)]
#[kani::stub(crate::xmss::XmssParams::xmss_pk_from_sig, Observe::checked_recover)]
fn sign_layers() {
    let seed = PkSeed(Array(kani::any::<[u8; N]>()));
    let secret = SkSeed(Array(kani::any::<[u8; N]>()));
    let hash = P::new_from_pk_seed(&seed);
    let message = kani::any::<[u8; N]>();
    let tree = kani::any();
    let leaf = kani::any();
    let offset: usize = kani::any();
    kani::assume(offset < XmssSig::<P>::SIZE);
    unsafe {
        SAMPLE = offset;
        PREVIOUS = message;
        TREE = tree;
        LEAF = leaf;
        SECRET = core::ptr::from_ref(&secret).cast();
        HASH = core::ptr::from_ref(&hash).cast();
    }
    let sig = hash.ht_sign(&Array(message), &secret, tree, leaf);
    unsafe {
        let signed = LAYER;
        let recovered = RECOVERED;
        assert_eq!(signed, D);
        assert_eq!(recovered, D - 1);
        let j: usize = kani::any();
        kani::assume(j < D);
        let byte = core::ptr::from_ref(&sig.0[j])
            .cast::<u8>()
            .add(offset)
            .read();
        assert_eq!(byte, BYTES[j]);
    }
}
