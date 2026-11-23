// Included inside the pinned peer's hypertree module, once per concrete suite.
use super::{HypertreeParams, HypertreeSig};
use crate::address::WotsHash;
use crate::hashes::HashSuite;
use crate::xmss::{XmssParams, XmssSig};
use crate::PkSeed;
use hybrid_array::Array;
use zerocopy::IntoBytes;

type P = crate::PEER_TYPE;
const N: usize = PARAM_N;
const D: usize = PARAM_D;
const HP: usize = PARAM_HP;

static mut LAYER: usize = 0;
static mut TREE: u64 = 0;
static mut LEAF: u32 = 0;
static mut PREVIOUS: [u8; N] = [0; N];
static mut SIGS: [*const (); D] = [core::ptr::null(); D];
static mut HASH: *const () = core::ptr::null();

trait ObserveXmss: XmssParams {
    fn checked_pk_from_sig(&self, index: u32, sig: &XmssSig<Self>, message: &Array<u8, Self::N>,
                           address: &WotsHash) -> Array<u8, Self::N> {
        unsafe {
            let j = LAYER;
            assert!(j < D);
            assert!(core::ptr::from_ref(self).cast::<()>() == HASH);
            assert!(core::ptr::from_ref(sig).cast::<()>() == SIGS[j]);
            let previous = PREVIOUS;
            assert_eq!(message.as_slice(), &previous);
            let tree = (u128::from(TREE) >> (HP*j)) as u64;
            let leaf = if j == 0 { LEAF } else { ((TREE >> (HP*(j-1))) & ((1u64 << HP)-1)) as u32 };
            assert_eq!(index, leaf);
            let mut encoded = [0u8; 32];
            encoded[..4].copy_from_slice(&(j as u32).to_be_bytes());
            encoded[8..16].copy_from_slice(&tree.to_be_bytes());
            assert_eq!(address.as_bytes(), &encoded);
            let next: [u8; N] = kani::any();
            PREVIOUS = next;
            LAYER = j+1;
            next.as_slice().try_into().unwrap()
        }
    }
}
impl<S: XmssParams> ObserveXmss for S {}

#[kani::proof]
#[kani::unwind(72)]
#[kani::stub(crate::xmss::XmssParams::xmss_pk_from_sig, ObserveXmss::checked_pk_from_sig)]
fn verify_layers() {
    let seed = PkSeed(Array(kani::any::<[u8; N]>()));
    let hash = P::new_from_pk_seed(&seed);
    let message: [u8; N] = kani::any();
    let expected: [u8; N] = kani::any();
    let tree = kani::any();
    let leaf = kani::any();
    // The concrete signature consists entirely of fixed arrays of u8. The
    // transmute checks the size at compile time and covers every typed value.
    let repr = kani::any::<[u8; HypertreeSig::<P>::SIZE]>();
    let sig = unsafe { core::mem::transmute::<_, HypertreeSig<P>>(repr) };
    unsafe {
        TREE = tree;
        LEAF = leaf;
        PREVIOUS = message;
        HASH = core::ptr::from_ref(&hash).cast();
        for j in 0..D {
            SIGS[j] = core::ptr::from_ref(&sig.0[j]).cast();
        }
    }
    let decision = hash.ht_verify(&Array(message), &sig, tree, leaf, &Array(expected));
    unsafe {
        let last = PREVIOUS;
        assert!(LAYER == D);
        assert!(decision == (last == expected));
    }
}
