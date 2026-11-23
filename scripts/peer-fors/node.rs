// The recursive child has an arbitrary result. The harness checks the exact
// RustCrypto node body at any valid level, with both recursive-call arguments.
use crate::address::{Address, ForsTree};
use crate::fors::ForsParams;
use crate::hashes::HashSuite;
use crate::hypertree::HypertreeParams;
use crate::wots::WotsParams;
use crate::xmss::XmssParams;
use crate::{PkSeed, SkPrf, SkSeed};
use hybrid_array::{Array, ArraySize};

include!("shape.rs");
const N: usize = PARAM_N;
const A: u32 = PARAM_A;
const K: u32 = PARAM_K;
static mut ADR: [u8; 32] = [0; 32];
static mut IDX: u32 = 0;
static mut Z: u32 = 0;
static mut CALLS: u32 = 0;
static mut SEED: [u8; N] = [0; N];
static mut STATE: [u8; N] = [0; N];
static mut LEFT: [u8; N] = [0; N];
static mut RIGHT: [u8; N] = [0; N];
static mut OUTPUT: [u8; N] = [0; N];

params! {
    fn fors_node(&self, seed: &SkSeed<Self::N>, idx: u32, z: u32, addr: &ForsTree) -> Array<u8,Self::N> {
        unsafe {
            assert!(seed.0.as_slice() == SEED && self.0 == STATE);
            assert!(addr.as_ref() == ADR && Z>0 && z==Z-1 && CALLS<2 && idx==2*IDX+CALLS);
            assert!(z<=A && idx<K<<(A-z));
            CALLS+=1;
            Array(if CALLS==1 { LEFT } else { RIGHT })
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
    fn prf_sk(&self, seed: &SkSeed<Self::N>, addr: &impl Address) -> Array<u8, Self::N> {
        unsafe {
            assert!(seed.0.as_slice() == SEED && self.0 == STATE);
            assert!(Z == 0 && CALLS == 0);
            let bytes = addr.as_ref();
            let a = ADR;
            assert!(
                bytes[..16] == a[..16]
                    && bytes[16..20] == 6u32.to_be_bytes()
                    && bytes[20..24] == a[20..24]
                    && bytes[24..28] == 0u32.to_be_bytes()
                    && bytes[28..] == IDX.to_be_bytes()
            );
            CALLS += 1;
            Array(LEFT)
        }
    }
    fn f(&self, addr: &impl Address, m: &Array<u8, Self::N>) -> Array<u8, Self::N> {
        unsafe {
            let a = ADR;
            let bytes = addr.as_ref();
            assert!(self.0 == STATE && Z == 0 && CALLS == 1 && m.as_slice() == LEFT);
            assert!(
                bytes[..24] == a[..24]
                    && bytes[24..28] == 0u32.to_be_bytes()
                    && bytes[28..] == IDX.to_be_bytes()
            );
            CALLS += 1;
            Array(OUTPUT)
        }
    }
    fn h(
        &self,
        addr: &impl Address,
        l: &Array<u8, Self::N>,
        r: &Array<u8, Self::N>,
    ) -> Array<u8, Self::N> {
        unsafe {
            let a = ADR;
            let bytes = addr.as_ref();
            assert!(self.0 == STATE && Z > 0 && CALLS == 2);
            assert!(
                bytes[..24] == a[..24]
                    && bytes[24..28] == Z.to_be_bytes()
                    && bytes[28..] == IDX.to_be_bytes()
            );
            assert!(l.as_slice() == LEFT && r.as_slice() == RIGHT);
            CALLS += 1;
            Array(OUTPUT)
        }
    }
}

#[kani::proof]
#[kani::unwind(70)]
fn node() {
    let id: u32 = kani::any();
    let z: u32 = kani::any();
    kani::assume(z <= A);
    kani::assume(id < K << (A - z));
    let mut addr = ForsTree::new(kani::any(), kani::any());
    addr.tree_height.set(kani::any());
    addr.tree_index.set(kani::any());
    let seed = SkSeed(Array(kani::any::<[u8; N]>()));
    let hash = P(kani::any());
    let result: [u8; N] = kani::any();
    unsafe {
        ADR = addr.as_ref().try_into().unwrap();
        STATE = hash.0;
        SEED = seed.0.0;
        IDX = id;
        Z = z;
        LEFT = kani::any();
        RIGHT = kani::any();
        OUTPUT = result;
    }
    let value = hash.proof_one_node(&seed, id, z, &addr);
    assert!(value.as_slice() == result);
    unsafe {
        assert!(CALLS == if z == 0 { 2 } else { 3 });
    }
}
