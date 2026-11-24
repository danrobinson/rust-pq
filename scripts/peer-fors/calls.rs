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
const K: usize = PARAM_K;
const MD: usize = (K * A as usize + 7) / 8;

unsafe extern "C" {
    fn secret_observe(dst: *mut u8, state: *const u8, seed: *const u8, addr: *const u8, index: u32);
    fn node_observe(
        dst: *mut u8,
        state: *const u8,
        seed: *const u8,
        addr: *const u8,
        index: u32,
        z: u32,
    );
    fn f_observe(dst: *mut u8, state: *const u8, addr: *const u8, v: *const u8);
    fn h_observe(dst: *mut u8, state: *const u8, addr: *const u8, l: *const u8, r: *const u8);
    fn t_observe(dst: *mut u8, state: *const u8, addr: *const u8, v: *const u8, k: usize);
}
params! {
    fn fors_sk_gen(&self, seed:&SkSeed<Self::N>, addr:&ForsTree, i:u32)->Array<u8,Self::N> {
        let mut x=Array::default(); unsafe {secret_observe(x.as_mut_ptr(),self.0.as_ptr(),seed.0.as_ptr(),addr.as_ref().as_ptr(),i)};x
    }
    fn fors_node(&self,seed:&SkSeed<Self::N>,i:u32,z:u32,addr:&ForsTree)->Array<u8,Self::N>{
        let mut x=Array::default();unsafe {node_observe(x.as_mut_ptr(),self.0.as_ptr(),seed.0.as_ptr(),addr.as_ref().as_ptr(),i,z)};x
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
        a: &impl Address,
        r: &Array<Array<u8, Self::N>, L>,
    ) -> Array<u8, Self::N> {
        let mut x = Array::default();
        unsafe {
            t_observe(
                x.as_mut_ptr(),
                self.0.as_ptr(),
                a.as_ref().as_ptr(),
                r.as_ptr().cast(),
                r.len(),
            )
        };
        x
    }
    fn f(&self, a: &impl Address, v: &Array<u8, Self::N>) -> Array<u8, Self::N> {
        let mut x = Array::default();
        unsafe {
            f_observe(
                x.as_mut_ptr(),
                self.0.as_ptr(),
                a.as_ref().as_ptr(),
                v.as_ptr(),
            )
        };
        x
    }
    fn h(
        &self,
        a: &impl Address,
        l: &Array<u8, Self::N>,
        r: &Array<u8, Self::N>,
    ) -> Array<u8, Self::N> {
        let mut x = Array::default();
        unsafe {
            h_observe(
                x.as_mut_ptr(),
                self.0.as_ptr(),
                a.as_ref().as_ptr(),
                l.as_ptr(),
                r.as_ptr(),
            )
        };
        x
    }
    fn prf_sk(&self, _: &SkSeed<Self::N>, _: &impl Address) -> Array<u8, Self::N> {
        unreachable!()
    }
}

#[unsafe(no_mangle)]
pub fn SUITE_sign(
    md: &[u8; MD],
    state: &P,
    seed: &SkSeed<<P as HashSuite>::N>,
    addr: &ForsTree,
    out: &mut [u8; N * K * (1 + A as usize)],
) {
    let sig = state.fors_sign(&Array(*md), seed, addr);
    sig.write_to(out);
}
#[unsafe(no_mangle)]
pub fn SUITE_recover(
    md: &[u8; MD],
    state: &P,
    addr: &ForsTree,
    sig: &[u8; N * K * (1 + A as usize)],
    out: &mut [u8; N],
) {
    let sig = crate::fors::ForsSignature::<P>::try_from(sig.as_slice()).unwrap();
    *out = state.fors_pk_from_sig(&sig, &Array(*md), addr).0;
}
