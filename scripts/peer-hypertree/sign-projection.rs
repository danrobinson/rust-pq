// Hypertree's generic algorithm treats each XMSS signature as an opaque value.
// Exercise its moves, indexes and unwraps on smaller byte arrays while retaining
// the production layer count and per-layer tree height.
use crate::SkPrf;
use crate::address::Address;
use crate::wots::WotsParams;
use hybrid_array::ArraySize;
use typenum::U1;
type Actual = crate::PEER_TYPE;
#[derive(Clone, Debug)]
struct P(u8);
impl HashSuite for P {
    type N = U1;
    type M = U1;
    fn new_from_pk_seed(pk: &PkSeed<U1>) -> Self {
        Self(pk.0[0])
    }
    fn prf_msg(_: &SkPrf<U1>, _: &Array<u8, U1>, _: &[&[impl AsRef<[u8]>]]) -> Array<u8, U1> {
        unreachable!()
    }
    fn h_msg(
        _: &Array<u8, U1>,
        _: &PkSeed<U1>,
        _: &Array<u8, U1>,
        _: &[&[impl AsRef<[u8]>]],
    ) -> Array<u8, U1> {
        unreachable!()
    }
    fn prf_sk(&self, _: &SkSeed<U1>, _: &impl Address) -> Array<u8, U1> {
        unreachable!()
    }
    fn t<L: ArraySize>(&self, _: &impl Address, _: &Array<Array<u8, U1>, L>) -> Array<u8, U1> {
        unreachable!()
    }
    fn h(&self, _: &impl Address, _: &Array<u8, U1>, _: &Array<u8, U1>) -> Array<u8, U1> {
        unreachable!()
    }
    fn f(&self, _: &impl Address, _: &Array<u8, U1>) -> Array<u8, U1> {
        unreachable!()
    }
}
impl WotsParams for P {
    type WotsMsgLen = U1;
    type WotsSigLen = U1;
}
impl XmssParams for P {
    type HPrime = <Actual as XmssParams>::HPrime;
}
impl HypertreeParams for P {
    type D = <Actual as HypertreeParams>::D;
    type H = <Actual as HypertreeParams>::H;
}
