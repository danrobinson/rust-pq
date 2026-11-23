// Compare the peer's write and read functions independently with the FIPS byte layout.
use crate::fors::ForsMTSig;
use hybrid_array::Array;

type P = crate::PEER_TYPE;
const N: usize = PARAM_N;
const A: usize = PARAM_A;
const SIZE: usize = N * (A + 1);

#[kani::proof]
#[kani::unwind(40)]
fn row() {
    let bytes: [u8; SIZE] = kani::any();
    let parsed = ForsMTSig::<P>::try_from(bytes.as_slice()).unwrap();
    let column: usize = kani::any();
    let level: usize = kani::any();
    kani::assume(column < N && level < A);
    assert_eq!(parsed.sk[column], bytes[column]);
    assert_eq!(parsed.auth[level][column], bytes[(level + 1) * N + column]);

    let secret: [u8; N] = kani::any();
    let auth: [[u8; N]; A] = kani::any();
    let sig = ForsMTSig::<P> {
        sk: Array(secret),
        auth: Array(auth.map(Array)),
    };
    let mut out: [u8; SIZE] = kani::any();
    sig.write_to(&mut out);
    assert_eq!(out[column], secret[column]);
    assert_eq!(out[(level + 1) * N + column], auth[level][column]);

    let bad_len: usize = kani::any();
    kani::assume(bad_len <= SIZE + 1 && bad_len != SIZE);
    let bad = [0u8; SIZE + 1];
    assert!(ForsMTSig::<P>::try_from(&bad[..bad_len]).is_err());
}
