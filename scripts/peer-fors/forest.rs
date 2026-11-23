// The actual pinned container constructor and writer on fully symbolic bytes.
// An arbitrary row, node, and byte compares the actual parsed fields to FIPS order.
use crate::fors::ForsSignature;

type P = crate::PEER_TYPE;
const N: usize = PARAM_N;
const A: usize = PARAM_A;
const K: usize = PARAM_K;
const SIZE: usize = (A + 1) * K * N;

#[kani::proof]
#[kani::unwind(75)]
fn forest() {
    let buffer: [u8; SIZE] = kani::any();
    let sig = ForsSignature::<P>::try_from(buffer.as_slice()).unwrap();
    let word: usize = kani::any();
    let t: usize = kani::any();
    let b: usize = kani::any();
    kani::assume(t < K && word <= A && b < N);
    let offset = (t * (A + 1) + word) * N + b;
    let value = if word == 0 {
        sig.0[t].sk[b]
    } else {
        sig.0[t].auth[word - 1][b]
    };
    assert_eq!(value, buffer[offset]);
    let mut dest: [u8; SIZE] = kani::any();
    sig.write_to(&mut dest);
    assert_eq!(dest[offset], buffer[offset]);
}
