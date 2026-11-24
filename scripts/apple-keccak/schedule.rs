// Each tag denotes an arbitrary 1600-bit input after a prefix of FIPS rounds.
// Keeping the coordinate in the tag also detects mixed or transposed stores.
const WIDTH: usize = 8;
type States = [[u64; WIDTH]; 25];
type V = [u64; 2];
// ROUND_CONSTANTS

fn advance(a: &mut [u64; 25], rc: u64) {
    let first = a[0];
    let step = (first / 25 % 25) as usize;
    assert!(step < 24 && RC[step] == rc);
    for (i, w) in a.iter_mut().enumerate() {
        assert_eq!(*w, first - first % 25 + i as u64);
        *w += 25;
    }
}
fn round_scalar(a: &mut [u64; 25], rc: u64) {
    advance(a, rc)
}
unsafe fn round(a: [V; 25], rc: u64) -> [V; 25] {
    let mut result = a;
    for j in 0..2 {
        let mut lane = std::array::from_fn(|i| a[i][j]);
        advance(&mut lane, rc);
        for i in 0..25 {
            result[i][j] = lane[i];
        }
    }
    result
}
unsafe fn round_inplace(a: [V; 25], rc: u64) -> [V; 25] {
    round(a, rc)
}

// PRODUCTION

fn main() {
    for n in 0..=WIDTH {
        for sha3 in [false, true] {
            let initial: States =
                std::array::from_fn(|w| std::array::from_fn(|lane| (lane * 625 + w) as u64));
            let mut result = initial;
            unsafe {
                if sha3 {
                    sha3::permute_active(&mut result, n);
                } else {
                    neon::permute_active(&mut result, n);
                }
            }
            for w in 0..25 {
                for lane in 0..n {
                    assert_eq!(result[w][lane], initial[w][lane] + 600);
                }
            }
        }
    }
}
