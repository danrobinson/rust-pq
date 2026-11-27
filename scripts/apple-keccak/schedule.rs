// A token identifies a complete symbolic lane and the ordered calls on that lane.
// Its low coordinate identifies each of the 25 independent words when the Rust
// code loads, shuffles, and stores lanes. Only the four round bodies are opaque.
use std::cell::{Cell, RefCell};
const WIDTH: usize = 8;
// The schedule can copy a word but has no arithmetic, comparison, or conversion on it.
#[derive(Clone, Copy)]
struct Word(usize);
type States = [[Word; WIDTH]; 25];
type V = [Word; 2];
// ROUND_CONSTANTS

#[derive(Clone)]
struct Trace {
    source: usize,
    calls: Vec<(&'static str, u64)>,
}
thread_local! {
    static TRACES: RefCell<Vec<Trace>> = const { RefCell::new(Vec::new()) };
    static SHA3: Cell<bool> = const { Cell::new(false) };
}
mod sha512 {
    pub mod hw {
        pub mod arm {
            pub fn available() -> bool {
                crate::SHA3.get()
            }
        }
    }
}

fn token(a: &[Word; 25]) -> usize {
    let id = a[0].0 / 25;
    for (i, word) in a.iter().enumerate() {
        assert_eq!(word.0, id * 25 + i, "mixed Keccak coordinates");
    }
    id
}

fn advance(a: &mut [Word; 25], rc: u64, kind: &'static str) {
    let input = token(a);
    TRACES.with_borrow_mut(|traces| {
        let mut next = traces[input].clone();
        next.calls.push((kind, rc));
        let id = traces.len();
        traces.push(next);
        *a = std::array::from_fn(|i| Word(id * 25 + i));
    });
}
fn round_scalar(a: &mut [Word; 25], rc: u64) {
    advance(a, rc, "scalar")
}

fn pair(a: [V; 25], rc: u64, kind: &'static str) -> [V; 25] {
    let mut result = a;
    for j in 0..2 {
        let mut lane = std::array::from_fn(|i| a[i][j]);
        advance(&mut lane, rc, kind);
        for i in 0..25 {
            result[i][j] = lane[i];
        }
    }
    result
}
unsafe fn round_sha3(a: [V; 25], rc: u64) -> [V; 25] {
    pair(a, rc, "sha3")
}
unsafe fn round_neon(a: [V; 25], rc: u64) -> [V; 25] {
    pair(a, rc, "neon")
}
unsafe fn round_inplace(a: [V; 25], rc: u64) -> [V; 25] {
    pair(a, rc, "inplace")
}

// PRODUCTION

fn main() {
    for n in 0..=WIDTH + 1 {
        for sha3 in [false, true] {
            SHA3.set(sha3);
            TRACES.with_borrow_mut(|ts| {
                *ts = (0..WIDTH)
                    .map(|source| Trace {
                        source,
                        calls: Vec::new(),
                    })
                    .collect();
            });
            let mut result: States =
                std::array::from_fn(|w| std::array::from_fn(|j| Word(25 * j + w)));
            if n > WIDTH {
                permute(&mut result);
            } else {
                permute_active(&mut result, n);
            }
            for lane in 0..WIDTH {
                let out = token(&std::array::from_fn(|i| result[i][lane]));
                TRACES.with_borrow(|ts| {
                    let t = &ts[out];
                    let calls = t
                        .calls
                        .iter()
                        .map(|(k, c)| format!("{k}:{c}"))
                        .collect::<Vec<_>>();
                    println!(
                        "{n} {} {lane} {} {}",
                        u8::from(sha3),
                        t.source,
                        calls.join(" ")
                    );
                });
            }
        }
    }
}
