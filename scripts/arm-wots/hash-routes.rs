// Symbolic register routing only. The mathematical meaning of each SHA-256
// operation is supplied by Armwide.Kernel in the Lean consumer of these traces.
#![allow(unused_unsafe, dead_code)]
use std::cell::RefCell;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum V {
    Zero,
    Digest(usize, bool), // node id, high register
    Head(usize, u8),     // source head, message/ABCD/EFGH component
    Block(usize, u8),    // symbolic pack_short call, schedule component
}
#[derive(Clone, Copy)]
struct Head {
    m0: V,
    a1: V,
    e1: V,
}
type Hdr = (u32, u32);
#[allow(non_camel_case_types)]
type uint16x8_t = Hdr;
struct Call {
    n: usize,
    hdr: Hdr,
    x: V,
    xb: V,
}
#[derive(Clone)]
struct Lane {
    origin: usize,
    calls: Vec<(usize, u32, u32, bool)>,
}
thread_local! {
    static CALLS:RefCell<Vec<Call>>=const {RefCell::new(Vec::new())};
    static LANES:RefCell<Vec<Lane>>=const {RefCell::new(Vec::new())};
}
fn make_hdr(c: u32, t: u32) -> Hdr {
    (c, t)
}
fn vdupq_n_u32(x: u32) -> V {
    assert_eq!(x, 0);
    V::Zero
}
fn pack_short<const N: usize>(hdr: Hdr, x: V, xb: V) -> (V, V, V) {
    let id = CALLS.with_borrow_mut(|cs| {
        let id = cs.len();
        cs.push(Call { n: N, hdr, x, xb });
        id
    });
    (V::Block(id, 1), V::Block(id, 2), V::Block(id, 3))
}
static K: [u32; 64] = [0; 64];
const STATE: [u32; 8] = [13; 8];
fn finish_from_r4<const L: usize, const HIGH: bool>(
    st: &[u32; 8],
    a1: [V; L],
    e1: [V; L],
    m0: [V; L],
    m1: [V; L],
    m2: [V; L],
    m3: [V; L],
    k: *const u32,
) -> ([V; L], [V; L]) {
    assert_eq!(k, K.as_ptr());
    assert_eq!(st, &STATE);
    let ids: [usize; L] = std::array::from_fn(|i| {
        let V::Head(h, 0) = m0[i] else {
            panic!("wrong first message word")
        };
        assert_eq!((a1[i], e1[i]), (V::Head(h, 1), V::Head(h, 2)));
        let V::Block(c, 1) = m1[i] else {
            panic!("wrong second message word")
        };
        assert_eq!((m2[i], m3[i]), (V::Block(c, 2), V::Block(c, 3)));
        CALLS.with_borrow(|cs| {
            LANES.with_borrow_mut(|ls| {
                let v = &cs[c];
                let V::Digest(source, false) = v.x else {
                    panic!("wrong low input")
                };
                assert_eq!(v.xb, V::Digest(source, true));
                assert_eq!(HIGH, v.n != 16);
                let mut next = ls[source].clone();
                next.calls.push((h, v.hdr.0, v.hdr.1, HIGH));
                let id = ls.len();
                ls.push(next);
                id
            })
        })
    });
    (
        ids.map(|i| V::Digest(i, false)),
        ids.map(|i| V::Digest(i, true)),
    )
}

// PRODUCTION

fn lift<const N: usize>(active: usize, steps: u32, shared: bool) {
    LANES.with_borrow_mut(|ls| {
        *ls = (0..4)
            .map(|origin| Lane {
                origin,
                calls: vec![],
            })
            .collect()
    });
    CALLS.with_borrow_mut(|cs| cs.clear());
    let z = V::Zero;
    let state = &STATE;
    let k_ptr = K.as_ptr();
    let heads: [Head; 4] = std::array::from_fn(|i| Head {
        m0: V::Head(i, 0),
        a1: V::Head(i, 1),
        e1: V::Head(i, 2),
    });
    let hash_head = Head {
        m0: V::Head(4, 0),
        a1: V::Head(4, 1),
        e1: V::Head(4, 2),
    };
    let chain: [usize; 4] = [0, 1, 2, 3];
    let cur_t: [u32; 4] = [32, 64, 96, 128];
    let mut x: [V; 4] = std::array::from_fn(|i| V::Digest(i, false));
    let mut xb: [V; 4] = std::array::from_fn(|i| V::Digest(i, true));
    if active < 4 {
        // TAIL_HASH
    } else if shared {
        // SHARED_HASH
    } else {
        // MIXED_HASH
    }
    for l in 0..active {
        let V::Digest(id, false) = x[l] else {
            panic!("wrong low output")
        };
        assert_eq!(xb[l], V::Digest(id, true));
        LANES.with_borrow(|ls| {
            let trace = &ls[id];
            print!(
                "{N} {active} {steps} {} {l} {}|",
                usize::from(shared),
                trace.origin
            );
            for &(h, chain, t, high) in &trace.calls {
                print!("{h},{chain},{t},{};", usize::from(high));
            }
            println!();
        });
    }
}
fn run<const N: usize>() {
    for active in 1..=4 {
        lift::<N>(active, 1, false);
    }
    for steps in 1..=15 {
        lift::<N>(4, steps, true);
    }
}
fn main() {
    run::<16>();
    run::<24>();
    run::<32>();
}
