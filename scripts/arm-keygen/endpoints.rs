// Shared symbolic vector operations from hash-routes.rs precede this module.
const WOTS_PRF: u32 = 5;
const WOTS_HASH: u32 = 0;
const LEN2: usize = 3;
#[derive(Clone, Copy)]
struct Adrs {
    typ: u32,
    keypair: u32,
}
impl Adrs {
    fn with_type(self, typ: u32) -> Self {
        Self { typ, keypair: 0 }
    }
    fn with_keypair(self, keypair: u32) -> Self {
        Self { keypair, ..self }
    }
}
fn make_head(state: &[u32; 8], a: Adrs) -> Head {
    assert_eq!(state, &STATE);
    assert_eq!(a.keypair, 97);
    let t = a.typ as usize;
    Head {
        m0: V::Head(t, 0),
        a1: V::Head(t, 1),
        e1: V::Head(t, 2),
    }
}
fn load_n<const N: usize>(sk: &[u8; N]) -> (V, V) {
    assert_eq!(sk, &[57; N]);
    (V::Digest(0, false), V::Digest(0, true))
}
fn store_n<const N: usize>(dst: &mut [usize], lo: V, hi: V) {
    assert!(dst.len() >= N);
    let V::Digest(node, false) = lo else {
        panic!("bad low register")
    };
    assert_eq!(hi, V::Digest(node, true));
    LANES.with_borrow(|lanes| {
        let l = &lanes[node];
        print!("{N} {} {}|", dst[0], l.origin);
        for (h, c, t, _) in &l.calls {
            print!("{h},{c},{t};");
        }
        println!();
    });
}
// PRODUCTION
fn run<const N: usize>(size: usize) {
    LANES.with_borrow_mut(|ls| {
        *ls = vec![Lane {
            origin: 0,
            calls: vec![],
        }]
    });
    CALLS.with_borrow_mut(|cs| cs.clear());
    let mut msg = (0..size).collect::<Vec<usize>>();
    wots_endpoints_1_active::<N>(
        &STATE,
        &[57; N],
        Adrs {
            typ: 77,
            keypair: 97,
        },
        &mut msg,
    );
}
fn main() {
    run::<16>(640);
    run::<24>(1280);
    run::<32>(2304);
}
