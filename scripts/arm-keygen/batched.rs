// Shared symbolic vector operations from hash-routes.rs precede this module.
const WOTS_PRF: u32 = 5;
const WOTS_HASH: u32 = 0;
const LEN2: usize = 3;

// All keypair computations are affine offsets from an arbitrary first key.
#[derive(Clone, Copy)]
struct Keypair(u32);
impl std::ops::Add<u32> for Keypair {
    type Output = Self;
    fn add(self, delta: u32) -> Self {
        Keypair(self.0.checked_add(delta).unwrap())
    }
}

#[derive(Clone, Copy)]
struct Adrs {
    typ: u32,
    keypair: Option<Keypair>,
}
impl Adrs {
    fn with_type(self, typ: u32) -> Self {
        Self { typ, keypair: None }
    }
    fn with_keypair(self, keypair: Keypair) -> Self {
        Self {
            keypair: Some(keypair),
            ..self
        }
    }
}

fn make_head(state: &[u32; 8], a: Adrs) -> Head {
    assert_eq!(state, &STATE);
    let h = 8 * a.keypair.expect("missing keypair").0 as usize + a.typ as usize;
    Head {
        m0: V::Head(h, 0),
        a1: V::Head(h, 1),
        e1: V::Head(h, 2),
    }
}
fn load_n<const N: usize>(sk: &[u8; N]) -> (V, V) {
    assert_eq!(sk, &[57; N]);
    (V::Digest(0, false), V::Digest(0, true))
}
#[derive(Clone, Copy)]
struct Cell {
    offset: usize,
    written: Option<(usize, usize)>,
}
fn zero<const L: usize, const G: usize>() -> [[Cell; L]; G] {
    std::array::from_fn(|k| {
        std::array::from_fn(|b| Cell {
            offset: k * L + b,
            written: None,
        })
    })
}
fn validate<const N: usize, const L: usize, const G: usize>(rows: &[[Cell; L]; G]) {
    for (k, row) in rows.iter().enumerate() {
        for (b, cell) in row.iter().enumerate() {
            assert_eq!(cell.offset, k * L + b);
            if (22..22 + N * (2 * N + 3)).contains(&b) {
                let (_, byte) = cell.written.expect("endpoint byte was never written");
                assert_eq!(byte, (b - 22) % N);
            } else {
                assert!(cell.written.is_none());
            }
        }
    }
}
fn store_n<const N: usize>(dst: &mut [Cell], lo: V, hi: V) {
    assert!(dst.len() >= N);
    let V::Digest(node, false) = lo else {
        panic!("wrong low register")
    };
    assert_eq!(hi, V::Digest(node, true));
    LANES.with_borrow(|ls| {
        let l = &ls[node];
        print!("{} {}|", dst[0].offset, l.origin);
        for (b, cell) in dst[..N].iter_mut().enumerate() {
            assert!(cell.written.replace((node, b)).is_none());
        }
        for (h, c, t, _) in &l.calls {
            print!("{h},{c},{t};");
        }
        println!();
    });
}
// PRODUCTION
fn run<const N: usize, const L: usize, const G: usize>() {
    LANES.with_borrow_mut(|ls| {
        *ls = vec![Lane {
            origin: 0,
            calls: vec![],
        }]
    });
    CALLS.with_borrow_mut(|cs| cs.clear());
    let a = Adrs {
        typ: 77,
        keypair: None,
    };
    println!("GROUP {N} {L} {G}");
    if G == 2 {
        let mut msgs = zero();
        wots_endpoints_2_active::<N, L>(&STATE, &[57; N], a, Keypair(0), &mut msgs);
        validate::<N, L, 2>(&msgs);
    } else {
        let mut msgs = zero();
        wots_endpoints_4_active::<N, L>(&STATE, &[57; N], a, Keypair(0), &mut msgs);
        validate::<N, L, 4>(&msgs);
    }
}
fn main() {
    run::<16, 640, 2>();
    run::<16, 640, 4>();
    run::<24, 1280, 2>();
    run::<24, 1280, 4>();
    run::<32, 2304, 2>();
    run::<32, 2304, 4>();
}
