const FORS_PRF: u32 = 6;
const FORS_TREE: u32 = 3;

#[derive(Clone, Copy)]
struct Base(u32);
impl std::ops::Add<u32> for Base {
    type Output = Self;
    fn add(self, offset: u32) -> Self { Self(self.0.checked_add(offset).unwrap()) }
}
#[derive(Clone, Copy)]
struct Adrs { typ: u32, keypair: u32 }
impl Adrs {
    fn with_type(self, typ: u32) -> Self { Self { typ, keypair: 0 } }
    fn with_keypair(self, keypair: u32) -> Self { Self { keypair, ..self } }
}
fn make_head(st: &[u32;8], address: Adrs) -> Head {
    assert_eq!(st, &STATE);
    assert_eq!(address.keypair,97);
    let typ = address.typ as usize;
    Head { m0: V::Head(typ,0), a1: V::Head(typ,1), e1: V::Head(typ,2) }
}
fn load_n<const N: usize>(sk: &[u8;N]) -> (V,V) {
    assert_eq!(sk,&[57;N]);
    (V::Digest(0,false),V::Digest(0,true))
}
fn store_n<const N: usize>(dst: &mut [usize], lo: V, hi: V) {
    assert_eq!(dst.len(),N);
    let slot = dst[0];
    assert!(slot < 128);
    let V::Digest(id,false) = lo else { panic!("bad low register"); };
    assert_eq!(hi,V::Digest(id,true));
    LANES.with_borrow(|lanes| {
        let row = &lanes[id];
        assert_eq!(row.origin,0);
        assert_eq!(row.calls,[(6,0,slot as u32,N!=16),(3,0,slot as u32,N!=16)]);
    });
    dst.fill(usize::MAX);
}
// PRODUCTION
fn run<const N: usize>() {
    for count in 0..=128 {
        LANES.with_borrow_mut(|ls| *ls=vec![Lane{origin:0,calls:vec![]}]);
        CALLS.with_borrow_mut(|cs| cs.clear());
        let mut out = (0..count).map(|j| [j;N]).collect::<Vec<_>>();
        fors_leaves_active(&STATE,&[57;N], Adrs{typ:77,keypair:97}, Base(0),&mut out);
        assert!(out.iter().all(|row| row == &[usize::MAX;N]));
    }
}
fn main() { run::<16>(); run::<24>(); run::<32>(); }
