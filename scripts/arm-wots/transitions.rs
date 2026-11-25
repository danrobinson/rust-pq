// Each token denotes an arbitrary entry register. Counter updates retain their
// provenance; decisions about a remaining count are supplied by the live mask.
#[derive(Clone, Copy)]
struct Counter {
    lane: usize,
    updates: usize,
    live: bool,
}
impl std::ops::SubAssign<u32> for Counter {
    fn sub_assign(&mut self, n: u32) {
        self.updates += n as usize;
    }
}
impl std::ops::AddAssign<u32> for Counter {
    fn add_assign(&mut self, n: u32) {
        self.updates += n as usize;
    }
}
impl PartialEq<u32> for Counter {
    fn eq(&self, n: &u32) -> bool {
        assert_eq!(*n, 0);
        !self.live
    }
}
impl PartialOrd<u32> for Counter {
    fn partial_cmp(&self, n: &u32) -> Option<std::cmp::Ordering> {
        assert_eq!(*n, 0);
        Some(if self.live {
            std::cmp::Ordering::Greater
        } else {
            std::cmp::Ordering::Equal
        })
    }
}
#[derive(Clone, Copy)]
struct Reg(usize);
#[derive(Clone, Copy)]
struct Chain(usize);
struct Store<'a> {
    events: &'a mut Vec<(usize, usize, usize, usize)>,
}
#[derive(Clone, Copy)]
struct Offset {
    chain: usize,
    stride: usize,
}
impl std::ops::Mul<usize> for Chain {
    type Output = Offset;
    fn mul(self, n: usize) -> Offset {
        Offset {
            chain: self.0,
            stride: n,
        }
    }
}
struct Address<'a> {
    events: &'a mut Vec<(usize, usize, usize, usize)>,
    off: Offset,
}
impl Store<'_> {
    fn at(&mut self, off: Offset) -> Address<'_> {
        Address {
            events: self.events,
            off,
        }
    }
}
unsafe fn store_n<const N: usize>(dst: Address<'_>, x: Reg, xb: Reg) {
    assert_eq!(dst.off.stride, N);
    dst.events.push((dst.off.chain, dst.off.stride, x.0, xb.0));
}
fn step<const N: usize>(tail: bool, count: usize, mask: usize, phases: usize) {
    let mut events = vec![];
    let mut sig = Store {
        events: &mut events,
    };
    let mut active = count;
    let mut x = std::array::from_fn::<_, 4, _>(Reg);
    let mut xb = std::array::from_fn::<_, 4, _>(|l| Reg(l + 4));
    let mut heads = std::array::from_fn::<_, 4, _>(|l| Reg(l + 8));
    let hash_head = Reg(12);
    let mut chain = std::array::from_fn::<_, 4, _>(Chain);
    let mut left = std::array::from_fn::<_, 4, _>(|lane| Counter {
        lane,
        updates: 0,
        live: mask & (1 << lane) != 0,
    });
    let mut cur_t = std::array::from_fn::<_, 4, _>(|lane| Counter {
        lane,
        updates: 0,
        live: false,
    });
    let mut is_prf = std::array::from_fn::<_, 4, _>(|lane| phases & (1 << lane) != 0);
    if tail {
        // TAIL
    } else {
        // COMPACTION
    }
    print!("{count} {mask} {phases}|");
    for l in 0..active {
        print!(
            "{},{},{},{},{},{},{},{},{};",
            x[l].0,
            xb[l].0,
            heads[l].0,
            chain[l].0,
            cur_t[l].lane,
            cur_t[l].updates,
            left[l].lane,
            left[l].updates,
            usize::from(is_prf[l])
        );
    }
    print!("|");
    for (c, n, x, xb) in events {
        print!("{c},{n},{x},{xb};");
    }
    println!();
}
fn run<const N: usize>() {
    for count in 1..=4 {
        for mask in 0..1 << count {
            for phases in 0..1 << count {
                step::<N>(count < 4, count, mask, phases);
            }
        }
    }
}
fn main() {
    run::<16>();
    run::<24>();
    run::<32>();
}
