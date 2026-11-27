// Shared symbolic data types from transitions.rs are prepended by the lifter.
#[derive(Clone, Copy)]
struct Cursor(usize);
struct Limit(bool);
impl std::ops::AddAssign<usize> for Cursor {
    fn add_assign(&mut self, k: usize) {
        self.0 += k;
    }
}
impl PartialEq<Limit> for Cursor {
    fn eq(&self, _: &Limit) -> bool {
        panic!("unexpected queue equality")
    }
}
impl PartialOrd<Limit> for Cursor {
    fn partial_cmp(&self, b: &Limit) -> Option<std::cmp::Ordering> {
        assert_eq!(self.0, 0);
        Some(if b.0 {
            std::cmp::Ordering::Less
        } else {
            std::cmp::Ordering::Equal
        })
    }
}
struct Digits([Counter; 5]);
impl std::ops::Index<Chain> for Digits {
    type Output = Counter;
    fn index(&self, i: Chain) -> &Counter {
        &self.0[i.0]
    }
}
impl std::ops::Add<Counter> for u32 {
    type Output = Counter;
    fn add(self, mut v: Counter) -> Counter {
        v.updates += self as usize;
        v
    }
}
struct Order;
impl Order {
    fn read(&self, c: Cursor) -> Chain {
        assert_eq!(c.0, 0);
        Chain(4)
    }
}
#[derive(Clone, Copy)]
struct Delta;
impl std::ops::SubAssign<Delta> for Counter {
    fn sub_assign(&mut self, _: Delta) {
        self.updates += 1024
    }
}
impl std::ops::AddAssign<Delta> for Counter {
    fn add_assign(&mut self, _: Delta) {
        self.updates += 1024
    }
}
fn run<const N: usize>(shared: bool, live: bool, phase: bool, more: bool, l: usize) {
    let mut events = vec![];
    let mut sig = Store {
        events: &mut events,
    };
    let sk_x = Reg(13);
    let sk_xb = Reg(14);
    let prf_head = Reg(15);
    let hash_head = Reg(12);
    let mut x = std::array::from_fn::<_, 4, _>(Reg);
    let mut xb = std::array::from_fn::<_, 4, _>(|j| Reg(j + 4));
    let mut heads = std::array::from_fn::<_, 4, _>(|j| Reg(j + 8));
    let mut chain = std::array::from_fn::<_, 4, _>(Chain);
    let mut cur_t = std::array::from_fn::<_, 4, _>(|lane| Counter {
        lane,
        updates: 0,
        live: false,
    });
    let mut left = std::array::from_fn::<_, 4, _>(|lane| Counter {
        lane,
        updates: 0,
        live,
    });
    let mut is_prf = [phase; 4];
    let digits = Digits(std::array::from_fn(|j| Counter {
        lane: j + 5,
        updates: 0,
        live: true,
    }));
    let mut next = Cursor(0);
    let len = Limit(more);
    let order = Order;
    let min_left = Delta;
    if shared {
        // SHARED_POST
    } else {
        // MIXED_POST
    }
    for j in 0..4 {
        if j != l {
            assert_eq!(
                (
                    x[j].0,
                    xb[j].0,
                    heads[j].0,
                    chain[j].0,
                    cur_t[j].lane,
                    cur_t[j].updates,
                    left[j].lane,
                    left[j].updates,
                    is_prf[j]
                ),
                (j, j + 4, j + 8, j, j, 0, j, 0, phase)
            );
        }
    }
    print!(
        "{} {} {} {} {}|{}|",
        usize::from(shared),
        usize::from(live),
        usize::from(phase),
        usize::from(more),
        l,
        next.0
    );
    print!(
        "{},{},{},{},{},{},{},{},{}|",
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
    for (c, n, x, xb) in events {
        assert_eq!(n, N);
        print!("{c},{x},{xb};");
    }
    println!();
}
fn width<const N: usize>() {
    for shared in [false, true] {
        for live in [false, true] {
            for phase in [false, true] {
                for more in [false, true] {
                    for l in 0..4 {
                        run::<N>(shared, live, phase, more, l);
                    }
                }
            }
        }
    }
}
fn main() {
    width::<16>();
    width::<24>();
    width::<32>();
}
