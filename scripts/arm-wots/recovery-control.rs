// A tag records a register's source. Only the counter domain observes the
// predicate that controls eviction. Its arithmetic retains symbolic operands.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct Count {
    origin: usize,
    base: i32,
    update: i32,
    positive: bool,
}
impl std::ops::AddAssign<i32> for Count {
    fn add_assign(&mut self, k: i32) { self.update += k; }
}
impl std::ops::SubAssign<i32> for Count {
    fn sub_assign(&mut self, k: i32) { self.update -= k; }
}
impl std::ops::Sub<Count> for i32 {
    type Output = Count;
    fn sub(self, d: Count) -> Count {
        assert_eq!(self, 15);
        assert_eq!(d.base, 1);
        Count { base: -1, ..d }
    }
}
impl PartialEq<i32> for Count {
    fn eq(&self, k: &i32) -> bool { assert_eq!(*k, 0); !self.positive }
}
impl PartialOrd<i32> for Count {
    fn partial_cmp(&self, k: &i32) -> Option<std::cmp::Ordering> {
        assert_eq!(*k, 0);
        Some(if self.positive {std::cmp::Ordering::Greater} else {std::cmp::Ordering::Equal})
    }
}
unsafe fn load_n<const N:usize>(src: &[u32]) -> (u32,u32) {
    assert!(src.len()>=N);
    (src[0],src[N-1])
}
unsafe fn store_n<const N:usize>(buf: &mut [u32], lo: u32, hi: u32) {
    // A source range mismatch is visible in the traces, including its offset,
    // stride, lane order and high-register provenance.
    assert!(buf.len()>=N);
    let offset = 22+67*N-buf.len();
    print!("{offset},{lo},{hi};");
}
fn run<const N:usize>(count:usize, mask:usize, q:usize) {
    const CHAINS:[usize;8] = [61,3,47,8,56,23,0,64];
    let mut x = std::array::from_fn::<_,4,_>(|i| 100+i as u32);
    let mut xb = std::array::from_fn::<_,4,_>(|i| 200+i as u32);
    let mut chain = std::array::from_fn::<_,4,_>(|i|CHAINS[i]);
    let mut cur_t = std::array::from_fn::<_,4,_>(|i| Count{origin:i,base:2,update:0,positive:false});
    let mut left = std::array::from_fn::<_,4,_>(|i| Count{origin:i,base:3,update:0,positive:mask & (1<<i)!=0});
    let digits = std::array::from_fn::<_,67,_>(|c| Count{
        origin:CHAINS.iter().position(|&x|x==c).unwrap_or(9),base:1,update:0,positive:true,
    });
    let mut sig=vec![u32::MAX;67*N];
    for (origin,&c) in CHAINS.iter().enumerate() {
        sig[c*N]=100+origin as u32;
        sig[(c+1)*N-1]=200+origin as u32;
    }
    let order=CHAINS.map(|x| x as u8);
    let mut active=count;
    let mut next=4;
    let total=4+q;
    let mut buf=vec![0;22+67*N];
    let min_left=32; // symbol for the full hot step size; 1 denotes a tail step
    print!("{N},{count},{mask},{q}|");
    if count==4 {
        // HOT
    } else {
        // TAIL
    }
    print!("|{}|",next-4);
    for i in 0..active {
        let c=CHAINS.iter().position(|&z|z==chain[i]).unwrap();
        assert_eq!((x[i],xb[i]),(100+c as u32,200+c as u32));
        let magnitude=if count==4 {min_left} else {1};
        assert_eq!((cur_t[i].origin,cur_t[i].base,cur_t[i].update),(c,if c<4{2}else{1},if c<4{magnitude}else{0}));
        assert_eq!((left[i].origin,left[i].base,left[i].update),(c,if c<4{3}else{-1},if c<4{-magnitude}else{0}));
        assert!(left[i].positive);
        print!("{c};");
    }
    println!();
}
fn probe<const N:usize>() {
    for a in 1..=4 {
        for mask in 0..1<<a {
            for q in 0..=if a==4 {4} else {0} { run::<N>(a,mask,q); }
        }
    }
}
fn main() { probe::<16>(); probe::<24>(); probe::<32>(); }
