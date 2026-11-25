// Distinct byte origins can be assigned arbitrary independent values after replay.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum Byte { Input(usize), Node(usize,usize,usize), Address(usize), Literal(u8), Output(usize) }
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
struct Index { tree:usize, height:usize, descents:usize }
impl Index {
    fn parent(self)->Self { Self {descents:self.descents+1,..self} }
}
const EMPTY:Index=Index{tree:usize::MAX,height:0,descents:0};
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum Word { Input, Zero, Height(u32), Position(Index) }
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
struct Adrs { typ:Word, keypair:Word, w2:Word, w3:Word }
const ADR:Adrs=Adrs{typ:Word::Input,keypair:Word::Input,w2:Word::Input,w3:Word::Input};
impl Adrs {
    fn with_type(self,typ:u32)->Self { Self {typ:Word::Height(typ),keypair:Word::Zero,w2:Word::Zero,w3:Word::Zero} }
    fn with_keypair(self,keypair:Word)->Self { Self {keypair,..self} }
    fn with_word2(self,h:u32)->Self { Self {w2:Word::Height(h),..self} }
    fn with_word3(self,i:Index)->Self { Self {w3:Word::Position(i),..self} }
    fn compress(self)->[Byte;22] {
        assert_eq!(self,Adrs{typ:Word::Height(FORS_ROOTS),keypair:ADR.keypair,w2:Word::Zero,w3:Word::Zero});
        std::array::from_fn(Byte::Address)
    }
}
const FORS_ROOTS:u32=4;
const K_MAX:usize=35;
struct Params{a:u32,k:u32}
#[derive(Clone,Copy,Debug,PartialEq,Eq)] enum State { Sha256, Sha512(usize) }
struct Seed<const N:usize> { state:State,state512:State }
#[derive(Clone,Copy)] struct Geometry { n:usize, k:usize, a:usize, pairs:bool, multi:bool, odd:bool }
use std::cell::Cell;
thread_local! {
  static TRACE:std::cell::RefCell<Vec<(usize,usize,usize)>>=const{std::cell::RefCell::new(Vec::new())};
  static PROGRAM:Cell<Geometry>=const { Cell::new(Geometry{n:0,k:0,a:0,pairs:false,multi:false,odd:false}) };
}
fn record(op:usize,a:usize,b:usize){TRACE.with_borrow_mut(|trace|trace.push((op,a,b)));}
fn geo()->Geometry{ PROGRAM.with(Cell::get) }
fn index(tree:usize,descents:usize)->Index { Index{tree,height:geo().a,descents} }
fn base_2b_stack(md:&[Byte],a:u32,k:usize)->[usize;35] {
    assert_eq!(md,[Byte::Input(usize::MAX)]);
    assert_eq!((a as usize,k),(geo().a,geo().k));
    std::array::from_fn(|i|i)
}
// Refined in Lean by absolute_indices on the exact extracted Rust loop.
fn absolute(tree:usize,height:u32,digit:usize)->Index {
    assert_eq!((tree,height as usize),(digit,geo().a)); index(tree,0)
}
fn sibling<const N:usize>(row:usize,level:usize)->[Byte;N] {
    std::array::from_fn(|b|Byte::Input((row*(geo().a+1)+1+level)*N+b))
}
fn node<const N:usize>(row:usize,level:usize)->[Byte;N] {
    std::array::from_fn(|b|Byte::Node(row,level,b))
}
fn block<const N:usize>(sig:&[Byte],offset:usize)->[Byte;N] { sig[offset*N..(offset+1)*N].try_into().unwrap() }
fn check_level<const N:usize>(indices:&[Index],values:&[[Byte;N]],height:usize,h:usize) {
    let g=geo();assert_eq!((indices.len(),values.len(),height),(g.k,g.k,g.a));
    for t in 0..g.k { assert_eq!(indices[t],index(t,h)); assert_eq!(values[t],node(t,h)); }
}
fn check_sig(sig:&[Byte]) {
    assert_eq!(sig.len(),geo().n*geo().k*(geo().a+1));
    for (i,b) in sig.iter().enumerate(){ assert_eq!(*b,Byte::Input(i)); }
}
fn compress_block(st:State,input:&[Byte],start:usize) {
    let g=geo(); let size=22+g.k*g.n;
    let block=if g.n==16 {64}else{128};
    let total=(size+1+block/8+block-1)/block*block;
    assert!(start+input.len()<=total);
    assert_eq!(st,if g.n==16 { State::Sha256 } else { State::Sha512(start) });
    let length=((block+size)*8).to_be_bytes();
    for (j,b) in input.iter().enumerate() {
        let i=start+j;
        let expected=if i<22 {Byte::Address(i)} else if i<size {
            Byte::Node((i-22)/g.n,g.a,(i-22)%g.n)
        } else if i==size {Byte::Literal(128)} else if i>=total-8 {
            Byte::Literal(length[i-(total-8)])
        } else {Byte::Literal(0)};
        assert_eq!(*b,expected);
    }
}
fn check_total(total:usize) {
    let g=geo(); let b=if g.n==16 {64}else{128};
    assert_eq!(total,(22+g.n*g.k+1+b/8+b-1)/b*b);
}
mod arm_wide {
    use super::*;
    pub(super) fn fors_verify_leaves<const N:usize>(st:&State,adrs:Adrs,sig:&[Byte],idx:&[Index],val:&mut [[Byte;N]],a:usize) {
        record(0,0,0); check_sig(sig); assert_eq!((*st,adrs,idx.len(),val.len(),a,N),(State::Sha256,ADR,geo().k,geo().k,geo().a,geo().n));
        for i in 0..geo().k { assert_eq!(idx[i],index(i,0)); val[i]=node(i,0); }
    }
    pub(super) fn fors_path_level_16(st:&State,adrs:Adrs,sig:&[Byte],idx:&mut [Index],val:&mut [[Byte;16]],a:usize,h:usize) {
        record(1,h,idx.len()); check_sig(sig); assert_eq!((*st,adrs),(State::Sha256,ADR)); check_level(idx,val,a,h);
        for i in 0..val.len(){idx[i]=idx[i].parent();val[i]=node(i,h+1);}
    }
    pub(super) fn compress_multi_1(st:&State,buf:&[Byte])->[Byte;16] {
        record(4,buf.len(),0); check_total(buf.len());compress_block(*st,buf,0);std::array::from_fn(Byte::Output)
    }
}
mod sha512 {
    use super::*;
    pub(super) fn compress(st:&State,buf:&[Byte],off:usize)->State {
        record(6,off,128); compress_block(*st,&buf[off..off+128],off);State::Sha512(off+128)
    }
    pub(super) mod paired {
        use super::*;
        pub(crate) fn path_parents_batch<const N:usize>(st:&State,adr:Adrs,val:&mut [[Byte;N]],idx:&mut [Index],sig:&[Byte],a:usize,h:usize)->usize {
            check_sig(sig);assert_eq!((*st,adr),(State::Sha512(0),ADR.with_word2(h as u32+1)));check_level(idx,val,a,h);
            let done=if geo().pairs {geo().k/2*2}else{0};
            record(2,h,done); for i in 0..done {idx[i]=idx[i].parent();val[i]=node(i,h+1);}
            done
        }
        pub(crate) fn compress_multi_1<const N:usize>(st:&State,buf:&[Byte])->Option<[Byte;N]> {
            record(5,buf.len(),0); check_total(buf.len());compress_block(*st,buf,0);geo().multi.then(||std::array::from_fn(Byte::Output))
        }
    }
}
fn thash_pair<const N:usize>(seed:&Seed<N>,adrs:&Adrs,left:&[Byte;N],right:&[Byte;N])->[Byte;N] {
    assert_eq!((seed.state,seed.state512),(State::Sha256,State::Sha512(0)));
    let Word::Position(p)=adrs.w3 else{panic!("missing tree position")};
    assert!(p.descents>0);
    let level=p.descents-1;
    record(3,level,p.tree);
    assert_eq!(*adrs,ADR.with_word2(p.descents as u32).with_word3(index(p.tree,p.descents)));
    let (old,sib)=if geo().odd { (right,left) } else { (left,right) };
    assert_eq!(*old,node(p.tree,level)); assert_eq!(*sib,sibling(p.tree,level));
    node(p.tree,p.descents)
}
mod hash {
    use super::*;
    pub(super) fn trunc512<const N:usize>(st:&State)->[Byte;N] {
        let State::Sha512(len)=*st else{panic!("wrong final state")};
        record(7,len,0); check_total(len);std::array::from_fn(Byte::Output)
    }
}
mod native {
    use super::*;
    // PRODUCTION
}
fn run<const N:usize>(k:usize,a:usize,pairs:bool,multi:bool,odd:bool) {
    PROGRAM.with(|p|p.set(Geometry{n:N,k,a,pairs,multi,odd}));
    let sig=(0..k*(a+1)*N).map(Byte::Input).collect::<Vec<_>>();
    let seed=Seed{state:State::Sha256,state512:State::Sha512(0)};
    let out=native::pk_from_sig::<N>(&Params{a:a as u32,k:k as u32},&sig,&[Byte::Input(usize::MAX)],&seed,ADR);
    assert_eq!(out,std::array::from_fn(Byte::Output));
    TRACE.with_borrow_mut(|t|{println!("{}",t.iter().map(|(op,a,b)|format!("{op} {a} {b}")).collect::<Vec<_>>().join(",")); t.clear()});
}
fn main(){
    for pairs in [false,true]{for multi in [false,true]{for parity in [false,true]{
        run::<16>(14,12,pairs,multi,parity);run::<16>(33,6,pairs,multi,parity);
        run::<24>(17,14,pairs,multi,parity);run::<24>(33,8,pairs,multi,parity);
        run::<32>(22,14,pairs,multi,parity);run::<32>(35,9,pairs,multi,parity);
    }}}
}
