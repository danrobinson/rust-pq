// The source gate inserts the production FORS queue builder and its exact record types above this observer.
fn check<const WIDTH: usize>(a:u32,k:usize,simd:bool) {
    let choices=(0..k).map(|t| ((t as u32)*6143+111) % (1<<a)).collect::<Vec<_>>();
    let (jobs,meta,size)=build::<WIDTH>(a,k,simd,&choices);
    let stride=a as usize+1;
    let mut cells=vec![None;k*stride];
    let mut chunks=vec![None;size];
    let mut put=|t:usize,c:usize,who:(u8,usize,usize,usize)| {
        assert!(cells[t*stride+c].replace(who).is_none(),"two producers for one field");
    };
    for job in jobs {
        match job.kind {
            WorkKind::ForsTreeLow {tree,low_h} => {
                for c in 0..=low_h as usize {put(tree as usize,c,(0,tree as usize,0,c))}
            }
            WorkKind::ForsShakeLow {first,active,low_h} => {
                assert_eq!(active as usize,(k-first as usize).min(WIDTH));
                for l in 0..active as usize {for c in 0..=low_h as usize {put(first as usize+l,c,(0,first as usize,l,c))}}
            }
            WorkKind::ForsNodeDirect {idx,height,slot} => {
                let (t,c)=(slot/stride,slot%stride);
                assert_eq!(c,height as usize+1);
                assert_eq!(idx,((t as u32)<<(a-height))+((choices[t]>>height)^1));
                put(t,c,(1,t,0,height as usize));
            }
            WorkKind::ForsShakeDirect {first,active,height} => {
                assert_eq!(active as usize,(k-first as usize).min(WIDTH));
                for l in 0..active as usize {put(first as usize+l,height as usize+1,(1,first as usize,l,height as usize));}
            }
            WorkKind::ForsNodeSplit {idx,height,slot} => {assert!(chunks[slot].replace((idx,height)).is_none());}
            WorkKind::ForsShakeSplit {first,active,height,sub_h,chunk,split_base,chunks:n} => {
                assert_eq!(active as usize,(k-first as usize).min(WIDTH));
                assert_eq!(n,1<<(height-sub_h));
                for l in 0..active as usize {
                    let tree=first as usize+l;
                    let root=((tree as u32)<<(a-height as u32))+((choices[tree]>>height)^1);
                    let pos=split_base+l*n+chunk as usize;
                    assert!(chunks[pos].replace(((root<<(height-sub_h))+chunk,sub_h as u32)).is_none());
                }
            }
            _ => panic!("unexpected job in FORS queue")
        }
    }
    for m in meta {
        let t=m.tree as usize;
        let h=m.height;
        let expected=((t as u32)<<(a-h))+((choices[t]>>h)^1);
        assert_eq!(expected,m.root_idx);
        assert_eq!(m.chunks,1<<(h-m.sub_h));
        for c in 0..m.chunks {
            let item=chunks[m.slot_start+c].take().expect("split input missing or read twice");
            assert_eq!(item,((expected<<(h-m.sub_h))+c as u32,m.sub_h));
        }
        put(t,h as usize+1,(2,t,0,h as usize));
    }
    assert!(chunks.iter().all(Option::is_none),"unconsumed split field");
    for cell in cells {let (tag,first,lane,col)=cell.expect("unowned final slot");println!("{tag} {first} {lane} {col}");}
}
fn main(){
    let args:Vec<_>=std::env::args().skip(1).map(|a|a.parse::<usize>().unwrap()).collect();
    for pair in args.chunks_exact(2) {
        let (a,k)=(pair[0] as u32,pair[1]);
        check::<3>(a,k,false);check::<3>(a,k,true);check::<8>(a,k,true);
    }
}
