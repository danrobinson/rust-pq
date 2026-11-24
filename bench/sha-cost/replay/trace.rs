use crate::{address::Adrs, params::Params};
use native::hash;
use std::{cell::RefCell, collections::HashMap};

pub struct Lane {
    pub template: [u8; 64],
    pub left: usize,
    pub right: Option<usize>,
    pub start: u32,
    pub end: u32,
}
pub enum Kind {
    Short,
    Pair,
    Many,
    Endpoints,
}
pub enum Op {
    Seed(usize),
    Chains {
        lanes: Vec<Lane>,
        out: usize,
    },
    Hash {
        addr: Adrs,
        ids: Vec<usize>,
        kind: Kind,
        out: usize,
    },
    Random(usize, usize, Vec<u8>, usize),
    Message(usize, usize, usize, Vec<u8>),
}
#[derive(Default)]
pub struct Trace {
    lookup: HashMap<Vec<u8>, usize>,
    pub values: Vec<Vec<u8>>,
    pub literals: usize,
    pub ops: Vec<Op>,
    pub digest: Vec<u8>,
}
thread_local! {static TRACE:RefCell<Trace>=RefCell::default();}
pub fn capture<T>(f: impl FnOnce(&mut Trace) -> T) -> T {
    TRACE.with(|t| f(&mut t.borrow_mut()))
}
impl Trace {
    pub fn id(&self, v: &[u8]) -> usize {
        *self.lookup.get(v).expect("unbound computed digest")
    }
    pub fn output(&mut self, v: &[u8]) -> usize {
        let id = self.values.len();
        self.lookup.insert(v.to_vec(), id);
        self.values.push(v.to_vec());
        id
    }
    pub fn literal(&mut self, v: &[u8]) {
        if !self.lookup.contains_key(v) {
            self.output(v);
        }
        self.literals = self.values.len();
    }
    /// Only original operation inputs may initialize the timed replay.
    pub fn memory<const N: usize>(&self) -> Vec<[u8; N]> {
        let mut v = vec![[0; N]; self.values.len()];
        for (dst, src) in v.iter_mut().zip(&self.values[..self.literals]) {
            dst.copy_from_slice(src);
        }
        v
    }
    pub fn check<const N: usize>(&self, v: &[[u8; N]], digest: &[u8]) {
        assert_eq!(v.len(), self.values.len());
        assert_eq!(digest, self.digest);
        for (out, want) in v.iter().zip(&self.values) {
            assert_eq!(out.as_slice(), want);
        }
    }
    pub fn replay<const N: usize, const FULL: bool>(
        &self,
        p: &Params,
        v: &mut [[u8; N]],
    ) -> Vec<u8> {
        // Every trace contains exactly one seed setup. Do not precompute it outside the timer.
        let mut seed = None;
        let mut md = Vec::new();
        let mut blocks = [[0; 64]; 128];
        let mut starts = [0; 128];
        let mut ends = [0; 128];
        let mut bytes = Vec::new();
        for op in &self.ops {
            match op {
                Op::Seed(i) => seed = Some(hash::seed_ctx(&v[*i])),
                Op::Random(k, r, m, o) => v[*o] = hash::prf_msg(&v[*k], &v[*r], m),
                Op::Message(r, k, root, m) => md = hash::h_msg(p, &v[*r], &v[*k], &v[*root], m),
                Op::Chains { lanes, out } => {
                    let state = &seed.as_ref().unwrap().state;
                    let b = &mut blocks[..lanes.len()];
                    for (i, l) in lanes.iter().enumerate() {
                        b[i] = l.template;
                        b[i][22..22 + N].copy_from_slice(&v[l.left]);
                        if let Some(j) = l.right {
                            b[i][22 + N..22 + 2 * N].copy_from_slice(&v[j]);
                        }
                        starts[i] = l.start;
                        ends[i] = l.end;
                    }
                    if FULL {
                        full::hash::chain_blocks::<N>(state, b, &starts, &ends);
                    } else {
                        hash::chain_blocks::<N>(state, b, &starts, &ends);
                    }
                    for (i, block) in b.iter().enumerate() {
                        v[out + i].copy_from_slice(&block[22..22 + N]);
                    }
                }
                Op::Hash {
                    addr,
                    ids,
                    kind,
                    out,
                } => {
                    let seed = seed.as_ref().unwrap();
                    v[*out] = match kind {
                        Kind::Short => hash::thash_short(seed, addr, &v[ids[0]]),
                        Kind::Pair => hash::thash_pair(seed, addr, &v[ids[0]], &v[ids[1]]),
                        Kind::Many => {
                            bytes.clear();
                            for i in ids {
                                bytes.extend_from_slice(&v[*i]);
                            }
                            hash::thash(seed, addr, &bytes)
                        }
                        Kind::Endpoints => {
                            for (b, i) in blocks.iter_mut().zip(ids) {
                                b[22..22 + N].copy_from_slice(&v[*i]);
                            }
                            hash::thash_values(seed, addr, &blocks[..ids.len()])
                        }
                    }
                }
            }
        }
        md
    }
}
