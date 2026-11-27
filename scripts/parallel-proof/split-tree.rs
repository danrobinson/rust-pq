// A node denotes a formal call of FIPS 205 Algorithm 9 or 15. Absolute
// indices are affine in the arbitrary root index supplied by the caller.
use std::ops::{Add, Shl};
use std::sync::OnceLock;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct Index {
    scale: u64,
    offset: u64,
}
impl Shl<u32> for Index {
    type Output = Self;
    fn shl(self, shift: u32) -> Self {
        Self {
            scale: self.scale << shift,
            offset: self.offset << shift,
        }
    }
}
impl Add<u32> for Index {
    type Output = Self;
    fn add(self, n: u32) -> Self {
        Self {
            offset: self.offset + u64::from(n),
            ..self
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct Node {
    height: u32,
    index: Index,
}
type Adrs = Node;
impl Node {
    fn with_word2(self, height: u32) -> Self {
        Self { height, ..self }
    }
    fn with_word3(self, index: Index) -> Self {
        Self { index, ..self }
    }
}
struct Seed<const N: usize>;
fn hash2<const N: usize>(_: &Seed<N>, parent: &Adrs, left: &Node, right: &Node) -> Node {
    let child = Node {
        height: parent.height.checked_sub(1).unwrap(),
        index: parent.index << 1,
    };
    assert_eq!(*left, child);
    assert_eq!(
        *right,
        Node {
            index: child.index + 1,
            ..child
        }
    );
    *parent
}

// PRODUCTION

fn main() {
    let root = Index {
        scale: 1,
        offset: 0,
    };
    for height in 0..=14 {
        for sub in 0..=height {
            let slots: Vec<_> = (0..1u32 << (height - sub))
                .map(|j| {
                    OnceLock::from(Node {
                        height: sub,
                        index: (root << (height - sub)) + j,
                    })
                })
                .collect();
            let address = Node {
                height: u32::MAX,
                index: Index {
                    scale: 0,
                    offset: u64::MAX,
                },
            };
            let result = reduce_tree(&slots, &Seed::<16>, address, root, sub, height);
            assert_eq!(
                result,
                Node {
                    height,
                    index: root
                }
            );
        }
    }
}
