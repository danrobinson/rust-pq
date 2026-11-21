//! Parameter sets (FIPS 205, Table 2).
//!
//! One `Params` value describes a parameter set. All six SHA-2 sets use
//! `lg_w = 4`, so the Winternitz parameters are constants.

/// Winternitz parameter, log2. The same for every parameter set of FIPS 205.
pub const LG_W: u32 = 4;
/// Winternitz parameter w = 2^LG_W.
pub const W: u32 = 16;
/// WOTS+ checksum chains (FIPS 205 §5: `len_2 = 3` when `lg_w = 4`).
pub const LEN2: usize = 3;

/// A row of FIPS 205 Table 2.
pub struct Params {
    /// Security parameter: hash output length in bytes.
    pub n: usize,
    /// Total hypertree height.
    pub h: u32,
    /// Number of hypertree layers.
    pub d: u32,
    /// Height of each XMSS tree (h' = h / d).
    pub hp: u32,
    /// FORS tree height.
    pub a: u32,
    /// Number of FORS trees.
    pub k: u32,
    /// Message digest length in bytes.
    pub m: usize,
}

pub const SHA2_128S: Params = Params { n: 16, h: 63, d: 7, hp: 9, a: 12, k: 14, m: 30 };
pub const SHA2_128F: Params = Params { n: 16, h: 66, d: 22, hp: 3, a: 6, k: 33, m: 34 };
pub const SHA2_192S: Params = Params { n: 24, h: 63, d: 7, hp: 9, a: 14, k: 17, m: 39 };
pub const SHA2_192F: Params = Params { n: 24, h: 66, d: 22, hp: 3, a: 8, k: 33, m: 42 };
pub const SHA2_256S: Params = Params { n: 32, h: 64, d: 8, hp: 8, a: 14, k: 22, m: 47 };
pub const SHA2_256F: Params = Params { n: 32, h: 68, d: 17, hp: 4, a: 9, k: 35, m: 49 };

impl Params {
    /// WOTS+ message chains: `len_1 = 2n` when `lg_w = 4`.
    pub fn len1(&self) -> usize {
        2 * self.n
    }

    /// WOTS+ chains in total: `len = len_1 + len_2`.
    pub fn len(&self) -> usize {
        2 * self.n + LEN2
    }

    /// Bytes of the digest used for FORS: ceil(k*a/8).
    pub fn md_bytes(&self) -> usize {
        ((self.k * self.a + 7) / 8) as usize
    }

    /// Bits of the tree index: h - h/d.
    pub fn tree_bits(&self) -> u32 {
        self.h - self.hp
    }

    /// Bytes of the digest used for the tree index: ceil((h - h/d)/8).
    pub fn tree_bytes(&self) -> usize {
        ((self.h - self.hp + 7) / 8) as usize
    }

    /// Bytes of the digest used for the leaf index: ceil(h/(8d)).
    pub fn leaf_bytes(&self) -> usize {
        ((self.hp + 7) / 8) as usize
    }

    /// Bytes of one XMSS signature: (len + h') * n.
    pub fn xmss_sig_bytes(&self) -> usize {
        (self.len() + self.hp as usize) * self.n
    }

    /// Bytes of a FORS signature: k * (1 + a) * n.
    pub fn fors_sig_bytes(&self) -> usize {
        (self.k * (1 + self.a)) as usize * self.n
    }

    /// Bytes of a signature: n + FORS + d XMSS signatures.
    pub fn sig_bytes(&self) -> usize {
        self.n + self.fors_sig_bytes() + self.d as usize * self.xmss_sig_bytes()
    }
}
