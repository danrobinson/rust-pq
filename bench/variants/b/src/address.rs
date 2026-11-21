//! Hash addresses (FIPS 205 §4.2), kept as fields and serialised in the
//! 22-byte compressed form used by the SHA2 parameter sets (§11.2).

pub const WOTS_HASH: u32 = 0;
pub const WOTS_PK: u32 = 1;
pub const TREE: u32 = 2;
pub const FORS_TREE: u32 = 3;
pub const FORS_ROOTS: u32 = 4;
pub const WOTS_PRF: u32 = 5;
pub const FORS_PRF: u32 = 6;

#[derive(Clone, Copy)]
pub struct Adrs {
    /// Layer address.
    pub layer: u32,
    /// Tree address. FIPS 205 allots 12 bytes; every parameter set uses at
    /// most 8, and the compressed form keeps only those 8.
    pub tree: u64,
    /// Address type.
    pub typ: u32,
    /// Word 1: key pair address.
    pub keypair: u32,
    /// Word 2: chain address or tree height.
    pub word2: u32,
    /// Word 3: hash address or tree index.
    pub word3: u32,
}

impl Adrs {
    pub fn new() -> Adrs {
        Adrs { layer: 0, tree: 0, typ: 0, keypair: 0, word2: 0, word3: 0 }
    }

    /// `setTypeAndClear`.
    pub fn with_type(self, typ: u32) -> Adrs {
        Adrs { layer: self.layer, tree: self.tree, typ, keypair: 0, word2: 0, word3: 0 }
    }

    pub fn with_layer(self, layer: u32) -> Adrs {
        Adrs { layer, ..self }
    }

    pub fn with_tree(self, tree: u64) -> Adrs {
        Adrs { tree, ..self }
    }

    pub fn with_keypair(self, keypair: u32) -> Adrs {
        Adrs { keypair, ..self }
    }

    /// `setChainAddress` / `setTreeHeight`.
    pub fn with_word2(self, word2: u32) -> Adrs {
        Adrs { word2, ..self }
    }

    /// `setHashAddress` / `setTreeIndex`.
    pub fn with_word3(self, word3: u32) -> Adrs {
        Adrs { word3, ..self }
    }

    /// The compressed address ADRSc: layer (1) ‖ tree (8) ‖ type (1) ‖ words (12).
    pub fn compress(&self) -> [u8; 22] {
        let t = self.tree;
        let a = self.keypair;
        let b = self.word2;
        let c = self.word3;
        [
            self.layer as u8,
            (t >> 56) as u8,
            (t >> 48) as u8,
            (t >> 40) as u8,
            (t >> 32) as u8,
            (t >> 24) as u8,
            (t >> 16) as u8,
            (t >> 8) as u8,
            t as u8,
            self.typ as u8,
            (a >> 24) as u8,
            (a >> 16) as u8,
            (a >> 8) as u8,
            a as u8,
            (b >> 24) as u8,
            (b >> 16) as u8,
            (b >> 8) as u8,
            b as u8,
            (c >> 24) as u8,
            (c >> 16) as u8,
            (c >> 8) as u8,
            c as u8,
        ]
    }
}
