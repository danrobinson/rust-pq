//! SHAKE256, the byte-oriented sponge of FIPS 202 §§5–6 with a 1088-bit rate.
//! Lanes use the index x + 5*y. Within a lane, byte zero is least significant.

const RATE: usize = 136;
const RC: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

fn round(a: &[u64; 25], rc: u64) -> [u64; 25] {
    let mut parity = [0u64; 5];
    let mut x = 0;
    while x < 5 {
        parity[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
        x += 1;
    }
    let mut d = [0u64; 5];
    let mut x = 0;
    while x < 5 {
        d[x] = parity[(x + 4) % 5] ^ parity[(x + 1) % 5].rotate_left(1);
        x += 1;
    }

    // Rho offsets from Table 2, with pi's destination coordinates (y, 2x+3y).
    const ROT: [u32; 25] = [
        0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56,
        14,
    ];
    let mut b = [0u64; 25];
    let mut i = 0;
    while i < 25 {
        let x = i % 5;
        let y = i / 5;
        b[y + 5 * ((2 * x + 3 * y) % 5)] = (a[i] ^ d[x]).rotate_left(ROT[i]);
        i += 1;
    }
    let mut out = [0u64; 25];
    let mut i = 0;
    while i < 25 {
        let x = i % 5;
        let row = i - x;
        out[i] = b[i] ^ (!b[row + (x + 1) % 5] & b[row + (x + 2) % 5]);
        i += 1;
    }
    out[0] ^= rc;
    out
}

fn permute(state: &mut [u64; 25]) {
    let mut i = 0;
    while i < 24 {
        *state = round(state, RC[i]);
        i += 1;
    }
}

/// Incrementally absorbs separate fields without allocating their concatenation.
pub(crate) struct Sponge {
    lanes: [u64; 25],
    pos: usize,
}

impl Sponge {
    pub(crate) fn new() -> Self {
        Self {
            lanes: [0; 25],
            pos: 0,
        }
    }

    pub(crate) fn absorb(&mut self, data: &[u8]) {
        let mut i = 0;
        while i < data.len() {
            self.lanes[self.pos / 8] ^= (data[i] as u64) << (8 * (self.pos % 8));
            self.pos += 1;
            if self.pos == RATE {
                permute(&mut self.lanes);
                self.pos = 0;
            }
            i += 1;
        }
    }

    pub(crate) fn finish(mut self, out: &mut [u8]) {
        self.lanes[self.pos / 8] ^= 0x1fu64 << (8 * (self.pos % 8));
        self.lanes[RATE / 8 - 1] ^= 1u64 << 63;
        permute(&mut self.lanes);
        let mut pos = 0;
        let mut i = 0;
        while i < out.len() {
            if pos == RATE {
                permute(&mut self.lanes);
                pos = 0;
            }
            out[i] = (self.lanes[pos / 8] >> (8 * (pos % 8))) as u8;
            pos += 1;
            i += 1;
        }
    }
}

/// SHAKE256 with caller-selected output length, in bytes.
pub fn shake256(input: &[u8], output: &mut [u8]) {
    let mut sponge = Sponge::new();
    sponge.absorb(input);
    sponge.finish(output);
}
