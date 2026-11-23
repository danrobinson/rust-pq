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

// FIPS 202 rho and pi. Fixed offsets let the compiler emit immediate rotations.
#[inline(always)]
fn rho_pi(a: &[u64; 25], d: &[u64; 5]) -> [u64; 25] {
    [
        (a[0] ^ d[0]).rotate_left(0),
        (a[6] ^ d[1]).rotate_left(44),
        (a[12] ^ d[2]).rotate_left(43),
        (a[18] ^ d[3]).rotate_left(21),
        (a[24] ^ d[4]).rotate_left(14),
        (a[3] ^ d[3]).rotate_left(28),
        (a[9] ^ d[4]).rotate_left(20),
        (a[10] ^ d[0]).rotate_left(3),
        (a[16] ^ d[1]).rotate_left(45),
        (a[22] ^ d[2]).rotate_left(61),
        (a[1] ^ d[1]).rotate_left(1),
        (a[7] ^ d[2]).rotate_left(6),
        (a[13] ^ d[3]).rotate_left(25),
        (a[19] ^ d[4]).rotate_left(8),
        (a[20] ^ d[0]).rotate_left(18),
        (a[4] ^ d[4]).rotate_left(27),
        (a[5] ^ d[0]).rotate_left(36),
        (a[11] ^ d[1]).rotate_left(10),
        (a[17] ^ d[2]).rotate_left(15),
        (a[23] ^ d[3]).rotate_left(56),
        (a[2] ^ d[2]).rotate_left(62),
        (a[8] ^ d[3]).rotate_left(55),
        (a[14] ^ d[4]).rotate_left(39),
        (a[15] ^ d[0]).rotate_left(41),
        (a[21] ^ d[1]).rotate_left(2),
    ]
}

#[inline(always)]
fn chi(b: &[u64; 25]) -> [u64; 25] {
    [
        b[0] ^ (!b[1] & b[2]),
        b[1] ^ (!b[2] & b[3]),
        b[2] ^ (!b[3] & b[4]),
        b[3] ^ (!b[4] & b[0]),
        b[4] ^ (!b[0] & b[1]),
        b[5] ^ (!b[6] & b[7]),
        b[6] ^ (!b[7] & b[8]),
        b[7] ^ (!b[8] & b[9]),
        b[8] ^ (!b[9] & b[5]),
        b[9] ^ (!b[5] & b[6]),
        b[10] ^ (!b[11] & b[12]),
        b[11] ^ (!b[12] & b[13]),
        b[12] ^ (!b[13] & b[14]),
        b[13] ^ (!b[14] & b[10]),
        b[14] ^ (!b[10] & b[11]),
        b[15] ^ (!b[16] & b[17]),
        b[16] ^ (!b[17] & b[18]),
        b[17] ^ (!b[18] & b[19]),
        b[18] ^ (!b[19] & b[15]),
        b[19] ^ (!b[15] & b[16]),
        b[20] ^ (!b[21] & b[22]),
        b[21] ^ (!b[22] & b[23]),
        b[22] ^ (!b[23] & b[24]),
        b[23] ^ (!b[24] & b[20]),
        b[24] ^ (!b[20] & b[21]),
    ]
}

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

    let b = rho_pi(a, &d);
    let mut out = chi(&b);
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
