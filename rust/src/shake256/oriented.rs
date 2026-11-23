//! Scalar Keccak in a rotated lane representation. The state stores each
//! word rotated right by its fixed rho/pi output offset. AArch64 can fold
//! the rotations into XOR and BIC operands throughout theta and chi.
use super::{RATE, RC};

const OFF: [u32; 25] = [
    0, 44, 43, 21, 14, 28, 20, 3, 45, 61, 1, 6, 25, 8, 18, 27, 36, 10, 15, 56, 62, 55, 39, 41, 2,
];

#[inline(always)]
fn round(a: &[u64; 25], rc: u64) -> [u64; 25] {
    let c = [
        a[0].rotate_left(0)
            ^ a[5].rotate_left(28)
            ^ a[10].rotate_left(1)
            ^ a[15].rotate_left(27)
            ^ a[20].rotate_left(62),
        a[1].rotate_left(44)
            ^ a[6].rotate_left(20)
            ^ a[11].rotate_left(6)
            ^ a[16].rotate_left(36)
            ^ a[21].rotate_left(55),
        a[2].rotate_left(43)
            ^ a[7].rotate_left(3)
            ^ a[12].rotate_left(25)
            ^ a[17].rotate_left(10)
            ^ a[22].rotate_left(39),
        a[3].rotate_left(21)
            ^ a[8].rotate_left(45)
            ^ a[13].rotate_left(8)
            ^ a[18].rotate_left(15)
            ^ a[23].rotate_left(41),
        a[4].rotate_left(14)
            ^ a[9].rotate_left(61)
            ^ a[14].rotate_left(18)
            ^ a[19].rotate_left(56)
            ^ a[24].rotate_left(2),
    ];
    let d = [
        c[4] ^ c[1].rotate_left(1),
        c[0] ^ c[2].rotate_left(1),
        c[1] ^ c[3].rotate_left(1),
        c[2] ^ c[4].rotate_left(1),
        c[3] ^ c[0].rotate_left(1),
    ];
    // These are the rho/pi outputs before applying their fixed rotations.
    let v = [
        d[0] ^ a[0].rotate_left(0),
        d[1] ^ a[6].rotate_left(20),
        d[2] ^ a[12].rotate_left(25),
        d[3] ^ a[18].rotate_left(15),
        d[4] ^ a[24].rotate_left(2),
        d[3] ^ a[3].rotate_left(21),
        d[4] ^ a[9].rotate_left(61),
        d[0] ^ a[10].rotate_left(1),
        d[1] ^ a[16].rotate_left(36),
        d[2] ^ a[22].rotate_left(39),
        d[1] ^ a[1].rotate_left(44),
        d[2] ^ a[7].rotate_left(3),
        d[3] ^ a[13].rotate_left(8),
        d[4] ^ a[19].rotate_left(56),
        d[0] ^ a[20].rotate_left(62),
        d[4] ^ a[4].rotate_left(14),
        d[0] ^ a[5].rotate_left(28),
        d[1] ^ a[11].rotate_left(6),
        d[2] ^ a[17].rotate_left(10),
        d[3] ^ a[23].rotate_left(41),
        d[2] ^ a[2].rotate_left(43),
        d[3] ^ a[8].rotate_left(45),
        d[4] ^ a[14].rotate_left(18),
        d[0] ^ a[15].rotate_left(27),
        d[1] ^ a[21].rotate_left(55),
    ];
    // Rotate each chi expression back by its output lane offset.
    [
        v[0] ^ (v[2] & !v[1].rotate_left(1)).rotate_left(43) ^ rc,
        v[1] ^ (v[3] & !v[2].rotate_left(22)).rotate_left(41),
        v[2] ^ (v[4] & !v[3].rotate_left(7)).rotate_left(35),
        v[3] ^ (v[0] & !v[4].rotate_left(14)).rotate_left(43),
        v[4] ^ (v[1] & !v[0].rotate_left(20)).rotate_left(30),
        v[5] ^ (v[7] & !v[6].rotate_left(17)).rotate_left(39),
        v[6] ^ (v[8] & !v[7].rotate_left(22)).rotate_left(25),
        v[7] ^ (v[9] & !v[8].rotate_left(48)).rotate_left(58),
        v[8] ^ (v[5] & !v[9].rotate_left(33)).rotate_left(47),
        v[9] ^ (v[6] & !v[5].rotate_left(8)).rotate_left(23),
        v[10] ^ (v[12] & !v[11].rotate_left(45)).rotate_left(24),
        v[11] ^ (v[13] & !v[12].rotate_left(17)).rotate_left(2),
        v[12] ^ (v[14] & !v[13].rotate_left(54)).rotate_left(57),
        v[13] ^ (v[10] & !v[14].rotate_left(17)).rotate_left(57),
        v[14] ^ (v[11] & !v[10].rotate_left(59)).rotate_left(52),
        v[15] ^ (v[17] & !v[16].rotate_left(26)).rotate_left(47),
        v[16] ^ (v[18] & !v[17].rotate_left(59)).rotate_left(43),
        v[17] ^ (v[19] & !v[18].rotate_left(23)).rotate_left(46),
        v[18] ^ (v[15] & !v[19].rotate_left(29)).rotate_left(12),
        v[19] ^ (v[16] & !v[15].rotate_left(55)).rotate_left(44),
        v[20] ^ (v[22] & !v[21].rotate_left(16)).rotate_left(41),
        v[21] ^ (v[23] & !v[22].rotate_left(62)).rotate_left(50),
        v[22] ^ (v[24] & !v[23].rotate_left(39)).rotate_left(27),
        v[23] ^ (v[20] & !v[24].rotate_left(4)).rotate_left(21),
        v[24] ^ (v[21] & !v[20].rotate_left(7)).rotate_left(53),
    ]
}

pub(super) fn permute(state: &mut [u64; 25]) {
    let mut a = core::array::from_fn(|i| state[i].rotate_right(OFF[i]));
    for &rc in &RC {
        a = round(&a, rc);
    }
    for i in 0..25 {
        state[i] = a[i].rotate_left(OFF[i]);
    }
}

pub(super) fn blocks(state: &mut [u64; 25], blocks: &[u8]) {
    let mut a = core::array::from_fn(|i| state[i].rotate_right(OFF[i]));
    for block in blocks.chunks_exact(RATE) {
        for i in 0..17 {
            let word = u64::from_le_bytes(block[8 * i..8 * i + 8].try_into().unwrap());
            a[i] ^= word.rotate_right(OFF[i]);
        }
        for &rc in &RC {
            a = round(&a, rc);
        }
    }
    for i in 0..25 {
        state[i] = a[i].rotate_left(OFF[i]);
    }
}
