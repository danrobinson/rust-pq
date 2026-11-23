// Appended to the pinned SHA-3 block_api module by the verification driver.
use super::*;
use digest::typenum::U136;
type Core = Sha3HasherCore<U136, U0, { crate::SHAKE_PAD }>;

struct Permutation {
    _tag: [u8; 8],
    input: State1600,
    output: State1600,
    calls: usize,
}
static mut ORACLE: Permutation = Permutation {
    _tag: *b"SHAKE256",
    input: [0; 25],
    output: [0; 25],
    calls: 0,
};

pub(super) fn select(f: impl FnOnce(keccak::Fn1600)) {
    f(observe)
}
fn same(a: State1600, b: State1600) {
    for i in 0..25 {
        assert!(a[i] == b[i]);
    }
}
fn observe(state: &mut State1600) {
    unsafe {
        let input = ORACLE.input;
        assert!(ORACLE.calls == 0);
        same(*state, input);
        *state = ORACLE.output;
        ORACLE.calls = 1;
    }
}
fn expect(input: State1600) -> State1600 {
    let output = kani::any();
    unsafe {
        ORACLE.input = input;
        ORACLE.output = output;
    }
    output
}
fn checked() {
    unsafe {
        assert!(ORACLE.calls == 1);
    }
}

#[kani::proof]
#[kani::unwind(27)]
fn initial() {
    same(Core::default().state, [0; 25]);
}
fn xor_byte(state: &mut State1600, pos: usize, byte: u8) {
    state[pos / 8] ^= (byte as u64) << (8 * (pos % 8));
}

#[kani::proof]
#[kani::unwind(138)]
fn absorb_block() {
    let mut h = Core::default();
    h.state = kani::any();
    let bytes: [u8; 136] = kani::any();
    let mut expected = h.state;
    for (pos, &b) in bytes.iter().enumerate() {
        xor_byte(&mut expected, pos, b);
    }
    let output = expect(expected);
    h.update_blocks(&[bytes.into()]);
    checked();
    same(h.state, output);
}

#[kani::proof]
#[kani::unwind(138)]
fn pad() {
    let mut h = Core::default();
    h.state = kani::any();
    let bytes: [u8; 136] = kani::any();
    let pos: usize = kani::any();
    kani::assume(pos < 136);
    let mut buf = Buffer::<Core>::default();
    buf.set(bytes.into(), pos);
    let mut expected = h.state;
    for (i, &b) in bytes.iter().enumerate() {
        if i < pos {
            xor_byte(&mut expected, i, b);
        }
    }
    xor_byte(&mut expected, pos, 0x1f);
    xor_byte(&mut expected, 135, 0x80);
    let output = expect(expected);
    let r = h.finalize_xof_core(&mut buf);
    checked();
    same(r.state, output);
}

#[kani::proof]
#[kani::unwind(138)]
fn read_block() {
    let state: State1600 = kani::any();
    let mut reader = Sha3ReaderCore::<U136>::new(&state, keccak::Keccak::new());
    let next = expect(state);
    let bytes = reader.read_block();
    checked();
    same(reader.state, next);
    for (i, &b) in bytes.iter().enumerate() {
        assert_eq!(b, (state[i / 8] >> (8 * (i % 8))) as u8);
    }
}
