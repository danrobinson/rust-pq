//! Is anything derived from the secret seed left on the stack after key
//! generation and signing?
//!
//! Each scenario runs on a thread whose stack is memory this test owns, so
//! that the whole stack can be read afterwards. The memory is then searched
//! for the two secret seeds, HMAC's key blocks and key-dependent state, the
//! FORS secret values next to the revealed ones, and the WOTS+ secret values
//! of the bottom layer, each in the forms the code holds them in: as bytes,
//! and as the 32-bit words of a SHA-256 message schedule.
//!
//! A control scenario calls the verified functions directly, without the
//! adapter's stack scrubbing. It must leave something to find; otherwise the
//! search proves nothing.
#![cfg(unix)]

use slh_dsa::{Sha2_128s, SigningKey};
use slhdsa::address::{Adrs, FORS_TREE, WOTS_HASH, WOTS_PRF};
use slhdsa::fors::{fors_pk_from_sig, fors_sk_gen};
use slhdsa::hash::{chain_blocks, h_msg, seed_ctx, short_block, thash_short, value};
use slhdsa::sha256::{compress, H0};
use slhdsa::util::{base_2b, to_int};
use slhdsa::wots::wots_digits;
use std::ffi::c_void;
use std::sync::{Arc, Mutex};

extern "C" {
    // In the system's thread library on macOS and Linux; the `libc` crate
    // does not declare it for macOS.
    fn pthread_attr_setstack(attr: *mut libc::pthread_attr_t, addr: *mut c_void, size: usize) -> libc::c_int;
}

const STACK_BYTES: usize = 4 << 20;
const FILL: u8 = 0xA5;

/// Run `f` on a fresh thread whose stack is returned afterwards.
fn on_owned_stack(f: impl FnOnce() + Send + 'static) -> Vec<u8> {
    extern "C" fn start(arg: *mut c_void) -> *mut c_void {
        // SAFETY: `arg` is the box leaked below, passed to exactly one thread.
        let f: Box<Box<dyn FnOnce() + Send>> = unsafe { Box::from_raw(arg.cast()) };
        if std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f())).is_err() {
            std::process::abort();
        }
        std::ptr::null_mut()
    }
    // SAFETY: plain use of mmap and pthreads. The mapping outlives the thread
    // (it is joined before the memory is read) and is unmapped at the end.
    unsafe {
        let stack = libc::mmap(
            std::ptr::null_mut(),
            STACK_BYTES,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_PRIVATE | libc::MAP_ANON,
            -1,
            0,
        );
        assert!(stack != libc::MAP_FAILED);
        std::ptr::write_bytes(stack.cast::<u8>(), FILL, STACK_BYTES);
        let mut attr: libc::pthread_attr_t = std::mem::zeroed();
        assert_eq!(libc::pthread_attr_init(&mut attr), 0);
        assert_eq!(pthread_attr_setstack(&mut attr, stack, STACK_BYTES), 0);
        let arg: Box<Box<dyn FnOnce() + Send>> = Box::new(Box::new(f));
        let mut thread: libc::pthread_t = std::mem::zeroed();
        assert_eq!(libc::pthread_create(&mut thread, &attr, start, Box::into_raw(arg).cast()), 0);
        assert_eq!(libc::pthread_join(thread, std::ptr::null_mut()), 0);
        libc::pthread_attr_destroy(&mut attr);
        let copy = std::slice::from_raw_parts(stack.cast::<u8>(), STACK_BYTES).to_vec();
        libc::munmap(stack, STACK_BYTES);
        copy
    }
}

/// How far down the stack was written (it grows from the high end).
fn depth(stack: &[u8]) -> usize {
    stack.len() - stack.iter().position(|b| *b != FILL).unwrap_or(stack.len())
}

/// The forms in which a 16-byte value at block bytes `at..at + 16` shows up.
fn forms(name: &str, v: &[u8], at: usize) -> Vec<(String, Vec<u8>)> {
    let mut out = vec![(format!("{name} (bytes)"), v.to_vec())];
    out.push((format!("{name} (first half)"), v[..8].to_vec()));
    out.push((format!("{name} (second half)"), v[8..].to_vec()));
    // In a message schedule the block is held as big-endian words, stored
    // little-endian: each aligned group of four bytes reversed.
    let skip = (4 - at % 4) % 4;
    let words: Vec<u8> = v[skip..].chunks_exact(4).flat_map(|w| w.iter().rev().copied().collect::<Vec<u8>>()).collect();
    out.push((format!("{name} (schedule words)"), words));
    out
}

struct Case {
    seeds: [u8; 48],
    msg: Vec<u8>,
    ctx: Vec<u8>,
    addrnd: [u8; 16],
}

/// Everything secret that the run of `case` computes and that we know how to
/// name, given the signature it produced.
fn secrets(case: &Case, sig: &[u8]) -> Vec<(String, Vec<u8>)> {
    let sk_seed: [u8; 16] = case.seeds[0..16].try_into().unwrap();
    let sk_prf: [u8; 16] = case.seeds[16..32].try_into().unwrap();
    let pk_seed: [u8; 16] = case.seeds[32..48].try_into().unwrap();
    let mut sk = [0u8; 64];
    let mut pk = [0u8; 32];
    slhdsa::keygen(&case.seeds, &mut sk, &mut pk);
    let pk_root: [u8; 16] = pk[16..32].try_into().unwrap();
    let seed = seed_ctx(&pk_seed);

    let mut out = Vec::new();
    out.extend(forms("SK.seed", &sk_seed, 22));
    out.extend(forms("SK.prf", &sk_prf, 0));

    // HMAC: the two key blocks and the state after each.
    let mut ipad = [0x36u8; 64];
    let mut opad = [0x5cu8; 64];
    for i in 0..16 {
        ipad[i] ^= sk_prf[i];
        opad[i] ^= sk_prf[i];
    }
    out.extend(forms("HMAC inner key block", &ipad[..16], 0));
    out.extend(forms("HMAC outer key block", &opad[..16], 0));
    for (name, block) in [("HMAC inner state", &ipad), ("HMAC outer state", &opad)] {
        let state = compress(&H0, block, 0);
        let le: Vec<u8> = state.iter().flat_map(|w| w.to_le_bytes()).collect();
        let be: Vec<u8> = state.iter().flat_map(|w| w.to_be_bytes()).collect();
        out.push((format!("{name} (words)"), le[..16].to_vec()));
        out.push((format!("{name} (bytes)"), be[..16].to_vec()));
    }

    // Where this signature sits: digest, indices, addresses.
    let mut mp = vec![0u8, case.ctx.len() as u8];
    mp.extend_from_slice(&case.ctx);
    mp.extend_from_slice(&case.msg);
    let r: [u8; 16] = sig[0..16].try_into().unwrap();
    let digest = h_msg(&r, &pk_seed, &pk_root, &mp);
    let md = &digest[0..21];
    let idx_tree = to_int(&digest[21..28]) & ((1u64 << 54) - 1);
    let idx_leaf = (to_int(&digest[28..30]) & 511) as u32;
    let fors_adrs = Adrs::new().with_tree(idx_tree).with_type(FORS_TREE).with_keypair(idx_leaf);
    let indices = base_2b(md, 12, 14);

    // FORS: the revealed secret value must be the one in the signature (this
    // checks the reconstruction above); its neighbour in the tree is secret.
    for i in 0..14u32 {
        let revealed = fors_sk_gen(&sk_seed, &seed, fors_adrs, (i << 12) + indices[i as usize]);
        assert_eq!(&revealed[..], &sig[16 + 208 * i as usize..32 + 208 * i as usize], "FORS reconstruction");
        let hidden = fors_sk_gen(&sk_seed, &seed, fors_adrs, (i << 12) + (indices[i as usize] ^ 1));
        out.extend(forms(&format!("FORS secret value, tree {i}"), &hidden, 22));
    }

    // WOTS+, bottom layer: the secret start of every chain that was advanced.
    let sig_fors = &sig[16..16 + 2912];
    let pk_fors = fors_pk_from_sig(sig_fors, md, &seed, fors_adrs);
    let digits = wots_digits(&pk_fors);
    let hash_adrs = Adrs::new().with_layer(0).with_tree(idx_tree).with_type(WOTS_HASH).with_keypair(idx_leaf);
    let prf_adrs = hash_adrs.with_type(WOTS_PRF).with_keypair(idx_leaf);
    for i in 0..35usize {
        let start = thash_short(&seed, &prf_adrs.with_word2(i as u32), &sk_seed);
        // Advancing it `digits[i]` steps must give the value in the signature.
        let mut block = [short_block(&hash_adrs.with_word2(i as u32), &start)];
        chain_blocks(&seed.state, &mut block, &[0], &[digits[i]]);
        let at = 16 + 2912 + 16 * i;
        assert_eq!(&value(&block[0])[..], &sig[at..at + 16], "WOTS reconstruction");
        if digits[i] > 0 {
            out.extend(forms(&format!("WOTS secret value, chain {i}"), &start, 22));
        }
    }
    out
}

/// The searched forms present in `stack`, each with how far below the top of
/// the stack its occurrences lie.
fn found(stack: &[u8], secrets: &[(String, Vec<u8>)]) -> Vec<String> {
    let mut out = Vec::new();
    for (name, pattern) in secrets {
        let at: Vec<usize> = stack
            .windows(pattern.len())
            .enumerate()
            .filter(|(_, w)| *w == &pattern[..])
            .map(|(i, _)| stack.len() - i)
            .collect();
        if !at.is_empty() {
            out.push(format!("{name}, {at:?} bytes below the top"));
        }
    }
    out
}

/// Pass a key by value through a call that is not inlined.
#[inline(never)]
fn carry(key: SigningKey<Sha2_128s>) -> SigningKey<Sha2_128s> {
    std::hint::black_box(key)
}

fn case() -> Arc<Case> {
    let mut seeds = [0u8; 48];
    for (i, b) in seeds.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(0x9d).wrapping_add(0x3b);
    }
    Arc::new(Case { seeds, msg: b"a message to sign".to_vec(), ctx: b"context".to_vec(), addrnd: [0xc7; 16] })
}

#[test]
fn nothing_secret_is_left_on_the_stack() {
    let case = case();

    // Control: the verified functions called directly, with no scrubbing.
    let signature = Arc::new(Mutex::new(Vec::new()));
    let (c, s) = (case.clone(), signature.clone());
    let stack = on_owned_stack(move || {
        let mut sk = [0u8; 64];
        let mut pk = [0u8; 32];
        slhdsa::keygen(&c.seeds, &mut sk, &mut pk);
        *s.lock().unwrap() = slhdsa::sign(&c.msg, &c.ctx, &sk, &c.addrnd).unwrap();
        // The checked signer too: it is the deepest computation.
        std::hint::black_box(slhdsa::sign_checked(&c.msg, &c.ctx, &sk, &c.addrnd));
        sk.fill(0);
        std::hint::black_box(&sk);
    });
    let sig = signature.lock().unwrap().clone();
    let all = secrets(&case, &sig);
    let left = found(&stack, &all);
    let unscrubbed_depth = depth(&stack);
    println!("without scrubbing: {} bytes of stack used, {} of {} searched forms found", unscrubbed_depth, left.len(), all.len());
    for name in &left {
        println!("    {name}");
    }
    assert!(!left.is_empty(), "the control left nothing to find: this search cannot see residues");
    // The scrub must reach as deep as the computation went.
    assert!(
        unscrubbed_depth + 8 * 1024 <= slh_dsa::SCRUB_BYTES,
        "signing used {unscrubbed_depth} bytes of stack; SCRUB_BYTES is too small"
    );

    // Control for the derived forms: the message PRF alone, stopped where
    // HMAC's key blocks have just been on the stack.
    let c = case.clone();
    let stack = on_owned_stack(move || {
        let sk_prf: [u8; 16] = c.seeds[16..32].try_into().unwrap();
        std::hint::black_box(slhdsa::hash::prf_msg(&sk_prf, &c.addrnd, &c.msg));
    });
    let left = found(&stack, &all);
    assert!(
        left.iter().any(|name| name.starts_with("HMAC")),
        "the control left no HMAC key block or state to find: {left:?}"
    );

    // The adapter: the same key and signature through its interface.
    let signature = Arc::new(Mutex::new(Vec::new()));
    let (c, s) = (case.clone(), signature.clone());
    let stack = on_owned_stack(move || {
        let key = SigningKey::<Sha2_128s>::slh_keygen_internal(&c.seeds[0..16], &c.seeds[16..32], &c.seeds[32..48]);
        let sig = key.try_sign_with_context(&c.msg, &c.ctx, Some(&c.addrnd)).unwrap();
        *s.lock().unwrap() = sig.to_vec();
        std::hint::black_box(key.try_sign_checked(&c.msg, &c.ctx, Some(&c.addrnd)).unwrap());
        // Move the key about before it is dropped. A moved value leaves its
        // bytes where it was, and nothing can wipe them there; the key
        // holds its secret in an allocation of its own so that a move
        // copies only a pointer.
        let moved = std::hint::black_box(carry(key));
        let copy = moved.clone();
        drop(moved);
        drop(std::hint::black_box(carry(copy)));
    });
    assert_eq!(*signature.lock().unwrap(), sig, "the two scenarios must compute the same signature");
    let left = found(&stack, &all);
    println!("with the adapter: {} bytes of stack used, {} of {} searched forms found", depth(&stack), left.len(), all.len());
    assert!(left.is_empty(), "left on the stack after the adapter returned: {left:?}");
}
