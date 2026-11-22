//! Is anything derived from the secret seed left on the stack after key
//! generation and signing? For each of the six SHA-2 parameter sets.
//!
//! Each scenario runs on a thread whose stack is memory this test owns, so
//! that the whole stack can be read afterwards. The memory is then searched
//! for the two secret seeds, HMAC's key blocks and key-dependent states, the
//! inner HMAC digest of `PRF_msg` (it depends on `SK.prf`), the FORS secret
//! values next to the revealed ones, and the WOTS+ secret values of the
//! bottom layer, each in the forms the code holds them in: as bytes, and as
//! the words of a SHA-256 or SHA-512 message schedule or state.
//!
//! A control scenario calls the verified functions directly, without the
//! adapter's stack scrubbing. It must leave something to find; otherwise the
//! search proves nothing. It also measures how deep the secret computations
//! go, which [`slh_dsa::SCRUB_BYTES`] must cover.
#![cfg(unix)]

use slh_dsa::{ParameterSet, SigningKey};
use slhdsa::address::{Adrs, FORS_TREE, WOTS_HASH, WOTS_PRF};
use slhdsa::fors::{fors_pk_from_sig, fors_sk_gen};
use slhdsa::hash::{chain_blocks, h_msg, seed_ctx, short_block, thash_short, value};
use slhdsa::params::Params;
use slhdsa::util::{base_2b, block, to_int};
use slhdsa::wots::wots_digits;
use slhdsa::{sha256, sha512};
use std::ffi::c_void;
use std::sync::{Arc, Mutex};

extern "C" {
    // In the system's thread library on macOS and Linux; the `libc` crate
    // does not declare it for macOS.
    fn pthread_attr_setstack(attr: *mut libc::pthread_attr_t, addr: *mut c_void, size: usize) -> libc::c_int;
}

const STACK_BYTES: usize = 4 << 20;
const FILL: u8 = 0xA5;
/// The margin the scrub must leave beyond the deepest measured call.
const MARGIN: usize = 8 * 1024;

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

/// The forms in which a value at block bytes `at..at + len` of a hash block
/// shows up: whole, in halves, and as the block's message-schedule words of
/// `word` bytes (4 for SHA-256, 8 for SHA-512), which are big-endian words
/// stored little-endian: each aligned group of `word` bytes reversed.
fn forms(name: &str, v: &[u8], at: usize, word: usize) -> Vec<(String, Vec<u8>)> {
    let half = v.len() / 2;
    let mut out = vec![(format!("{name} (bytes)"), v.to_vec())];
    out.push((format!("{name} (first half)"), v[..half].to_vec()));
    out.push((format!("{name} (second half)"), v[half..].to_vec()));
    let skip = (word - at % word) % word;
    let words: Vec<u8> = v[skip..].chunks_exact(word).flat_map(|w| w.iter().rev().copied().collect::<Vec<u8>>()).collect();
    out.push((format!("{name} (schedule words)"), words));
    out
}

/// A digest or state, as the bytes of its big-endian and of its native
/// (little-endian) words of `word` bytes, cut into 16-byte pieces.
fn digest_forms(name: &str, be: &[u8], word: usize) -> Vec<(String, Vec<u8>)> {
    let le: Vec<u8> = be.chunks_exact(word).flat_map(|w| w.iter().rev().copied().collect::<Vec<u8>>()).collect();
    let mut out = Vec::new();
    for (i, piece) in be.chunks_exact(16).enumerate() {
        out.push((format!("{name} (bytes {}..{})", 16 * i, 16 * i + 16), piece.to_vec()));
    }
    for (i, piece) in le.chunks_exact(16).enumerate() {
        out.push((format!("{name} (words, bytes {}..{})", 16 * i, 16 * i + 16), piece.to_vec()));
    }
    out
}

struct Case {
    seeds: Vec<u8>,
    msg: Vec<u8>,
    ctx: Vec<u8>,
    addrnd: Vec<u8>,
}

impl Case {
    /// `M' = 0 ‖ |ctx| ‖ ctx ‖ M`.
    fn framed(&self) -> Vec<u8> {
        let mut mp = vec![0u8, self.ctx.len() as u8];
        mp.extend_from_slice(&self.ctx);
        mp.extend_from_slice(&self.msg);
        mp
    }
}

/// The name searched for the inner HMAC digest of `PRF_msg`.
const INNER_DIGEST: &str = "PRF_msg inner digest";

/// Everything secret that the run of `case` computes and that we know how to
/// name, given the signature it produced.
fn secrets<const N: usize>(p: &Params, case: &Case, sig: &[u8]) -> Vec<(String, Vec<u8>)> {
    let sk_seed: [u8; N] = block::<N>(&case.seeds, 0);
    let sk_prf: [u8; N] = block::<N>(&case.seeds, 1);
    let pk_seed: [u8; N] = block::<N>(&case.seeds, 2);
    let mut sk = vec![0u8; 4 * N];
    let mut pk = vec![0u8; 2 * N];
    slhdsa::api::keygen::<N>(p, &case.seeds, &mut sk, &mut pk);
    let pk_root: [u8; N] = block::<N>(&pk, 1);
    let seed = seed_ctx::<N>(&pk_seed);
    // `PRF_msg` is HMAC-SHA-256 for n = 16 and HMAC-SHA-512 otherwise.
    let (blk, word) = if N == 16 { (64, 4) } else { (128, 8) };

    let mut out = Vec::new();
    out.extend(forms("SK.seed", &sk_seed, 22, 4));
    out.extend(forms("SK.prf", &sk_prf, 0, word));

    // HMAC: the two key blocks, the state after each, and the inner digest.
    let mut ipad = vec![0x36u8; blk];
    let mut opad = vec![0x5cu8; blk];
    for i in 0..N {
        ipad[i] ^= sk_prf[i];
        opad[i] ^= sk_prf[i];
    }
    out.extend(forms("HMAC inner key block", &ipad[..16], 0, word));
    out.extend(forms("HMAC outer key block", &opad[..16], 0, word));
    for (name, block) in [("HMAC inner state", &ipad), ("HMAC outer state", &opad)] {
        let (le, be): (Vec<u8>, Vec<u8>) = if N == 16 {
            let state = sha256::compress(&sha256::H0, block, 0);
            (state.iter().flat_map(|w| w.to_le_bytes()).collect(), state.iter().flat_map(|w| w.to_be_bytes()).collect())
        } else {
            let state = sha512::compress(&sha512::H0, block, 0);
            (state.iter().flat_map(|w| w.to_le_bytes()).collect(), state.iter().flat_map(|w| w.to_be_bytes()).collect())
        };
        out.push((format!("{name} (words)"), le[..16].to_vec()));
        out.push((format!("{name} (bytes)"), be[..16].to_vec()));
    }
    let mp = case.framed();
    let mut inner_input = ipad.clone();
    inner_input.extend_from_slice(&case.addrnd);
    inner_input.extend_from_slice(&mp);
    let inner: Vec<u8> = if N == 16 { sha256::sha256(&inner_input).to_vec() } else { sha512::sha512(&inner_input).to_vec() };
    out.extend(digest_forms(INNER_DIGEST, &inner, word));
    // The inner digest is what it should be: the outer hash of it is R.
    let mut outer_input = opad.clone();
    outer_input.extend_from_slice(&inner);
    let outer: Vec<u8> = if N == 16 { sha256::sha256(&outer_input).to_vec() } else { sha512::sha512(&outer_input).to_vec() };
    assert_eq!(&outer[..N], &sig[..N], "PRF_msg reconstruction");

    // Where this signature sits: digest, indices, addresses.
    let r: [u8; N] = block::<N>(sig, 0);
    let digest = h_msg::<N>(p, &r, &pk_seed, &pk_root, &mp);
    let md_len = p.md_bytes();
    let md = &digest[0..md_len];
    let idx_tree = to_int(&digest[md_len..md_len + p.tree_bytes()]) & (u64::MAX >> (64 - p.tree_bits()));
    let lo = md_len + p.tree_bytes();
    let idx_leaf = (to_int(&digest[lo..lo + p.leaf_bytes()]) & ((1u64 << p.hp) - 1)) as u32;
    let fors_adrs = Adrs::new().with_tree(idx_tree).with_type(FORS_TREE).with_keypair(idx_leaf);
    let (k, a) = (p.k, p.a);
    let indices = base_2b(md, a, k as usize);

    // FORS: the revealed secret value must be the one in the signature (this
    // checks the reconstruction above); its neighbour in the tree is secret.
    for i in 0..k {
        let at = N + (1 + a as usize) * N * i as usize;
        let revealed = fors_sk_gen::<N>(&sk_seed, &seed, fors_adrs, (i << a) + indices[i as usize]);
        assert_eq!(&revealed[..], &sig[at..at + N], "FORS reconstruction");
        let hidden = fors_sk_gen::<N>(&sk_seed, &seed, fors_adrs, (i << a) + (indices[i as usize] ^ 1));
        out.extend(forms(&format!("FORS secret value, tree {i}"), &hidden, 22, 4));
    }

    // WOTS+, bottom layer: the secret start of every chain that was advanced.
    let fors_end = N + p.fors_sig_bytes();
    let pk_fors = fors_pk_from_sig::<N>(p, &sig[N..fors_end], md, &seed, fors_adrs);
    let digits = wots_digits::<N>(&pk_fors);
    let hash_adrs = Adrs::new().with_layer(0).with_tree(idx_tree).with_type(WOTS_HASH).with_keypair(idx_leaf);
    let prf_adrs = hash_adrs.with_type(WOTS_PRF).with_keypair(idx_leaf);
    for i in 0..p.len() {
        let start = thash_short::<N>(&seed, &prf_adrs.with_word2(i as u32), &sk_seed);
        // Advancing it `digits[i]` steps must give the value in the signature.
        let mut block = [short_block(&hash_adrs.with_word2(i as u32), &start)];
        chain_blocks::<N>(&seed.state, &mut block, &[0], &[digits[i]]);
        let at = fors_end + N * i;
        assert_eq!(&value::<N>(&block[0])[..], &sig[at..at + N], "WOTS reconstruction");
        if digits[i] > 0 {
            out.extend(forms(&format!("WOTS secret value, chain {i}"), &start, 22, 4));
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
fn carry<P: ParameterSet>(key: SigningKey<P>) -> SigningKey<P> {
    std::hint::black_box(key)
}

/// The verified crate's functions for one set, on slices, called directly.
struct Direct {
    keygen: fn(&[u8], &mut [u8], &mut [u8]),
    sign: fn(&[u8], &[u8], &[u8], &[u8]) -> Option<Vec<u8>>,
    sign_checked: fn(&[u8], &[u8], &[u8], &[u8]) -> Option<Vec<u8>>,
}

macro_rules! direct {
    ($m:ident) => {
        Direct {
            keygen: |seeds, sk, pk| {
                slhdsa::$m::keygen(seeds.try_into().unwrap(), sk.try_into().unwrap(), pk.try_into().unwrap())
            },
            sign: |m, ctx, sk, addrnd| slhdsa::$m::sign(m, ctx, sk.try_into().unwrap(), addrnd.try_into().unwrap()),
            sign_checked: |m, ctx, sk, addrnd| {
                slhdsa::$m::sign_checked(m, ctx, sk.try_into().unwrap(), addrnd.try_into().unwrap())
            },
        }
    };
}

fn case(n: usize) -> Arc<Case> {
    let mut seeds = vec![0u8; 3 * n];
    for (i, b) in seeds.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(0x9d).wrapping_add(0x3b);
    }
    Arc::new(Case { seeds, msg: b"a message to sign".to_vec(), ctx: b"context".to_vec(), addrnd: vec![0xc7; n] })
}

/// The whole check for one set.
fn check<P: ParameterSet, const N: usize>(name: &str, p: &'static Params, direct: Direct) {
    let case = case(N);
    let direct = Arc::new(direct);

    // How deep each secret computation goes, called directly.
    let mut sk = vec![0u8; 4 * N];
    let mut pk = vec![0u8; 2 * N];
    (direct.keygen)(&case.seeds, &mut sk, &mut pk);
    let sk = Arc::new(sk);
    let (c, d) = (case.clone(), direct.clone());
    let keygen_depth = depth(&on_owned_stack(move || {
        let mut sk = vec![0u8; 4 * N];
        let mut pk = vec![0u8; 2 * N];
        (d.keygen)(&c.seeds, &mut sk, &mut pk);
        std::hint::black_box((&sk, &pk));
    }));
    let (c, d, k) = (case.clone(), direct.clone(), sk.clone());
    let sign_depth = depth(&on_owned_stack(move || {
        std::hint::black_box((d.sign)(&c.msg, &c.ctx, &k, &c.addrnd));
    }));
    let (c, d, k) = (case.clone(), direct.clone(), sk.clone());
    let checked_depth = depth(&on_owned_stack(move || {
        std::hint::black_box((d.sign_checked)(&c.msg, &c.ctx, &k, &c.addrnd));
    }));

    // Control: the verified functions called directly, with no scrubbing.
    let signature = Arc::new(Mutex::new(Vec::new()));
    let (c, s, d) = (case.clone(), signature.clone(), direct.clone());
    let stack = on_owned_stack(move || {
        let mut sk = vec![0u8; 4 * N];
        let mut pk = vec![0u8; 2 * N];
        (d.keygen)(&c.seeds, &mut sk, &mut pk);
        *s.lock().unwrap() = (d.sign)(&c.msg, &c.ctx, &sk, &c.addrnd).unwrap();
        // The checked signer too: it is the deepest computation.
        std::hint::black_box((d.sign_checked)(&c.msg, &c.ctx, &sk, &c.addrnd));
        sk.fill(0);
        std::hint::black_box(&sk);
    });
    let sig = signature.lock().unwrap().clone();
    let all = secrets::<N>(p, &case, &sig);
    let left = found(&stack, &all);
    let unscrubbed_depth = depth(&stack);

    println!(
        "{name}: stack used: keygen {keygen_depth}, sign {sign_depth}, sign_checked {checked_depth}, \
         all three {unscrubbed_depth} bytes (SCRUB_BYTES {})",
        slh_dsa::SCRUB_BYTES
    );
    println!("{name}: without scrubbing, {} of {} searched forms found", left.len(), all.len());
    for found in &left {
        println!("    {found}");
    }
    assert!(!left.is_empty(), "{name}: the control left nothing to find: this search cannot see residues");
    // The scrub must reach as deep as the computation went.
    for (what, d) in [("keygen", keygen_depth), ("sign", sign_depth), ("sign_checked", checked_depth), ("all", unscrubbed_depth)] {
        assert!(d + MARGIN <= slh_dsa::SCRUB_BYTES, "{name}: {what} used {d} bytes of stack; SCRUB_BYTES is too small");
    }

    // Control for the HMAC forms: the message PRF alone, stopped where HMAC's
    // key blocks and inner digest have just been on the stack.
    let c = case.clone();
    let stack = on_owned_stack(move || {
        let sk_prf: [u8; N] = block::<N>(&c.seeds, 1);
        let addrnd: [u8; N] = block::<N>(&c.addrnd, 0);
        std::hint::black_box(slhdsa::hash::prf_msg::<N>(&sk_prf, &addrnd, &c.framed()));
    });
    let left = found(&stack, &all);
    assert!(
        left.iter().any(|f| f.starts_with("HMAC")),
        "{name}: the control left no HMAC key block or state to find: {left:?}"
    );
    assert!(
        left.iter().any(|f| f.starts_with(INNER_DIGEST)),
        "{name}: the control left no form of PRF_msg's inner digest to find: {left:?}"
    );

    // The adapter: the same key and signature through its interface.
    let signature = Arc::new(Mutex::new(Vec::new()));
    let (c, s) = (case.clone(), signature.clone());
    let stack = on_owned_stack(move || {
        let key = SigningKey::<P>::slh_keygen_internal(&c.seeds[0..N], &c.seeds[N..2 * N], &c.seeds[2 * N..3 * N]);
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
    assert_eq!(*signature.lock().unwrap(), sig, "{name}: the two scenarios must compute the same signature");
    let left = found(&stack, &all);
    println!("{name}: with the adapter, {} bytes of stack used, {} of {} searched forms found", depth(&stack), left.len(), all.len());
    assert!(left.is_empty(), "{name}: left on the stack after the adapter returned: {left:?}");
}

#[test]
fn sha2_128s() {
    check::<slh_dsa::Sha2_128s, 16>("SHA2-128s", &slhdsa::params::SHA2_128S, direct!(sha2_128s));
}

#[test]
fn sha2_128f() {
    check::<slh_dsa::Sha2_128f, 16>("SHA2-128f", &slhdsa::params::SHA2_128F, direct!(sha2_128f));
}

#[test]
fn sha2_192s() {
    check::<slh_dsa::Sha2_192s, 24>("SHA2-192s", &slhdsa::params::SHA2_192S, direct!(sha2_192s));
}

#[test]
fn sha2_192f() {
    check::<slh_dsa::Sha2_192f, 24>("SHA2-192f", &slhdsa::params::SHA2_192F, direct!(sha2_192f));
}

#[test]
fn sha2_256s() {
    check::<slh_dsa::Sha2_256s, 32>("SHA2-256s", &slhdsa::params::SHA2_256S, direct!(sha2_256s));
}

#[test]
fn sha2_256f() {
    check::<slh_dsa::Sha2_256f, 32>("SHA2-256f", &slhdsa::params::SHA2_256F, direct!(sha2_256f));
}
