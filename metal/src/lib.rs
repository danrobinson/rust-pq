//! Apple Silicon Metal GPU compute backend for SLH-DSA (FIPS 205, SHA-2 sets).
//!
//! Supports all six FIPS 205 SHA-2 parameter sets:
//! - `SLH-DSA-SHA2-128s` & `SLH-DSA-SHA2-128f` (`N = 16`, SHA-256 everywhere)
//! - `SLH-DSA-SHA2-192s` & `SLH-DSA-SHA2-192f` (`N = 24`, SHA-256 + SHA-512)
//! - `SLH-DSA-SHA2-256s` & `SLH-DSA-SHA2-256f` (`N = 32`, SHA-256 + SHA-512)
//!
//! Uses Apple Silicon Unified Memory (`MTLResourceStorageModeShared`) for zero-copy
//! CPU/GPU handoff, executes all FORS, XMSS, and WOTS+ work inside a single Metal
//! command buffer, and zeroizes all secret key material buffers after GPU completion.

pub mod gpu;

use std::sync::Mutex;

use gpu::{InlineBytes, MetalBuffer, MetalContext, MetalError, MetalPipeline};
use slhdsa::hash::{h_msg, prf_msg, seed_ctx};
use slhdsa::params::Params;
use slhdsa::util::{base_2b, block, to_int};

const SHADER_SRC: &str = include_str!("../shaders/slhdsa.metal");

// ============================================================================
// Shared C-ABI Structs (matching shaders/slhdsa.metal)
// ============================================================================

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct KeyMaterial {
    sk_seed: [u32; 8],
    state256: [u32; 8],
    state512: [u64; 8],
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct XmssTreeDesc {
    tree: u64,
    key_idx: u32,
    layer: u32,
    target_leaf: u32,
    auth_byte_off: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct ForsJobDesc {
    idx_tree: u64,
    key_idx: u32,
    idx_leaf: u32,
    sig_byte_off: u32,
    _pad: u32,
    indices: [u32; 36],
}

impl Default for ForsJobDesc {
    fn default() -> Self {
        Self {
            idx_tree: 0,
            key_idx: 0,
            idx_leaf: 0,
            sig_byte_off: 0,
            _pad: 0,
            indices: [0u32; 36],
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct WotsSignLayerDesc {
    tree: u64,
    key_idx: u32,
    layer: u32,
    keypair: u32,
    sig_idx: u32,
    wots_byte_off: u32,
    _pad: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct XmssParams {
    num_trees: u32,
    hp: u32,
    leaves_per_tree: u32,
    wots_len: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct ForsParams {
    num_sigs: u32,
    k: u32,
    a: u32,
    s1: u32,
    s2: u32,
    subtrees_per_tree: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct WotsSignParams {
    num_layers: u32,
    d: u32,
    wots_len: u32,
}

// ============================================================================
// Pipeline Table & Unified-Memory Scratch Pool
// ============================================================================

struct PipelinesForN {
    wots_chains: MetalPipeline,
    wots_tlen: MetalPipeline,
    xmss_leaves_streaming: MetalPipeline,
    xmss_reduce: MetalPipeline,
    fors_pass1: MetalPipeline,
    fors_pass2: MetalPipeline,
    fors_pk: MetalPipeline,
    wots_sign: MetalPipeline,
}

impl PipelinesForN {
    fn load(ctx: &MetalContext, suffix: &str) -> Result<Self, MetalError> {
        Ok(Self {
            wots_chains: ctx.pipeline(&format!("wots_chains_{suffix}"))?,
            wots_tlen: ctx.pipeline(&format!("wots_tlen_{suffix}"))?,
            xmss_leaves_streaming: ctx.pipeline(&format!("xmss_leaves_streaming_{suffix}"))?,
            xmss_reduce: ctx.pipeline(&format!("xmss_reduce_{suffix}"))?,
            fors_pass1: ctx.pipeline(&format!("fors_pass1_{suffix}"))?,
            fors_pass2: ctx.pipeline(&format!("fors_pass2_{suffix}"))?,
            fors_pk: ctx.pipeline(&format!("fors_pk_{suffix}"))?,
            wots_sign: ctx.pipeline(&format!("wots_sign_{suffix}"))?,
        })
    }
}

struct ScratchPool {
    keys: Option<MetalBuffer>,
    xmss_trees: Option<MetalBuffer>,
    chain_tips: Option<MetalBuffer>,
    xmss_leaves: Option<MetalBuffer>,
    xmss_roots: Option<MetalBuffer>,
    fors_jobs: Option<MetalBuffer>,
    fors_sub_roots: Option<MetalBuffer>,
    fors_roots: Option<MetalBuffer>,
    pk_fors: Option<MetalBuffer>,
    wots_layers: Option<MetalBuffer>,
    out_sigs: Option<MetalBuffer>,
}

impl ScratchPool {
    fn new() -> Self {
        Self {
            keys: None,
            xmss_trees: None,
            chain_tips: None,
            xmss_leaves: None,
            xmss_roots: None,
            fors_jobs: None,
            fors_sub_roots: None,
            fors_roots: None,
            pk_fors: None,
            wots_layers: None,
            out_sigs: None,
        }
    }

    fn ensure<'a>(
        ctx: &MetalContext,
        slot: &'a mut Option<MetalBuffer>,
        min_bytes: usize,
        secret: bool,
    ) -> Result<&'a mut MetalBuffer, MetalError> {
        let need_alloc = match slot {
            Some(buf) => buf.len() < min_bytes,
            None => true,
        };
        if need_alloc {
            let cap = min_bytes.max(64);
            let buf = if secret {
                ctx.alloc_secret_buffer(cap)?
            } else {
                ctx.alloc_buffer(cap)?
            };
            *slot = Some(buf);
        }
        Ok(slot.as_mut().unwrap())
    }
}

// ============================================================================
// Request Types
// ============================================================================

/// A single internal-mode signing request (`slh_sign_internal`).
pub struct SignInternalReq<'a, const N: usize> {
    pub msg: &'a [u8],
    pub sk: &'a [u8],
    pub addrnd: &'a [u8; N],
}

/// A single pure-mode signing request (`slh_sign`).
pub struct SignReq<'a, const N: usize> {
    pub msg: &'a [u8],
    pub ctx: &'a [u8],
    pub sk: &'a [u8],
    pub addrnd: &'a [u8; N],
}

// ============================================================================
// MetalSigner
// ============================================================================

/// Apple Silicon Metal GPU compute engine for SLH-DSA-SHA2.
///
/// Compiles shaders and caches compute pipelines once on creation; safe to reuse
/// across any number of single or batched keygen and signing operations.
pub struct MetalSigner {
    ctx: MetalContext,
    p16: PipelinesForN,
    p24: PipelinesForN,
    p32: PipelinesForN,
    pool: Mutex<ScratchPool>,
    /// Leaf count threshold below which XMSS uses the two-phase per-chain kernel
    /// (`wots_chains` + `wots_tlen`) for maximum GPU thread occupancy; at or above
    /// this threshold it uses the zero-temp-memory `xmss_leaves_streaming` kernel.
    /// Set to `None` to use the per-`N` Apple Silicon tuned default (`4096` for
    /// `N = 16`, `49152` for `N = 24, 32` where splitting 32-bit WOTS chains from
    /// 64-bit SHA-512 `T_len` halves register pressure).
    pub two_phase_leaf_limit: Option<usize>,
}

impl MetalSigner {
    /// Initializes the default Apple Metal GPU device and compiles all SLH-DSA shaders.
    pub fn new() -> Result<Self, MetalError> {
        let ctx = MetalContext::new(SHADER_SRC)?;
        let p16 = PipelinesForN::load(&ctx, "N16")?;
        let p24 = PipelinesForN::load(&ctx, "N24")?;
        let p32 = PipelinesForN::load(&ctx, "N32")?;
        Ok(Self {
            ctx,
            p16,
            p24,
            p32,
            pool: Mutex::new(ScratchPool::new()),
            two_phase_leaf_limit: None,
        })
    }

    fn use_two_phase<const N: usize>(&self, total_leaves: usize) -> bool {
        let limit = self.two_phase_leaf_limit.unwrap_or(match N {
            16 => 4096,
            _ => 49152,
        });
        total_leaves < limit
    }

    /// Returns the name of the active Metal GPU (e.g. `"Apple M4"`).
    pub fn device_name(&self) -> String {
        self.ctx.device_name()
    }

    /// Returns true if the GPU uses Apple Silicon Unified Memory.
    pub fn has_unified_memory(&self) -> bool {
        self.ctx.has_unified_memory()
    }

    fn pipelines<const N: usize>(&self) -> Result<&PipelinesForN, MetalError> {
        match N {
            16 => Ok(&self.p16),
            24 => Ok(&self.p24),
            32 => Ok(&self.p32),
            _ => Err(MetalError(format!("unsupported SLH-DSA N={N}"))),
        }
    }

    // ------------------------------------------------------------------------
    // Keygen (Single & Batch)
    // ------------------------------------------------------------------------

    /// Algorithm 18, `slh_keygen_internal` on Metal GPU.
    pub fn keygen_internal<const N: usize>(
        &self,
        p: &Params,
        sk_seed: &[u8; N],
        sk_prf: &[u8; N],
        pk_seed: &[u8; N],
    ) -> Result<(Vec<u8>, Vec<u8>), MetalError> {
        let mut res = self.keygen_internal_batch::<N>(p, &[(*sk_seed, *sk_prf, *pk_seed)])?;
        Ok(res.pop().unwrap())
    }

    /// Algorithm 21, `slh_keygen` on Metal GPU, writing into caller buffers `sk` (4N) and `pk` (2N).
    pub fn keygen<const N: usize>(
        &self,
        p: &Params,
        seeds: &[u8],
        sk: &mut [u8],
        pk: &mut [u8],
    ) -> Result<(), MetalError> {
        assert_eq!(seeds.len(), 3 * N);
        assert_eq!(sk.len(), 4 * N);
        assert_eq!(pk.len(), 2 * N);
        let sk_seed = block::<N>(seeds, 0);
        let sk_prf = block::<N>(seeds, 1);
        let pk_seed = block::<N>(seeds, 2);
        let (sk_out, pk_out) = self.keygen_internal::<N>(p, &sk_seed, &sk_prf, &pk_seed)?;
        sk.copy_from_slice(&sk_out);
        pk.copy_from_slice(&pk_out);
        Ok(())
    }

    /// Batch key generation: generates `batch.len()` independent SLH-DSA keypairs
    /// in a single Metal GPU command buffer.
    pub fn keygen_internal_batch<const N: usize>(
        &self,
        p: &Params,
        batch: &[([u8; N], [u8; N], [u8; N])],
    ) -> Result<Vec<(Vec<u8>, Vec<u8>)>, MetalError> {
        assert_eq!(p.n, N);
        let count = batch.len();
        if count == 0 {
            return Ok(Vec::new());
        }

        let pipes = self.pipelines::<N>()?;
        let nw = N / 4;
        let leaves_per_tree = 1usize << p.hp;
        let total_leaves = count * leaves_per_tree;
        let wots_len = p.len();
        let use_two_phase = self.use_two_phase::<N>(total_leaves);

        let mut pool = self.pool.lock().unwrap();
        let keys_bytes = count * std::mem::size_of::<KeyMaterial>();
        let trees_bytes = count * std::mem::size_of::<XmssTreeDesc>();
        let leaves_bytes = total_leaves * N;
        let roots_bytes = count * N;

        {
            let keys_buf = ScratchPool::ensure(&self.ctx, &mut pool.keys, keys_bytes, true)?;
            let km_slice = keys_buf.as_mut_slice_of::<KeyMaterial>(count);
            for (i, (sk_seed, _sk_prf, pk_seed)) in batch.iter().enumerate() {
                km_slice[i] = build_key_material::<N>(sk_seed, pk_seed);
            }
        }
        {
            let trees_buf = ScratchPool::ensure(&self.ctx, &mut pool.xmss_trees, trees_bytes, false)?;
            let td_slice = trees_buf.as_mut_slice_of::<XmssTreeDesc>(count);
            for (i, td) in td_slice.iter_mut().enumerate() {
                *td = XmssTreeDesc {
                    tree: 0,
                    key_idx: i as u32,
                    layer: p.d - 1,
                    target_leaf: u32::MAX,
                    auth_byte_off: 0,
                };
            }
        }
        if use_two_phase {
            let tips_bytes = total_leaves * wots_len * N;
            ScratchPool::ensure(&self.ctx, &mut pool.chain_tips, tips_bytes, false)?;
        }
        ScratchPool::ensure(&self.ctx, &mut pool.xmss_leaves, leaves_bytes, false)?;
        ScratchPool::ensure(&self.ctx, &mut pool.xmss_roots, roots_bytes, false)?;
        // Dummy 16-byte out_sigs buffer for xmss_reduce binding (never written when target_leaf == MAX)
        ScratchPool::ensure(&self.ctx, &mut pool.out_sigs, 16, false)?;

        let xmss_params = XmssParams {
            num_trees: count as u32,
            hp: p.hp,
            leaves_per_tree: leaves_per_tree as u32,
            wots_len: wots_len as u32,
        };

        let keys_buf = pool.keys.as_ref().unwrap();
        let trees_buf = pool.xmss_trees.as_ref().unwrap();
        let leaves_buf = pool.xmss_leaves.as_ref().unwrap();
        let roots_buf = pool.xmss_roots.as_ref().unwrap();
        let out_sigs_buf = pool.out_sigs.as_ref().unwrap();

        let mut cmd = self.ctx.begin_cmd(false)?;
        if use_two_phase {
            let tips_buf = pool.chain_tips.as_ref().unwrap();
            let total_chains = (total_leaves * wots_len) as u32;
            let tg_chains = choose_tg_size(&pipes.wots_chains, total_chains);
            cmd.dispatch_threads(
                &pipes.wots_chains,
                &[keys_buf, trees_buf, tips_buf],
                &[InlineBytes::of(3, &xmss_params)],
                total_chains,
                tg_chains,
                0,
            );
            let tg_tlen = choose_tg_size(&pipes.wots_tlen, total_leaves as u32);
            cmd.dispatch_threads(
                &pipes.wots_tlen,
                &[keys_buf, trees_buf, tips_buf, leaves_buf],
                &[InlineBytes::of(4, &xmss_params)],
                total_leaves as u32,
                tg_tlen,
                0,
            );
        } else {
            let tg_leaves = choose_tg_size(&pipes.xmss_leaves_streaming, total_leaves as u32);
            cmd.dispatch_threads(
                &pipes.xmss_leaves_streaming,
                &[keys_buf, trees_buf, leaves_buf],
                &[InlineBytes::of(3, &xmss_params)],
                total_leaves as u32,
                tg_leaves,
                0,
            );
        }

        let reduce_tg = 1u32 << (p.hp - 1);
        let reduce_tg_mem = reduce_tg * (N as u32);
        cmd.dispatch_threadgroups(
            &pipes.xmss_reduce,
            &[keys_buf, trees_buf, leaves_buf, roots_buf, out_sigs_buf],
            &[InlineBytes::of(5, &xmss_params)],
            count as u32,
            reduce_tg,
            reduce_tg_mem,
        );

        let gpu_res = cmd.commit_and_wait();
        // Always scrub secret key material immediately after GPU finishes.
        pool.keys.as_mut().unwrap().zeroize_contents();
        gpu_res?;

        let roots_words = pool.xmss_roots.as_ref().unwrap().as_slice_of::<u32>(count * nw);
        let mut out = Vec::with_capacity(count);
        for (i, (sk_seed, sk_prf, pk_seed)) in batch.iter().enumerate() {
            let pk_root = words_to_bytes::<N>(&roots_words[i * nw..(i + 1) * nw]);
            let mut sk = Vec::with_capacity(4 * N);
            sk.extend_from_slice(sk_seed);
            sk.extend_from_slice(sk_prf);
            sk.extend_from_slice(pk_seed);
            sk.extend_from_slice(&pk_root);
            let mut pk = Vec::with_capacity(2 * N);
            pk.extend_from_slice(pk_seed);
            pk.extend_from_slice(&pk_root);
            out.push((sk, pk));
        }
        Ok(out)
    }

    // ------------------------------------------------------------------------
    // Signing (Single & Batch, Internal & Pure)
    // ------------------------------------------------------------------------

    /// Algorithm 19, `slh_sign_internal` on Metal GPU.
    pub fn sign_internal<const N: usize>(
        &self,
        p: &Params,
        m: &[u8],
        sk: &[u8],
        addrnd: &[u8; N],
    ) -> Result<Vec<u8>, MetalError> {
        let mut sigs = self.sign_internal_batch::<N>(
            p,
            &[SignInternalReq {
                msg: m,
                sk,
                addrnd,
            }],
        )?;
        Ok(sigs.pop().unwrap())
    }

    /// Algorithm 22, `slh_sign` (pure hedged signing) on Metal GPU.
    /// Returns `Ok(None)` if `ctx.len() > 255`.
    pub fn sign<const N: usize>(
        &self,
        p: &Params,
        m: &[u8],
        ctx: &[u8],
        sk: &[u8],
        addrnd: &[u8; N],
    ) -> Result<Option<Vec<u8>>, MetalError> {
        if ctx.len() > 255 {
            return Ok(None);
        }
        let mp = with_context(m, ctx);
        self.sign_internal::<N>(p, &mp, sk, addrnd).map(Some)
    }

    /// Algorithm 22, `slh_sign` (pure deterministic signing) on Metal GPU.
    /// Returns `Ok(None)` if `ctx.len() > 255`.
    pub fn sign_deterministic<const N: usize>(
        &self,
        p: &Params,
        m: &[u8],
        ctx: &[u8],
        sk: &[u8],
    ) -> Result<Option<Vec<u8>>, MetalError> {
        if ctx.len() > 255 {
            return Ok(None);
        }
        let pk_seed = block::<N>(sk, 2);
        self.sign::<N>(p, m, ctx, sk, &pk_seed)
    }

    /// Batch pure-mode signing (`slh_sign`) for arbitrary `(msg, ctx, sk, addrnd)` requests
    /// in a single Metal GPU command buffer. Returns `Ok(None)` if any `ctx.len() > 255`.
    pub fn sign_batch<const N: usize>(
        &self,
        p: &Params,
        requests: &[SignReq<'_, N>],
    ) -> Result<Option<Vec<Vec<u8>>>, MetalError> {
        if requests.iter().any(|r| r.ctx.len() > 255) {
            return Ok(None);
        }
        let framed: Vec<Vec<u8>> = requests
            .iter()
            .map(|r| with_context(r.msg, r.ctx))
            .collect();
        let internal_reqs: Vec<SignInternalReq<'_, N>> = requests
            .iter()
            .zip(framed.iter())
            .map(|(r, mp)| SignInternalReq {
                msg: mp.as_slice(),
                sk: r.sk,
                addrnd: r.addrnd,
            })
            .collect();
        self.sign_internal_batch::<N>(p, &internal_reqs).map(Some)
    }

    /// Convenience helper: batch-sign multiple messages under the same secret key `sk`
    /// with context `ctx` and per-message randomness `addrnds`.
    pub fn sign_batch_same_key<const N: usize>(
        &self,
        p: &Params,
        sk: &[u8],
        messages: &[&[u8]],
        ctx: &[u8],
        addrnds: &[&[u8; N]],
    ) -> Result<Option<Vec<Vec<u8>>>, MetalError> {
        assert_eq!(messages.len(), addrnds.len());
        if ctx.len() > 255 {
            return Ok(None);
        }
        let reqs: Vec<SignReq<'_, N>> = messages
            .iter()
            .zip(addrnds.iter())
            .map(|(&msg, &addrnd)| SignReq {
                msg,
                ctx,
                sk,
                addrnd,
            })
            .collect();
        self.sign_batch::<N>(p, &reqs)
    }

    /// Convenience helper: deterministic batch-sign multiple messages under the same `sk`.
    pub fn sign_deterministic_batch_same_key<const N: usize>(
        &self,
        p: &Params,
        sk: &[u8],
        messages: &[&[u8]],
        ctx: &[u8],
    ) -> Result<Option<Vec<Vec<u8>>>, MetalError> {
        if ctx.len() > 255 {
            return Ok(None);
        }
        let pk_seed = block::<N>(sk, 2);
        let reqs: Vec<SignReq<'_, N>> = messages
            .iter()
            .map(|&msg| SignReq {
                msg,
                ctx,
                sk,
                addrnd: &pk_seed,
            })
            .collect();
        self.sign_batch::<N>(p, &reqs)
    }

    /// Batch internal-mode signing (`slh_sign_internal`) in ONE single Metal GPU command buffer.
    pub fn sign_internal_batch<const N: usize>(
        &self,
        p: &Params,
        requests: &[SignInternalReq<'_, N>],
    ) -> Result<Vec<Vec<u8>>, MetalError> {
        assert_eq!(p.n, N);
        let num_sigs = requests.len();
        if num_sigs == 0 {
            return Ok(Vec::new());
        }

        let pipes = self.pipelines::<N>()?;
        let sig_bytes = p.sig_bytes();
        let fors_sig_bytes = p.fors_sig_bytes();
        let xmss_sig_bytes = p.xmss_sig_bytes();
        let wots_len = p.len();
        let d = p.d as usize;
        let hp = p.hp;
        let leaves_per_tree = 1usize << hp;
        let total_trees = num_sigs * d;
        let total_xmss_leaves = total_trees * leaves_per_tree;
        let use_two_phase = self.use_two_phase::<N>(total_xmss_leaves);

        // FORS two-pass split: s1 <= 8 (max 256 threads/TG), s2 <= 7 (max 128 threads/TG)
        let s1 = if p.a <= 8 { p.a } else { 7 };
        let s2 = p.a - s1;
        let subtrees_per_tree = 1u32 << s2;

        // CPU preprocessing: deduplicate KeyMaterial + compute R, H_msg, FORS indices, HT descriptors
        let mut unique_keys: Vec<([u8; N], [u8; N], KeyMaterial)> = Vec::new();
        let mut r_values: Vec<[u8; N]> = Vec::with_capacity(num_sigs);
        let mut fors_jobs_host: Vec<ForsJobDesc> = Vec::with_capacity(num_sigs);
        let mut xmss_trees_host: Vec<XmssTreeDesc> = Vec::with_capacity(total_trees);
        let mut wots_layers_host: Vec<WotsSignLayerDesc> = Vec::with_capacity(total_trees);

        for (sig_idx, req) in requests.iter().enumerate() {
            assert_eq!(req.sk.len(), 4 * N);
            let sk_seed = block::<N>(req.sk, 0);
            let sk_prf = block::<N>(req.sk, 1);
            let pk_seed = block::<N>(req.sk, 2);
            let pk_root = block::<N>(req.sk, 3);

            let key_idx = match unique_keys
                .iter()
                .position(|(ss, ps, _)| ss == &sk_seed && ps == &pk_seed)
            {
                Some(idx) => idx as u32,
                None => {
                    let km = build_key_material::<N>(&sk_seed, &pk_seed);
                    unique_keys.push((sk_seed, pk_seed, km));
                    (unique_keys.len() - 1) as u32
                }
            };

            let r = prf_msg::<N>(&sk_prf, req.addrnd, req.msg);
            let digest = h_msg::<N>(p, &r, &pk_seed, &pk_root, req.msg);
            let idx_tree = digest_tree(p, &digest);
            let idx_leaf = digest_leaf(p, &digest);
            let md = &digest[0..p.md_bytes()];
            let fors_idx_vec = base_2b(md, p.a, p.k as usize);

            let sig_byte_off = (sig_idx * sig_bytes) as u32;
            let mut fjob = ForsJobDesc {
                idx_tree,
                key_idx,
                idx_leaf,
                sig_byte_off,
                _pad: 0,
                indices: [0u32; 36],
            };
            for (i, &idx) in fors_idx_vec.iter().enumerate() {
                fjob.indices[i] = idx;
            }
            fors_jobs_host.push(fjob);
            r_values.push(r);

            let mut tree = idx_tree;
            let mut leaf = idx_leaf;
            for j in 0..d {
                let layer_sig_off = sig_byte_off + (N + fors_sig_bytes + j * xmss_sig_bytes) as u32;
                let auth_byte_off = layer_sig_off + (wots_len * N) as u32;
                xmss_trees_host.push(XmssTreeDesc {
                    tree,
                    key_idx,
                    layer: j as u32,
                    target_leaf: leaf,
                    auth_byte_off,
                });
                wots_layers_host.push(WotsSignLayerDesc {
                    tree,
                    key_idx,
                    layer: j as u32,
                    keypair: leaf,
                    sig_idx: sig_idx as u32,
                    wots_byte_off: layer_sig_off,
                    _pad: 0,
                });
                leaf = (tree & ((1u64 << hp) - 1)) as u32;
                tree >>= hp;
            }
        }

        let mut pool = self.pool.lock().unwrap();
        let num_keys = unique_keys.len();

        {
            let keys_buf = ScratchPool::ensure(
                &self.ctx,
                &mut pool.keys,
                num_keys * std::mem::size_of::<KeyMaterial>(),
                true,
            )?;
            let km_slice = keys_buf.as_mut_slice_of::<KeyMaterial>(num_keys);
            for (i, (_, _, km)) in unique_keys.iter().enumerate() {
                km_slice[i] = *km;
            }
        }
        {
            let trees_buf = ScratchPool::ensure(
                &self.ctx,
                &mut pool.xmss_trees,
                total_trees * std::mem::size_of::<XmssTreeDesc>(),
                false,
            )?;
            trees_buf
                .as_mut_slice_of::<XmssTreeDesc>(total_trees)
                .copy_from_slice(&xmss_trees_host);
        }
        {
            let fjobs_buf = ScratchPool::ensure(
                &self.ctx,
                &mut pool.fors_jobs,
                num_sigs * std::mem::size_of::<ForsJobDesc>(),
                false,
            )?;
            fjobs_buf
                .as_mut_slice_of::<ForsJobDesc>(num_sigs)
                .copy_from_slice(&fors_jobs_host);
        }
        {
            let wlayers_buf = ScratchPool::ensure(
                &self.ctx,
                &mut pool.wots_layers,
                total_trees * std::mem::size_of::<WotsSignLayerDesc>(),
                false,
            )?;
            wlayers_buf
                .as_mut_slice_of::<WotsSignLayerDesc>(total_trees)
                .copy_from_slice(&wots_layers_host);
        }

        if use_two_phase {
            ScratchPool::ensure(
                &self.ctx,
                &mut pool.chain_tips,
                total_xmss_leaves * wots_len * N,
                false,
            )?;
        }
        ScratchPool::ensure(&self.ctx, &mut pool.xmss_leaves, total_xmss_leaves * N, false)?;
        ScratchPool::ensure(&self.ctx, &mut pool.xmss_roots, total_trees * N, false)?;
        ScratchPool::ensure(
            &self.ctx,
            &mut pool.fors_sub_roots,
            num_sigs * (p.k as usize) * (subtrees_per_tree as usize) * N,
            false,
        )?;
        if s2 > 0 {
            ScratchPool::ensure(
                &self.ctx,
                &mut pool.fors_roots,
                num_sigs * (p.k as usize) * N,
                false,
            )?;
        }
        ScratchPool::ensure(&self.ctx, &mut pool.pk_fors, num_sigs * N, false)?;
        {
            let out_sigs_buf =
                ScratchPool::ensure(&self.ctx, &mut pool.out_sigs, num_sigs * sig_bytes, false)?;
            let sig_slice = out_sigs_buf.as_mut_slice();
            for (sig_idx, r) in r_values.iter().enumerate() {
                let off = sig_idx * sig_bytes;
                sig_slice[off..off + N].copy_from_slice(r);
            }
        }

        let xmss_params = XmssParams {
            num_trees: total_trees as u32,
            hp,
            leaves_per_tree: leaves_per_tree as u32,
            wots_len: wots_len as u32,
        };
        let fors_params = ForsParams {
            num_sigs: num_sigs as u32,
            k: p.k,
            a: p.a,
            s1,
            s2,
            subtrees_per_tree,
        };
        let wots_sign_params = WotsSignParams {
            num_layers: total_trees as u32,
            d: p.d,
            wots_len: wots_len as u32,
        };

        let keys_buf = pool.keys.as_ref().unwrap();
        let trees_buf = pool.xmss_trees.as_ref().unwrap();
        let leaves_buf = pool.xmss_leaves.as_ref().unwrap();
        let roots_buf = pool.xmss_roots.as_ref().unwrap();
        let fjobs_buf = pool.fors_jobs.as_ref().unwrap();
        let fsub_buf = pool.fors_sub_roots.as_ref().unwrap();
        let froots_buf = if s2 > 0 {
            pool.fors_roots.as_ref().unwrap()
        } else {
            fsub_buf
        };
        let pk_fors_buf = pool.pk_fors.as_ref().unwrap();
        let wlayers_buf = pool.wots_layers.as_ref().unwrap();
        let out_sigs_buf = pool.out_sigs.as_ref().unwrap();

        // Single concurrent command buffer overlapping XMSS and FORS across all M4 GPU cores!
        let mut cmd = self.ctx.begin_cmd(true)?;

        // Stage 1: Launch XMSS leaves (phase 1 or streaming) + FORS Pass 1 concurrently!
        if use_two_phase {
            let tips_buf = pool.chain_tips.as_ref().unwrap();
            let total_chains = (total_xmss_leaves * wots_len) as u32;
            let tg_chains = choose_tg_size(&pipes.wots_chains, total_chains);
            cmd.dispatch_threads(
                &pipes.wots_chains,
                &[keys_buf, trees_buf, tips_buf],
                &[InlineBytes::of(3, &xmss_params)],
                total_chains,
                tg_chains,
                0,
            );
        } else {
            let tg_leaves = choose_tg_size(&pipes.xmss_leaves_streaming, total_xmss_leaves as u32);
            cmd.dispatch_threads(
                &pipes.xmss_leaves_streaming,
                &[keys_buf, trees_buf, leaves_buf],
                &[InlineBytes::of(3, &xmss_params)],
                total_xmss_leaves as u32,
                tg_leaves,
                0,
            );
        }

        let fors1_tgs = (num_sigs as u32) * p.k * subtrees_per_tree;
        let fors1_tg_x = 1u32 << (s1 - 1);
        let fors1_tg_mem = fors1_tg_x * (N as u32);
        cmd.dispatch_threadgroups(
            &pipes.fors_pass1,
            &[keys_buf, fjobs_buf, fsub_buf, out_sigs_buf],
            &[InlineBytes::of(4, &fors_params)],
            fors1_tgs,
            fors1_tg_x,
            fors1_tg_mem,
        );

        cmd.barrier();

        // Stage 2:
        // - XMSS: wots_tlen (if two-phase) or xmss_reduce (if streaming)
        // - FORS: fors_pass2 (if s2 > 0) or fors_pk (if s2 == 0)
        if use_two_phase {
            let tips_buf = pool.chain_tips.as_ref().unwrap();
            let tg_tlen = choose_tg_size(&pipes.wots_tlen, total_xmss_leaves as u32);
            cmd.dispatch_threads(
                &pipes.wots_tlen,
                &[keys_buf, trees_buf, tips_buf, leaves_buf],
                &[InlineBytes::of(4, &xmss_params)],
                total_xmss_leaves as u32,
                tg_tlen,
                0,
            );
        } else {
            let reduce_tg = 1u32 << (hp - 1);
            let reduce_tg_mem = reduce_tg * (N as u32);
            cmd.dispatch_threadgroups(
                &pipes.xmss_reduce,
                &[keys_buf, trees_buf, leaves_buf, roots_buf, out_sigs_buf],
                &[InlineBytes::of(5, &xmss_params)],
                total_trees as u32,
                reduce_tg,
                reduce_tg_mem,
            );
        }

        if s2 > 0 {
            let fors2_tgs = (num_sigs as u32) * p.k;
            let fors2_tg_x = 1u32 << (s2 - 1);
            let fors2_tg_mem = fors2_tg_x * (N as u32);
            cmd.dispatch_threadgroups(
                &pipes.fors_pass2,
                &[keys_buf, fjobs_buf, fsub_buf, froots_buf, out_sigs_buf],
                &[InlineBytes::of(5, &fors_params)],
                fors2_tgs,
                fors2_tg_x,
                fors2_tg_mem,
            );
        } else {
            let tg_fpk = choose_tg_size(&pipes.fors_pk, num_sigs as u32);
            cmd.dispatch_threads(
                &pipes.fors_pk,
                &[keys_buf, fjobs_buf, froots_buf, pk_fors_buf],
                &[InlineBytes::of(4, &fors_params)],
                num_sigs as u32,
                tg_fpk,
                0,
            );
        }

        cmd.barrier();

        // Stage 3: finish xmss_reduce (if two-phase) and/or fors_pk (if s2 > 0)
        let mut need_stage3_barrier = false;
        if use_two_phase {
            let reduce_tg = 1u32 << (hp - 1);
            let reduce_tg_mem = reduce_tg * (N as u32);
            cmd.dispatch_threadgroups(
                &pipes.xmss_reduce,
                &[keys_buf, trees_buf, leaves_buf, roots_buf, out_sigs_buf],
                &[InlineBytes::of(5, &xmss_params)],
                total_trees as u32,
                reduce_tg,
                reduce_tg_mem,
            );
            need_stage3_barrier = true;
        }
        if s2 > 0 {
            let tg_fpk = choose_tg_size(&pipes.fors_pk, num_sigs as u32);
            cmd.dispatch_threads(
                &pipes.fors_pk,
                &[keys_buf, fjobs_buf, froots_buf, pk_fors_buf],
                &[InlineBytes::of(4, &fors_params)],
                num_sigs as u32,
                tg_fpk,
                0,
            );
            need_stage3_barrier = true;
        }
        if need_stage3_barrier {
            cmd.barrier();
        }

        // Final Stage: WOTS+ signatures for all B * d layers written directly into out_sigs!
        let total_wots_chains = (total_trees * wots_len) as u32;
        let tg_wsig = choose_tg_size(&pipes.wots_sign, total_wots_chains);
        cmd.dispatch_threads(
            &pipes.wots_sign,
            &[keys_buf, wlayers_buf, pk_fors_buf, roots_buf, out_sigs_buf],
            &[InlineBytes::of(5, &wots_sign_params)],
            total_wots_chains,
            tg_wsig,
            0,
        );

        let gpu_res = cmd.commit_and_wait();
        // Scrub secret key buffer immediately after GPU execution completes.
        pool.keys.as_mut().unwrap().zeroize_contents();
        gpu_res?;

        let sig_slice = pool.out_sigs.as_ref().unwrap().as_slice();
        let mut out = Vec::with_capacity(num_sigs);
        for sig_idx in 0..num_sigs {
            let off = sig_idx * sig_bytes;
            out.push(sig_slice[off..off + sig_bytes].to_vec());
        }
        Ok(out)
    }
}

// ============================================================================
// Helpers
// ============================================================================

fn build_key_material<const N: usize>(sk_seed: &[u8; N], pk_seed: &[u8; N]) -> KeyMaterial {
    let seed = seed_ctx::<N>(pk_seed);
    let mut sk_words = [0u32; 8];
    for i in 0..(N / 4) {
        sk_words[i] = u32::from_be_bytes([
            sk_seed[4 * i],
            sk_seed[4 * i + 1],
            sk_seed[4 * i + 2],
            sk_seed[4 * i + 3],
        ]);
    }
    KeyMaterial {
        sk_seed: sk_words,
        state256: seed.state,
        state512: seed.state512,
    }
}

fn words_to_bytes<const N: usize>(words: &[u32]) -> [u8; N] {
    let mut out = [0u8; N];
    for i in 0..(N / 4) {
        out[4 * i..4 * i + 4].copy_from_slice(&words[i].to_be_bytes());
    }
    out
}

fn with_context(m: &[u8], ctx: &[u8]) -> Vec<u8> {
    let mut mp = Vec::with_capacity(2 + ctx.len() + m.len());
    mp.push(0u8);
    mp.push(ctx.len() as u8);
    mp.extend_from_slice(ctx);
    mp.extend_from_slice(m);
    mp
}

fn digest_tree(p: &Params, digest: &[u8]) -> u64 {
    let lo = p.md_bytes();
    to_int(&digest[lo..lo + p.tree_bytes()]) & (u64::MAX >> (64 - p.tree_bits()))
}

fn digest_leaf(p: &Params, digest: &[u8]) -> u32 {
    let lo = p.md_bytes() + p.tree_bytes();
    (to_int(&digest[lo..lo + p.leaf_bytes()]) & ((1u64 << p.hp) - 1)) as u32
}

fn choose_tg_size(pipe: &MetalPipeline, total_threads: u32) -> u32 {
    let max_tg = pipe.max_tg_size().min(256).max(1);
    let simd = pipe.simd_width().max(1);
    let target = if total_threads <= simd {
        total_threads.max(1)
    } else if total_threads <= 128 {
        128.min(max_tg)
    } else {
        256.min(max_tg)
    };
    target.max(1)
}

// ============================================================================
// Typed Per-Set Convenience Modules
// ============================================================================

macro_rules! metal_set {
    ($mod_name:ident, $slh_mod:ident) => {
        pub mod $mod_name {
            use super::{MetalError, MetalSigner};
            pub use slhdsa::$slh_mod::params;
            use params::{N, PARAMS, PK_BYTES, SEED_BYTES, SK_BYTES};

            pub fn keygen_internal(
                gpu: &MetalSigner,
                sk_seed: &[u8; N],
                sk_prf: &[u8; N],
                pk_seed: &[u8; N],
            ) -> Result<([u8; SK_BYTES], [u8; PK_BYTES]), MetalError> {
                let (sk, pk) = gpu.keygen_internal::<N>(&PARAMS, sk_seed, sk_prf, pk_seed)?;
                Ok((sk.try_into().unwrap(), pk.try_into().unwrap()))
            }

            pub fn keygen(
                gpu: &MetalSigner,
                seeds: &[u8; SEED_BYTES],
                sk: &mut [u8; SK_BYTES],
                pk: &mut [u8; PK_BYTES],
            ) -> Result<(), MetalError> {
                gpu.keygen::<N>(&PARAMS, seeds, sk, pk)
            }

            pub fn sign_internal(
                gpu: &MetalSigner,
                m: &[u8],
                sk: &[u8; SK_BYTES],
                addrnd: &[u8; N],
            ) -> Result<Vec<u8>, MetalError> {
                gpu.sign_internal::<N>(&PARAMS, m, sk, addrnd)
            }

            pub fn sign(
                gpu: &MetalSigner,
                m: &[u8],
                ctx: &[u8],
                sk: &[u8; SK_BYTES],
                addrnd: &[u8; N],
            ) -> Result<Option<Vec<u8>>, MetalError> {
                gpu.sign::<N>(&PARAMS, m, ctx, sk, addrnd)
            }

            pub fn sign_deterministic(
                gpu: &MetalSigner,
                m: &[u8],
                ctx: &[u8],
                sk: &[u8; SK_BYTES],
            ) -> Result<Option<Vec<u8>>, MetalError> {
                gpu.sign_deterministic::<N>(&PARAMS, m, ctx, sk)
            }

            pub fn sign_batch_same_key(
                gpu: &MetalSigner,
                sk: &[u8; SK_BYTES],
                messages: &[&[u8]],
                ctx: &[u8],
                addrnds: &[&[u8; N]],
            ) -> Result<Option<Vec<Vec<u8>>>, MetalError> {
                gpu.sign_batch_same_key::<N>(&PARAMS, sk, messages, ctx, addrnds)
            }

            pub fn sign_deterministic_batch_same_key(
                gpu: &MetalSigner,
                sk: &[u8; SK_BYTES],
                messages: &[&[u8]],
                ctx: &[u8],
            ) -> Result<Option<Vec<Vec<u8>>>, MetalError> {
                gpu.sign_deterministic_batch_same_key::<N>(&PARAMS, sk, messages, ctx)
            }

            pub fn verify(m: &[u8], sig: &[u8], ctx: &[u8], pk: &[u8; PK_BYTES]) -> bool {
                slhdsa::$slh_mod::verify(m, sig, ctx, pk)
            }
        }
    };
}

metal_set!(sha2_128s, sha2_128s);
metal_set!(sha2_128f, sha2_128f);
metal_set!(sha2_192s, sha2_192s);
metal_set!(sha2_192f, sha2_192f);
metal_set!(sha2_256s, sha2_256s);
metal_set!(sha2_256f, sha2_256f);
