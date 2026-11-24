//! Apple Silicon Metal GPU compute backend for SLH-DSA (FIPS 205, all 12 SHA-2 & SHAKE sets).
//!
//! Supports all twelve FIPS 205 parameter sets:
//! - SHA-2: `SLH-DSA-SHA2-{128s,128f,192s,192f,256s,256f}`
//! - SHAKE: `SLH-DSA-SHAKE-{128s,128f,192s,192f,256s,256f}`
//!
//! Uses Apple Silicon Unified Memory (`MTLResourceStorageModeShared`) for zero-copy
//! CPU/GPU handoff, executes all FORS, XMSS, and WOTS+ work inside a single concurrent
//! Metal command buffer, and zeroizes all secret key material buffers after GPU completion.

pub mod gpu;

use std::sync::Mutex;

use gpu::{InlineBytes, MetalBuffer, MetalContext, MetalError, MetalPipeline};
use slhdsa::hash::{h_msg, prf_msg, seed_ctx};
use slhdsa::params::Params;
use slhdsa::shake256::shake256;
use slhdsa::util::{base_2b, block, to_int};

// GPU code specializes its arrays, reductions and layouts to FIPS 205 Table 2.
fn validate_geometry<const N: usize>(p: &Params) -> Result<(), MetalError> {
    use slhdsa::params::{SHA2_128F, SHA2_128S, SHA2_192F, SHA2_192S, SHA2_256F, SHA2_256S};
    let row = match (N, p.hp) {
        (16, 3) => SHA2_128F, (16, 9) => SHA2_128S,
        (24, 3) => SHA2_192F, (24, 9) => SHA2_192S,
        (32, 4) => SHA2_256F, (32, 8) => SHA2_256S,
        _ => return Err(MetalError("unsupported SLH-DSA geometry".into())),
    };
    if (p.n, p.h, p.d, p.a, p.k, p.m) != (row.n, row.h, row.d, row.a, row.k, row.m) {
        return Err(MetalError("unsupported SLH-DSA geometry".into()));
    }
    Ok(())
}

// Bound the largest per-item extent in the units actually indexed by MSL
// (signature bytes, or SHA-2 u32 / SHAKE u64 lanes).
fn check_grid(count: usize, stride: usize) -> Result<(), MetalError> {
    if count > u32::MAX as usize / stride {
        return Err(MetalError("batch exceeds Metal's 32-bit index range".into()));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn metal_compiler_agrees_with_rust_on_all_shared_record_layouts() {
        use std::fmt::Write;
        use std::mem::{align_of, offset_of, size_of};
        let mut source = SHADER_SRC.to_owned();
        macro_rules! layout {
            ($name:ident, $($field:ident),+) => {{
                let name = stringify!($name);
                writeln!(source, "static_assert(sizeof({name}) == {}, \"{name} size\");", size_of::<$name>()).unwrap();
                writeln!(source, "static_assert(alignof({name}) == {}, \"{name} alignment\");", align_of::<$name>()).unwrap();
                $(
                    let field = stringify!($field);
                    writeln!(source, "static_assert(__builtin_offsetof({name}, {field}) == {}, \"{name}.{field}\");",
                        offset_of!($name, $field)).unwrap();
                )+
            }};
        }
        layout!(KeyMaterial, sk_seed, state256, state512);
        layout!(ShakeKeyMaterial, sk_seed, pk_seed);
        layout!(XmssTreeDesc, tree, key_idx, layer, target_leaf, auth_byte_off);
        layout!(ForsJobDesc, idx_tree, key_idx, idx_leaf, sig_byte_off, _pad, indices);
        layout!(WotsSignLayerDesc, tree, key_idx, layer, keypair, sig_idx, wots_byte_off, _pad);
        layout!(XmssParams, num_trees, hp, leaves_per_tree, wots_len);
        layout!(ForsParams, num_sigs, k, a, s1, s2, subtrees_per_tree);
        layout!(WotsSignParams, num_layers, d, wots_len);
        MetalContext::new(&source).unwrap();
    }

    #[test]
    fn grid_limits_include_the_last_representable_batch() {
        for stride in [1, 3, 4, 8, 7 * 512 * 35 * 4] {
            let last = u32::MAX as usize / stride;
            assert!(check_grid(last, stride).is_ok());
            assert!(check_grid(last + 1, stride).is_err());
            assert!(check_grid(usize::MAX, stride).is_err());
        }
    }
}

const SHADER_SRC: &str = concat!(
    include_str!("../shaders/slhdsa.metal"),
    "\n",
    include_str!("../shaders/slhdsa_shake.metal"),
);

#[derive(Clone, Copy, PartialEq, Eq)]
enum HashFamily {
    Sha2,
    Shake,
}

// ============================================================================
// Shared C-ABI Structs (matching shaders/slhdsa.metal & slhdsa_shake.metal)
// ============================================================================

#[repr(C)]
#[derive(bytemuck::Pod, bytemuck::Zeroable, Clone, Copy, Default)]
struct KeyMaterial {
    sk_seed: [u32; 8],
    state256: [u32; 8],
    state512: [u64; 8],
}

#[repr(C)]
#[derive(bytemuck::Pod, bytemuck::Zeroable, Clone, Copy, Default)]
struct ShakeKeyMaterial {
    sk_seed: [u64; 4],
    pk_seed: [u64; 4],
}

#[repr(C)]
#[derive(bytemuck::Pod, bytemuck::Zeroable, Clone, Copy, Default)]
struct XmssTreeDesc {
    tree: u64,
    key_idx: u32,
    layer: u32,
    target_leaf: u32,
    auth_byte_off: u32,
}

#[repr(C)]
#[derive(bytemuck::Pod, bytemuck::Zeroable, Clone, Copy)]
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
#[derive(bytemuck::Pod, bytemuck::Zeroable, Clone, Copy, Default)]
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
#[derive(bytemuck::Pod, bytemuck::Zeroable, Clone, Copy)]
struct XmssParams {
    num_trees: u32,
    hp: u32,
    leaves_per_tree: u32,
    wots_len: u32,
}

#[repr(C)]
#[derive(bytemuck::Pod, bytemuck::Zeroable, Clone, Copy)]
struct ForsParams {
    num_sigs: u32,
    k: u32,
    a: u32,
    s1: u32,
    s2: u32,
    subtrees_per_tree: u32,
}

#[repr(C)]
#[derive(bytemuck::Pod, bytemuck::Zeroable, Clone, Copy)]
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
    fn load(ctx: &MetalContext, prefix: &str, suffix: &str) -> Result<Self, MetalError> {
        Ok(Self {
            wots_chains: ctx.pipeline(&format!("{prefix}wots_chains_{suffix}"))?,
            wots_tlen: ctx.pipeline(&format!("{prefix}wots_tlen_{suffix}"))?,
            xmss_leaves_streaming: ctx.pipeline(&format!("{prefix}xmss_leaves_streaming_{suffix}"))?,
            xmss_reduce: ctx.pipeline(&format!("{prefix}xmss_reduce_{suffix}"))?,
            fors_pass1: ctx.pipeline(&format!("{prefix}fors_pass1_{suffix}"))?,
            fors_pass2: ctx.pipeline(&format!("{prefix}fors_pass2_{suffix}"))?,
            fors_pk: ctx.pipeline(&format!("{prefix}fors_pk_{suffix}"))?,
            wots_sign: ctx.pipeline(&format!("{prefix}wots_sign_{suffix}"))?,
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

/// Apple Silicon Metal GPU compute engine for all 12 FIPS 205 SLH-DSA parameter sets
/// (both SHA-2 and SHAKE families).
///
/// Compiles shaders and caches compute pipelines once on creation; safe to reuse
/// across any number of single or batched keygen and signing operations.
pub struct MetalSigner {
    ctx: MetalContext,
    sha2_p16: PipelinesForN,
    sha2_p24: PipelinesForN,
    sha2_p32: PipelinesForN,
    shake_p16: PipelinesForN,
    shake_p24: PipelinesForN,
    shake_p32: PipelinesForN,
    pool: Mutex<ScratchPool>,
    /// Leaf count threshold below which XMSS uses the two-phase per-chain kernel
    /// (`wots_chains` + `wots_tlen`) for maximum GPU thread occupancy; at or above
    /// this threshold it uses the zero-temp-memory `xmss_leaves_streaming` kernel.
    /// Set to `None` to use the Apple Silicon tuned default (`4096` for SHA2-128,
    /// `49152` for SHA2-192/256, and `65536` for SHAKE where splitting 64-bit
    /// Keccak/SHA-512 state halves register pressure).
    pub two_phase_leaf_limit: Option<usize>,
}

impl MetalSigner {
    /// Initializes the default Apple Metal GPU device and compiles all SLH-DSA
    /// SHA-2 and SHAKE compute shaders.
    pub fn new() -> Result<Self, MetalError> {
        let ctx = MetalContext::new(SHADER_SRC)?;
        let sha2_p16 = PipelinesForN::load(&ctx, "", "N16")?;
        let sha2_p24 = PipelinesForN::load(&ctx, "", "N24")?;
        let sha2_p32 = PipelinesForN::load(&ctx, "", "N32")?;
        let shake_p16 = PipelinesForN::load(&ctx, "shake_", "N16")?;
        let shake_p24 = PipelinesForN::load(&ctx, "shake_", "N24")?;
        let shake_p32 = PipelinesForN::load(&ctx, "shake_", "N32")?;
        Ok(Self {
            ctx,
            sha2_p16,
            sha2_p24,
            sha2_p32,
            shake_p16,
            shake_p24,
            shake_p32,
            pool: Mutex::new(ScratchPool::new()),
            two_phase_leaf_limit: None,
        })
    }

    /// Returns the name of the active Metal GPU (e.g. `"Apple M4"`).
    pub fn device_name(&self) -> String {
        self.ctx.device_name()
    }

    /// Returns true if the GPU uses Apple Silicon Unified Memory.
    pub fn has_unified_memory(&self) -> bool {
        self.ctx.has_unified_memory()
    }

    fn pipelines<const N: usize>(&self, family: HashFamily) -> Result<&PipelinesForN, MetalError> {
        match (family, N) {
            (HashFamily::Sha2, 16) => Ok(&self.sha2_p16),
            (HashFamily::Sha2, 24) => Ok(&self.sha2_p24),
            (HashFamily::Sha2, 32) => Ok(&self.sha2_p32),
            (HashFamily::Shake, 16) => Ok(&self.shake_p16),
            (HashFamily::Shake, 24) => Ok(&self.shake_p24),
            (HashFamily::Shake, 32) => Ok(&self.shake_p32),
            _ => Err(MetalError(format!("unsupported SLH-DSA N={N}"))),
        }
    }

    fn use_two_phase<const N: usize>(&self, family: HashFamily, total_leaves: usize) -> bool {
        let limit = self.two_phase_leaf_limit.unwrap_or(match (family, N) {
            (HashFamily::Sha2, 16) => 4096,
            (HashFamily::Sha2, _) => 49152,
            (HashFamily::Shake, _) => 65536,
        });
        total_leaves < limit
    }

    // ------------------------------------------------------------------------
    // SHA-2 Keygen & Signing Public API
    // ------------------------------------------------------------------------

    /// Algorithm 18, `slh_keygen_internal` (SHA-2) on Metal GPU.
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

    /// Algorithm 21, `slh_keygen` (SHA-2) on Metal GPU, writing into `sk` (4N) and `pk` (2N).
    pub fn keygen<const N: usize>(
        &self,
        p: &Params,
        seeds: &[u8],
        sk: &mut [u8],
        pk: &mut [u8],
    ) -> Result<(), MetalError> {
        self.keygen_family::<N>(HashFamily::Sha2, p, seeds, sk, pk)
    }

    /// Batch key generation (SHA-2) in a single Metal GPU command buffer.
    pub fn keygen_internal_batch<const N: usize>(
        &self,
        p: &Params,
        batch: &[([u8; N], [u8; N], [u8; N])],
    ) -> Result<Vec<(Vec<u8>, Vec<u8>)>, MetalError> {
        self.keygen_internal_batch_family::<N>(HashFamily::Sha2, p, batch)
    }

    /// Algorithm 19, `slh_sign_internal` (SHA-2) on Metal GPU.
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

    /// Algorithm 22, `slh_sign` (SHA-2, pure hedged signing) on Metal GPU.
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

    /// Algorithm 22, `slh_sign` (SHA-2, pure deterministic signing) on Metal GPU.
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

    /// Batch pure-mode signing (SHA-2) in a single Metal GPU command buffer.
    pub fn sign_batch<const N: usize>(
        &self,
        p: &Params,
        requests: &[SignReq<'_, N>],
    ) -> Result<Option<Vec<Vec<u8>>>, MetalError> {
        self.sign_batch_family::<N>(HashFamily::Sha2, p, requests)
    }

    /// Same-key batch hedged signing (SHA-2) in a single Metal GPU command buffer.
    pub fn sign_batch_same_key<const N: usize>(
        &self,
        p: &Params,
        sk: &[u8],
        messages: &[&[u8]],
        ctx: &[u8],
        addrnds: &[&[u8; N]],
    ) -> Result<Option<Vec<Vec<u8>>>, MetalError> {
        self.sign_batch_same_key_family::<N>(HashFamily::Sha2, p, sk, messages, ctx, addrnds)
    }

    /// Same-key batch deterministic signing (SHA-2) in a single Metal GPU command buffer.
    pub fn sign_deterministic_batch_same_key<const N: usize>(
        &self,
        p: &Params,
        sk: &[u8],
        messages: &[&[u8]],
        ctx: &[u8],
    ) -> Result<Option<Vec<Vec<u8>>>, MetalError> {
        self.sign_deterministic_batch_same_key_family::<N>(HashFamily::Sha2, p, sk, messages, ctx)
    }

    /// Batch internal-mode signing (SHA-2) in ONE single Metal GPU command buffer.
    pub fn sign_internal_batch<const N: usize>(
        &self,
        p: &Params,
        requests: &[SignInternalReq<'_, N>],
    ) -> Result<Vec<Vec<u8>>, MetalError> {
        self.sign_internal_batch_family::<N>(HashFamily::Sha2, p, requests)
    }

    // ------------------------------------------------------------------------
    // SHAKE Keygen & Signing Public API
    // ------------------------------------------------------------------------

    /// Algorithm 18, `slh_keygen_internal` (SHAKE) on Metal GPU.
    pub fn shake_keygen_internal<const N: usize>(
        &self,
        p: &Params,
        sk_seed: &[u8; N],
        sk_prf: &[u8; N],
        pk_seed: &[u8; N],
    ) -> Result<(Vec<u8>, Vec<u8>), MetalError> {
        let mut res = self.shake_keygen_internal_batch::<N>(p, &[(*sk_seed, *sk_prf, *pk_seed)])?;
        Ok(res.pop().unwrap())
    }

    /// Algorithm 21, `slh_keygen` (SHAKE) on Metal GPU, writing into `sk` (4N) and `pk` (2N).
    pub fn shake_keygen<const N: usize>(
        &self,
        p: &Params,
        seeds: &[u8],
        sk: &mut [u8],
        pk: &mut [u8],
    ) -> Result<(), MetalError> {
        self.keygen_family::<N>(HashFamily::Shake, p, seeds, sk, pk)
    }

    /// Batch key generation (SHAKE) in a single Metal GPU command buffer.
    pub fn shake_keygen_internal_batch<const N: usize>(
        &self,
        p: &Params,
        batch: &[([u8; N], [u8; N], [u8; N])],
    ) -> Result<Vec<(Vec<u8>, Vec<u8>)>, MetalError> {
        self.keygen_internal_batch_family::<N>(HashFamily::Shake, p, batch)
    }

    /// Algorithm 19, `slh_sign_internal` (SHAKE) on Metal GPU.
    pub fn shake_sign_internal<const N: usize>(
        &self,
        p: &Params,
        m: &[u8],
        sk: &[u8],
        addrnd: &[u8; N],
    ) -> Result<Vec<u8>, MetalError> {
        let mut sigs = self.shake_sign_internal_batch::<N>(
            p,
            &[SignInternalReq {
                msg: m,
                sk,
                addrnd,
            }],
        )?;
        Ok(sigs.pop().unwrap())
    }

    /// Algorithm 22, `slh_sign` (SHAKE, pure hedged signing) on Metal GPU.
    pub fn shake_sign<const N: usize>(
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
        self.shake_sign_internal::<N>(p, &mp, sk, addrnd).map(Some)
    }

    /// Algorithm 22, `slh_sign` (SHAKE, pure deterministic signing) on Metal GPU.
    pub fn shake_sign_deterministic<const N: usize>(
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
        self.shake_sign::<N>(p, m, ctx, sk, &pk_seed)
    }

    /// Batch pure-mode signing (SHAKE) in a single Metal GPU command buffer.
    pub fn shake_sign_batch<const N: usize>(
        &self,
        p: &Params,
        requests: &[SignReq<'_, N>],
    ) -> Result<Option<Vec<Vec<u8>>>, MetalError> {
        self.sign_batch_family::<N>(HashFamily::Shake, p, requests)
    }

    /// Same-key batch hedged signing (SHAKE) in a single Metal GPU command buffer.
    pub fn shake_sign_batch_same_key<const N: usize>(
        &self,
        p: &Params,
        sk: &[u8],
        messages: &[&[u8]],
        ctx: &[u8],
        addrnds: &[&[u8; N]],
    ) -> Result<Option<Vec<Vec<u8>>>, MetalError> {
        self.sign_batch_same_key_family::<N>(HashFamily::Shake, p, sk, messages, ctx, addrnds)
    }

    /// Same-key batch deterministic signing (SHAKE) in a single Metal GPU command buffer.
    pub fn shake_sign_deterministic_batch_same_key<const N: usize>(
        &self,
        p: &Params,
        sk: &[u8],
        messages: &[&[u8]],
        ctx: &[u8],
    ) -> Result<Option<Vec<Vec<u8>>>, MetalError> {
        self.sign_deterministic_batch_same_key_family::<N>(HashFamily::Shake, p, sk, messages, ctx)
    }

    /// Batch internal-mode signing (SHAKE) in ONE single Metal GPU command buffer.
    pub fn shake_sign_internal_batch<const N: usize>(
        &self,
        p: &Params,
        requests: &[SignInternalReq<'_, N>],
    ) -> Result<Vec<Vec<u8>>, MetalError> {
        self.sign_internal_batch_family::<N>(HashFamily::Shake, p, requests)
    }

    // ------------------------------------------------------------------------
    // Unified Family Implementation (SHA-2 and SHAKE)
    // ------------------------------------------------------------------------

    fn keygen_family<const N: usize>(
        &self,
        family: HashFamily,
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
        let mut res = self.keygen_internal_batch_family::<N>(family, p, &[(sk_seed, sk_prf, pk_seed)])?;
        let (sk_out, pk_out) = res.pop().unwrap();
        sk.copy_from_slice(&sk_out);
        pk.copy_from_slice(&pk_out);
        Ok(())
    }

    fn keygen_internal_batch_family<const N: usize>(
        &self,
        family: HashFamily,
        p: &Params,
        batch: &[([u8; N], [u8; N], [u8; N])],
    ) -> Result<Vec<(Vec<u8>, Vec<u8>)>, MetalError> {
        validate_geometry::<N>(p)?;
        let count = batch.len();
        if count == 0 {
            return Ok(Vec::new());
        }

        let pipes = self.pipelines::<N>(family)?;
        let leaves_per_tree = 1usize << p.hp;
        let words = N / if family == HashFamily::Shake { 8 } else { 4 };
        check_grid(count, leaves_per_tree * words)?;
        let total_leaves = count * leaves_per_tree;
        let wots_len = p.len();
        let use_two_phase = self.use_two_phase::<N>(family, total_leaves);
        if use_two_phase {
            check_grid(count, leaves_per_tree * wots_len * words)?;
        }

        let mut pool = self.pool.lock().unwrap();
        let trees_bytes = count * std::mem::size_of::<XmssTreeDesc>();
        let leaves_bytes = total_leaves * N;
        let roots_bytes = count * N;

        match family {
            HashFamily::Sha2 => {
                let keys_bytes = count * std::mem::size_of::<KeyMaterial>();
                let keys_buf = ScratchPool::ensure(&self.ctx, &mut pool.keys, keys_bytes, true)?;
                let km_slice = keys_buf.as_mut_slice_of::<KeyMaterial>(count);
                for (i, (sk_seed, _sk_prf, pk_seed)) in batch.iter().enumerate() {
                    km_slice[i] = build_key_material::<N>(sk_seed, pk_seed);
                }
            }
            HashFamily::Shake => {
                let keys_bytes = count * std::mem::size_of::<ShakeKeyMaterial>();
                let keys_buf = ScratchPool::ensure(&self.ctx, &mut pool.keys, keys_bytes, true)?;
                let km_slice = keys_buf.as_mut_slice_of::<ShakeKeyMaterial>(count);
                for (i, (sk_seed, _sk_prf, pk_seed)) in batch.iter().enumerate() {
                    km_slice[i] = build_shake_key_material::<N>(sk_seed, pk_seed);
                }
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
        // SAFETY for the dispatches below: the pool guard retains exclusive host
        // access through completion. Kernel bindings use the matching family and
        // width, with allocations sized above for the validated geometry and grid.
        if use_two_phase {
            let tips_buf = pool.chain_tips.as_ref().unwrap();
            let total_chains = (total_leaves * wots_len) as u32;
            let tg_chains = choose_tg_size(&pipes.wots_chains, total_chains);
            unsafe {
                cmd.dispatch_threads(
                    &pipes.wots_chains,
                    &[keys_buf, trees_buf, tips_buf],
                    &[InlineBytes::of(3, &xmss_params)],
                    total_chains,
                    tg_chains,
                    0,
                );
            }
            let tg_tlen = choose_tg_size(&pipes.wots_tlen, total_leaves as u32);
            unsafe {
                cmd.dispatch_threads(
                    &pipes.wots_tlen,
                    &[keys_buf, trees_buf, tips_buf, leaves_buf],
                    &[InlineBytes::of(4, &xmss_params)],
                    total_leaves as u32,
                    tg_tlen,
                    0,
                );
            }
        } else {
            let tg_leaves = choose_tg_size(&pipes.xmss_leaves_streaming, total_leaves as u32);
            unsafe {
                cmd.dispatch_threads(
                    &pipes.xmss_leaves_streaming,
                    &[keys_buf, trees_buf, leaves_buf],
                    &[InlineBytes::of(3, &xmss_params)],
                    total_leaves as u32,
                    tg_leaves,
                    0,
                );
            }
        }

        let reduce_tg = 1u32 << (p.hp - 1);
        let reduce_tg_mem = reduce_tg * (N as u32);
        unsafe {
            cmd.dispatch_threadgroups(
                &pipes.xmss_reduce,
                &[keys_buf, trees_buf, leaves_buf, roots_buf, out_sigs_buf],
                &[InlineBytes::of(5, &xmss_params)],
                count as u32,
                reduce_tg,
                reduce_tg_mem,
            );
        }

        let gpu_res = cmd.commit_and_wait();
        pool.keys.as_mut().unwrap().zeroize_contents();
        gpu_res?;

        let mut out = Vec::with_capacity(count);
        match family {
            HashFamily::Sha2 => {
                let nw = N / 4;
                let roots_words = pool.xmss_roots.as_ref().unwrap().as_slice_of::<u32>(count * nw);
                for (i, (sk_seed, sk_prf, pk_seed)) in batch.iter().enumerate() {
                    let pk_root = words_to_bytes::<N>(&roots_words[i * nw..(i + 1) * nw]);
                    out.push(pack_keypair(sk_seed, sk_prf, pk_seed, &pk_root));
                }
            }
            HashFamily::Shake => {
                let nl = N / 8;
                let roots_lanes = pool.xmss_roots.as_ref().unwrap().as_slice_of::<u64>(count * nl);
                for (i, (sk_seed, sk_prf, pk_seed)) in batch.iter().enumerate() {
                    let pk_root = lanes_to_bytes::<N>(&roots_lanes[i * nl..(i + 1) * nl]);
                    out.push(pack_keypair(sk_seed, sk_prf, pk_seed, &pk_root));
                }
            }
        }
        Ok(out)
    }

    fn sign_batch_family<const N: usize>(
        &self,
        family: HashFamily,
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
        self.sign_internal_batch_family::<N>(family, p, &internal_reqs)
            .map(Some)
    }

    fn sign_batch_same_key_family<const N: usize>(
        &self,
        family: HashFamily,
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
        self.sign_batch_family::<N>(family, p, &reqs)
    }

    fn sign_deterministic_batch_same_key_family<const N: usize>(
        &self,
        family: HashFamily,
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
        self.sign_batch_family::<N>(family, p, &reqs)
    }

    fn sign_internal_batch_family<const N: usize>(
        &self,
        family: HashFamily,
        p: &Params,
        requests: &[SignInternalReq<'_, N>],
    ) -> Result<Vec<Vec<u8>>, MetalError> {
        validate_geometry::<N>(p)?;
        let num_sigs = requests.len();
        if num_sigs == 0 {
            return Ok(Vec::new());
        }

        let pipes = self.pipelines::<N>(family)?;
        let sig_bytes = p.sig_bytes();
        let fors_sig_bytes = p.fors_sig_bytes();
        let xmss_sig_bytes = p.xmss_sig_bytes();
        let wots_len = p.len();
        let d = p.d as usize;
        let hp = p.hp;
        let leaves_per_tree = 1usize << hp;
        let words = N / if family == HashFamily::Shake { 8 } else { 4 };
        check_grid(num_sigs, sig_bytes.max(d * leaves_per_tree * words))?;
        let total_trees = num_sigs * d;
        let total_xmss_leaves = total_trees * leaves_per_tree;
        let use_two_phase = self.use_two_phase::<N>(family, total_xmss_leaves);

        // FORS two-pass split: s1 <= 8 (max 128 threads/TG with 2-leaf), s2 <= 7
        let s1 = if p.a <= 8 { p.a } else { 7 };
        let s2 = p.a - s1;
        let subtrees_per_tree = 1u32 << s2;
        check_grid(num_sigs, p.k as usize * subtrees_per_tree as usize * words)?;
        if use_two_phase {
            check_grid(num_sigs, d * leaves_per_tree * wots_len * words)?;
        }

        // CPU preprocessing: deduplicate keys + compute R, H_msg, FORS indices, HT descriptors
        let mut unique_seeds: Vec<([u8; N], [u8; N])> = Vec::new();
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

            let key_idx = match unique_seeds
                .iter()
                .position(|(ss, ps)| ss == &sk_seed && ps == &pk_seed)
            {
                Some(idx) => idx as u32,
                None => {
                    unique_seeds.push((sk_seed, pk_seed));
                    (unique_seeds.len() - 1) as u32
                }
            };

            let (r, digest) = match family {
                HashFamily::Sha2 => {
                    let r = prf_msg::<N>(&sk_prf, req.addrnd, req.msg);
                    let digest = h_msg::<N>(p, &r, &pk_seed, &pk_root, req.msg);
                    (r, digest)
                }
                HashFamily::Shake => {
                    let r = shake_prf_msg::<N>(&sk_prf, req.addrnd, req.msg);
                    let digest = shake_h_msg::<N>(p, &r, &pk_seed, &pk_root, req.msg);
                    (r, digest)
                }
            };

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
        let num_keys = unique_seeds.len();

        match family {
            HashFamily::Sha2 => {
                let keys_buf = ScratchPool::ensure(
                    &self.ctx,
                    &mut pool.keys,
                    num_keys * std::mem::size_of::<KeyMaterial>(),
                    true,
                )?;
                let km_slice = keys_buf.as_mut_slice_of::<KeyMaterial>(num_keys);
                for (i, (sk_seed, pk_seed)) in unique_seeds.iter().enumerate() {
                    km_slice[i] = build_key_material::<N>(sk_seed, pk_seed);
                }
            }
            HashFamily::Shake => {
                let keys_buf = ScratchPool::ensure(
                    &self.ctx,
                    &mut pool.keys,
                    num_keys * std::mem::size_of::<ShakeKeyMaterial>(),
                    true,
                )?;
                let km_slice = keys_buf.as_mut_slice_of::<ShakeKeyMaterial>(num_keys);
                for (i, (sk_seed, pk_seed)) in unique_seeds.iter().enumerate() {
                    km_slice[i] = build_shake_key_material::<N>(sk_seed, pk_seed);
                }
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

        let mut cmd = self.ctx.begin_cmd(true)?;
        // SAFETY for the dispatches below: the pool guard retains exclusive host
        // access through completion. Kernel bindings use the matching family and
        // width, with allocations sized above for the validated geometry and grid.

        // Stage 1: Launch XMSS leaves + FORS Pass 1 concurrently!
        if use_two_phase {
            let tips_buf = pool.chain_tips.as_ref().unwrap();
            let total_chains = (total_xmss_leaves * wots_len) as u32;
            let tg_chains = choose_tg_size(&pipes.wots_chains, total_chains);
            unsafe {
                cmd.dispatch_threads(
                    &pipes.wots_chains,
                    &[keys_buf, trees_buf, tips_buf],
                    &[InlineBytes::of(3, &xmss_params)],
                    total_chains,
                    tg_chains,
                    0,
                );
            }
        } else {
            let tg_leaves = choose_tg_size(&pipes.xmss_leaves_streaming, total_xmss_leaves as u32);
            unsafe {
                cmd.dispatch_threads(
                    &pipes.xmss_leaves_streaming,
                    &[keys_buf, trees_buf, leaves_buf],
                    &[InlineBytes::of(3, &xmss_params)],
                    total_xmss_leaves as u32,
                    tg_leaves,
                    0,
                );
            }
        }

        let fors1_tgs = (num_sigs as u32) * p.k * subtrees_per_tree;
        let fors1_tg_x = 1u32 << (s1 - 1);
        let fors1_tg_mem = fors1_tg_x * (N as u32);
        unsafe {
            cmd.dispatch_threadgroups(
                &pipes.fors_pass1,
                &[keys_buf, fjobs_buf, fsub_buf, out_sigs_buf],
                &[InlineBytes::of(4, &fors_params)],
                fors1_tgs,
                fors1_tg_x,
                fors1_tg_mem,
            );
        }

        cmd.barrier();

        // Stage 2: XMSS (wots_tlen or xmss_reduce) + FORS (fors_pass2 or fors_pk)
        if use_two_phase {
            let tips_buf = pool.chain_tips.as_ref().unwrap();
            let tg_tlen = choose_tg_size(&pipes.wots_tlen, total_xmss_leaves as u32);
            unsafe {
                cmd.dispatch_threads(
                    &pipes.wots_tlen,
                    &[keys_buf, trees_buf, tips_buf, leaves_buf],
                    &[InlineBytes::of(4, &xmss_params)],
                    total_xmss_leaves as u32,
                    tg_tlen,
                    0,
                );
            }
        } else {
            let reduce_tg = 1u32 << (hp - 1);
            let reduce_tg_mem = reduce_tg * (N as u32);
            unsafe {
                cmd.dispatch_threadgroups(
                    &pipes.xmss_reduce,
                    &[keys_buf, trees_buf, leaves_buf, roots_buf, out_sigs_buf],
                    &[InlineBytes::of(5, &xmss_params)],
                    total_trees as u32,
                    reduce_tg,
                    reduce_tg_mem,
                );
            }
        }

        if s2 > 0 {
            let fors2_tgs = (num_sigs as u32) * p.k;
            let fors2_tg_x = 1u32 << (s2 - 1);
            let fors2_tg_mem = fors2_tg_x * (N as u32);
            unsafe {
                cmd.dispatch_threadgroups(
                    &pipes.fors_pass2,
                    &[keys_buf, fjobs_buf, fsub_buf, froots_buf, out_sigs_buf],
                    &[InlineBytes::of(5, &fors_params)],
                    fors2_tgs,
                    fors2_tg_x,
                    fors2_tg_mem,
                );
            }
        } else {
            let tg_fpk = choose_tg_size(&pipes.fors_pk, num_sigs as u32);
            unsafe {
                cmd.dispatch_threads(
                    &pipes.fors_pk,
                    &[keys_buf, fjobs_buf, froots_buf, pk_fors_buf],
                    &[InlineBytes::of(4, &fors_params)],
                    num_sigs as u32,
                    tg_fpk,
                    0,
                );
            }
        }

        cmd.barrier();

        // Stage 3: finish xmss_reduce (if two-phase) and/or fors_pk (if s2 > 0)
        let mut need_stage3_barrier = false;
        if use_two_phase {
            let reduce_tg = 1u32 << (hp - 1);
            let reduce_tg_mem = reduce_tg * (N as u32);
            unsafe {
                cmd.dispatch_threadgroups(
                    &pipes.xmss_reduce,
                    &[keys_buf, trees_buf, leaves_buf, roots_buf, out_sigs_buf],
                    &[InlineBytes::of(5, &xmss_params)],
                    total_trees as u32,
                    reduce_tg,
                    reduce_tg_mem,
                );
            }
            need_stage3_barrier = true;
        }
        if s2 > 0 {
            let tg_fpk = choose_tg_size(&pipes.fors_pk, num_sigs as u32);
            unsafe {
                cmd.dispatch_threads(
                    &pipes.fors_pk,
                    &[keys_buf, fjobs_buf, froots_buf, pk_fors_buf],
                    &[InlineBytes::of(4, &fors_params)],
                    num_sigs as u32,
                    tg_fpk,
                    0,
                );
            }
            need_stage3_barrier = true;
        }
        if need_stage3_barrier {
            cmd.barrier();
        }

        // Final Stage: WOTS+ signatures for all B * d layers written directly into out_sigs!
        let total_wots_chains = (total_trees * wots_len) as u32;
        let tg_wsig = choose_tg_size(&pipes.wots_sign, total_wots_chains);
        unsafe {
            cmd.dispatch_threads(
                &pipes.wots_sign,
                &[keys_buf, wlayers_buf, pk_fors_buf, roots_buf, out_sigs_buf],
                &[InlineBytes::of(5, &wots_sign_params)],
                total_wots_chains,
                tg_wsig,
                0,
            );
        }

        let gpu_res = cmd.commit_and_wait();
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

fn build_shake_key_material<const N: usize>(sk_seed: &[u8; N], pk_seed: &[u8; N]) -> ShakeKeyMaterial {
    let mut sk_lanes = [0u64; 4];
    let mut pk_lanes = [0u64; 4];
    for i in 0..(N / 8) {
        sk_lanes[i] = u64::from_le_bytes(sk_seed[8 * i..8 * i + 8].try_into().unwrap());
        pk_lanes[i] = u64::from_le_bytes(pk_seed[8 * i..8 * i + 8].try_into().unwrap());
    }
    ShakeKeyMaterial {
        sk_seed: sk_lanes,
        pk_seed: pk_lanes,
    }
}

fn words_to_bytes<const N: usize>(words: &[u32]) -> [u8; N] {
    let mut out = [0u8; N];
    for i in 0..(N / 4) {
        out[4 * i..4 * i + 4].copy_from_slice(&words[i].to_be_bytes());
    }
    out
}

fn lanes_to_bytes<const N: usize>(lanes: &[u64]) -> [u8; N] {
    let mut out = [0u8; N];
    for i in 0..(N / 8) {
        out[8 * i..8 * i + 8].copy_from_slice(&lanes[i].to_le_bytes());
    }
    out
}

fn pack_keypair<const N: usize>(
    sk_seed: &[u8; N],
    sk_prf: &[u8; N],
    pk_seed: &[u8; N],
    pk_root: &[u8; N],
) -> (Vec<u8>, Vec<u8>) {
    let mut sk = Vec::with_capacity(4 * N);
    sk.extend_from_slice(sk_seed);
    sk.extend_from_slice(sk_prf);
    sk.extend_from_slice(pk_seed);
    sk.extend_from_slice(pk_root);
    let mut pk = Vec::with_capacity(2 * N);
    pk.extend_from_slice(pk_seed);
    pk.extend_from_slice(pk_root);
    (sk, pk)
}

fn shake_prf_msg<const N: usize>(sk_prf: &[u8; N], opt_rand: &[u8; N], msg: &[u8]) -> [u8; N] {
    let mut input = Vec::with_capacity(2 * N + msg.len());
    input.extend_from_slice(sk_prf);
    input.extend_from_slice(opt_rand);
    input.extend_from_slice(msg);
    let mut out = [0u8; N];
    shake256(&input, &mut out);
    out
}

fn shake_h_msg<const N: usize>(
    p: &Params,
    r: &[u8; N],
    pk_seed: &[u8; N],
    pk_root: &[u8; N],
    msg: &[u8],
) -> Vec<u8> {
    let mut input = Vec::with_capacity(3 * N + msg.len());
    input.extend_from_slice(r);
    input.extend_from_slice(pk_seed);
    input.extend_from_slice(pk_root);
    input.extend_from_slice(msg);
    let mut out = vec![0u8; p.m];
    shake256(&input, &mut out);
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
// Typed Per-Set Convenience Modules (All 12 SHA-2 & SHAKE Parameter Sets)
// ============================================================================

macro_rules! metal_set {
    ($mod_name:ident, $slh_mod:ident, $kg_int:ident, $kg:ident, $sg_int:ident, $sg:ident, $sg_det:ident, $sg_batch:ident, $sg_det_batch:ident) => {
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
                let (sk, pk) = gpu.$kg_int::<N>(&PARAMS, sk_seed, sk_prf, pk_seed)?;
                Ok((sk.try_into().unwrap(), pk.try_into().unwrap()))
            }

            pub fn keygen(
                gpu: &MetalSigner,
                seeds: &[u8; SEED_BYTES],
                sk: &mut [u8; SK_BYTES],
                pk: &mut [u8; PK_BYTES],
            ) -> Result<(), MetalError> {
                gpu.$kg::<N>(&PARAMS, seeds, sk, pk)
            }

            pub fn sign_internal(
                gpu: &MetalSigner,
                m: &[u8],
                sk: &[u8; SK_BYTES],
                addrnd: &[u8; N],
            ) -> Result<Vec<u8>, MetalError> {
                gpu.$sg_int::<N>(&PARAMS, m, sk, addrnd)
            }

            pub fn sign(
                gpu: &MetalSigner,
                m: &[u8],
                ctx: &[u8],
                sk: &[u8; SK_BYTES],
                addrnd: &[u8; N],
            ) -> Result<Option<Vec<u8>>, MetalError> {
                gpu.$sg::<N>(&PARAMS, m, ctx, sk, addrnd)
            }

            pub fn sign_deterministic(
                gpu: &MetalSigner,
                m: &[u8],
                ctx: &[u8],
                sk: &[u8; SK_BYTES],
            ) -> Result<Option<Vec<u8>>, MetalError> {
                gpu.$sg_det::<N>(&PARAMS, m, ctx, sk)
            }

            pub fn sign_batch_same_key(
                gpu: &MetalSigner,
                sk: &[u8; SK_BYTES],
                messages: &[&[u8]],
                ctx: &[u8],
                addrnds: &[&[u8; N]],
            ) -> Result<Option<Vec<Vec<u8>>>, MetalError> {
                gpu.$sg_batch::<N>(&PARAMS, sk, messages, ctx, addrnds)
            }

            pub fn sign_deterministic_batch_same_key(
                gpu: &MetalSigner,
                sk: &[u8; SK_BYTES],
                messages: &[&[u8]],
                ctx: &[u8],
            ) -> Result<Option<Vec<Vec<u8>>>, MetalError> {
                gpu.$sg_det_batch::<N>(&PARAMS, sk, messages, ctx)
            }

            pub fn verify(m: &[u8], sig: &[u8], ctx: &[u8], pk: &[u8; PK_BYTES]) -> bool {
                slhdsa::$slh_mod::verify(m, sig, ctx, pk)
            }
        }
    };
}

metal_set!(sha2_128s, sha2_128s, keygen_internal, keygen, sign_internal, sign, sign_deterministic, sign_batch_same_key, sign_deterministic_batch_same_key);
metal_set!(sha2_128f, sha2_128f, keygen_internal, keygen, sign_internal, sign, sign_deterministic, sign_batch_same_key, sign_deterministic_batch_same_key);
metal_set!(sha2_192s, sha2_192s, keygen_internal, keygen, sign_internal, sign, sign_deterministic, sign_batch_same_key, sign_deterministic_batch_same_key);
metal_set!(sha2_192f, sha2_192f, keygen_internal, keygen, sign_internal, sign, sign_deterministic, sign_batch_same_key, sign_deterministic_batch_same_key);
metal_set!(sha2_256s, sha2_256s, keygen_internal, keygen, sign_internal, sign, sign_deterministic, sign_batch_same_key, sign_deterministic_batch_same_key);
metal_set!(sha2_256f, sha2_256f, keygen_internal, keygen, sign_internal, sign, sign_deterministic, sign_batch_same_key, sign_deterministic_batch_same_key);

metal_set!(shake_128s, shake_128s, shake_keygen_internal, shake_keygen, shake_sign_internal, shake_sign, shake_sign_deterministic, shake_sign_batch_same_key, shake_sign_deterministic_batch_same_key);
metal_set!(shake_128f, shake_128f, shake_keygen_internal, shake_keygen, shake_sign_internal, shake_sign, shake_sign_deterministic, shake_sign_batch_same_key, shake_sign_deterministic_batch_same_key);
metal_set!(shake_192s, shake_192s, shake_keygen_internal, shake_keygen, shake_sign_internal, shake_sign, shake_sign_deterministic, shake_sign_batch_same_key, shake_sign_deterministic_batch_same_key);
metal_set!(shake_192f, shake_192f, shake_keygen_internal, shake_keygen, shake_sign_internal, shake_sign, shake_sign_deterministic, shake_sign_batch_same_key, shake_sign_deterministic_batch_same_key);
metal_set!(shake_256s, shake_256s, shake_keygen_internal, shake_keygen, shake_sign_internal, shake_sign, shake_sign_deterministic, shake_sign_batch_same_key, shake_sign_deterministic_batch_same_key);
metal_set!(shake_256f, shake_256f, shake_keygen_internal, shake_keygen, shake_sign_internal, shake_sign, shake_sign_deterministic, shake_sign_batch_same_key, shake_sign_deterministic_batch_same_key);
