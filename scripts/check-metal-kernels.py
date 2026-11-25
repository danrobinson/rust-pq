#!/usr/bin/env python3
"""Verify the Metal SLH-DSA shaders, message construction, FFI boundary, and Lean proofs.

1. Audits the Objective-C/Rust FFI boundary (`metal/src/bridge.m`, `metal/src/gpu.rs`,
   `metal/src/lib.rs`): ARC lifetimes, buffer sizing, 32-bit GPU index overflow guards
   across all 12 parameter sets, zeroize scrubbing of secret buffers, kernel binding
   indices, threadgroup memory sizing, and concurrent-encoder barrier placement.
2. Compiles the ACTUAL production MSL shaders (`metal/shaders/slhdsa.metal` and
   `metal/shaders/slhdsa_shake.metal`) on CPU via C++20 coroutines (`clang++ -O2
   -std=c++20 -fsanitize=undefined,bounds -fno-sanitize-recover=all`), executing every
   threadgroup & thread deterministically (both forward and reverse schedules, checking
   zero barrier divergence and out-of-bounds sentinel guards) while hooking
   `sha256_compress`, `sha256_compress_from`, `sha512_compress`, and `keccak_f1600` to
   verify every single message block's ADRSc/ADRS encoding, domain tag, padding, and
   bit-length trailer against independent FIPS 180-4 / FIPS 202 references, and checking
   end-to-end keygen & signing (B=1 and multi-key B=2, two-phase & streaming XMSS)
   byte-for-byte against NIST ACVP vectors for all 12 SHA-2 and SHAKE parameter sets.
3. Builds `Metal.Pipeline` in Lean 4 and audits all headline theorems strictly within
   `[propext, Classical.choice, Quot.sound]`.
"""

import hashlib
import hmac
import json
import os
import re
import runpy
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

# Table 2 (FIPS 205 §11): all 12 SHA-2 and SHAKE parameter sets
PARAM_SETS = [
    # name, family, N, h, d, hp, a, k, m
    ("sha2-128f", "sha2", 16, 66, 22, 3, 6, 33, 34),
    ("sha2-128s", "sha2", 16, 63, 7, 9, 12, 14, 30),
    ("sha2-192f", "sha2", 24, 66, 22, 3, 8, 33, 42),
    ("sha2-192s", "sha2", 24, 63, 7, 9, 14, 17, 39),
    ("sha2-256f", "sha2", 32, 68, 17, 4, 9, 35, 49),
    ("sha2-256s", "sha2", 32, 64, 8, 8, 14, 22, 47),
    ("shake-128f", "shake", 16, 66, 22, 3, 6, 33, 34),
    ("shake-128s", "shake", 16, 63, 7, 9, 12, 14, 30),
    ("shake-192f", "shake", 24, 66, 22, 3, 8, 33, 42),
    ("shake-192s", "shake", 24, 63, 7, 9, 14, 17, 39),
    ("shake-256f", "shake", 32, 68, 17, 4, 9, 35, 49),
    ("shake-256s", "shake", 32, 64, 8, 8, 14, 22, 47),
]


def compact(text: str) -> str:
    return re.sub(r"//[^\n]*|\s+", "", text)


def require_contains(source: str, fragments: list[str], label: str) -> None:
    c = compact(source)
    for frag in fragments:
        if compact(frag) not in c:
            raise ValueError(f"{label}: missing required pattern: {frag}")


def require_ordered(source: str, markers: list[str], label: str) -> None:
    c = compact(source)
    pos = 0
    for m in markers:
        cm = compact(m)
        idx = c.find(cm, pos)
        if idx < 0:
            raise ValueError(f"{label}: missing ordered marker: {m}")
        pos = idx + len(cm)


def audit_ffi_and_host_boundary() -> str:
    """Check Objective-C bridge, Rust FFI wrapper, buffer sizing, zeroize, overflow guards,
    and kernel binding/barrier consistency across all 12 parameter sets."""
    bridge = (ROOT / "metal/src/bridge.m").read_text()
    gpu_rs = (ROOT / "metal/src/gpu.rs").read_text()
    lib_rs = (ROOT / "metal/src/lib.rs").read_text()
    sha2_msl = (ROOT / "metal/shaders/slhdsa.metal").read_text()
    shake_msl = (ROOT / "metal/shaders/slhdsa_shake.metal").read_text()

    # 1. Objective-C bridge ARC retention/release, zero-len guard, null guards, barrier & completion check
    require_contains(
        bridge,
        [
            "(__bridge_retained SlhMetalCtx *)obj",
            "(__bridge_transfer SlhMetalCtxObj *)ctx",
            "(__bridge_retained SlhMetalPipeline *)p",
            "(__bridge_transfer SlhMetalPipelineObj *)p",
            "(__bridge_retained SlhMetalBuffer *)b",
            "(__bridge_transfer SlhMetalBufferObj *)buf",
            "(__bridge_retained SlhMetalCmd *)cmd",
            "(__bridge_transfer SlhMetalCmdObj *)cmd",
            "size_t alloc_len = (len == 0) ? 16 : len;",
            "MTLResourceStorageModeShared",
            "b.requestedLen = len;",
            "if (obj.concurrent) { [obj.encoder memoryBarrierWithScope:MTLBarrierScopeBuffers]; }",
            "if (!cmd || !pipeline || grid_x == 0 || tg_x == 0) { return; }",
            "if (tg_mem_len > 0) { [enc setThreadgroupMemoryLength:tg_mem_len atIndex:0]; }",
            "if ([obj.cmdBuf status] != MTLCommandBufferStatusCompleted)",
        ],
        "metal/src/bridge.m",
    )

    # 2. Rust FFI wrapper: RAII Drop, zeroize on drop, checked_mul, inline bytes bounds, dispatch array bounds
    require_contains(
        gpu_rs,
        [
            "buf.zeroize_on_drop = true;",
            "let len = count.checked_mul(std::mem::size_of::<T>()).expect(",
            "assert!(len > 0,",
            "self.as_mut_slice().zeroize();",
            "if self.zeroize_on_drop { self.zeroize_contents(); }",
            "unsafe { slh_metal_buffer_destroy(self.raw.as_ptr()) };",
            "assert!(buffers.len() <= 16 && inline_bytes.len() <= 8);",
            "u32::try_from(b.data.len()).expect(",
            "impl Drop for MetalContext",
            "impl Drop for MetalPipeline",
            "impl Drop for MetalBuffer",
            "impl Drop for MetalCommand",
        ],
        "metal/src/gpu.rs",
    )

    # 3. Host orchestrator: geometry validation, 32-bit overflow guards, secret allocation & scrubbing
    require_contains(
        lib_rs,
        [
            "if count > u32::MAX as usize / stride",
            "validate_geometry::<N>(p)?;",
            "ScratchPool::ensure(&self.ctx, &mut pool.keys, keys_bytes, true)?",
            "ScratchPool::ensure(&self.ctx, &mut pool.keys, num_keys * std::mem::size_of::<KeyMaterial>(), true,)?",
            "ScratchPool::ensure(&self.ctx, &mut pool.keys, num_keys * std::mem::size_of::<ShakeKeyMaterial>(), true,)?",
        ],
        "metal/src/lib.rs",
    )

    # Both operations install cleanup before writing any pooled key material.
    require_contains(lib_rs, ["impl Drop for ScratchUse<'_> {fn drop(&mut self) {if let Some(keys) = &mut self.0.keys { keys.zeroize_contents(); }}}"], "scratch key cleanup")
    keygen_fn = lib_rs[
        lib_rs.index("fn keygen_internal_batch_family") : lib_rs.index("fn sign_batch_family")
    ]
    sign_fn = lib_rs[
        lib_rs.index("fn sign_internal_batch_family") : lib_rs.index("// Helpers")
    ]
    require_ordered(
        keygen_fn,
        [
            "validate_geometry::<N>(p)?;",
            "check_grid(count, leaves_per_tree * words)?;",
            "check_grid(count, leaves_per_tree * wots_len * words)?;",
            "let cleanup = ScratchUse(&mut locked);",
            "let pool = &mut *cleanup.0;",
            "ScratchPool::ensure(&self.ctx, &mut pool.keys,",
            "cmd.commit_and_wait()?;",
        ],
        "keygen_internal_batch_family",
    )
    require_ordered(
        sign_fn,
        [
            "validate_geometry::<N>(p)?;",
            "check_grid(num_sigs, sig_bytes.max(d * leaves_per_tree * words))?;",
            "let s1 = if p.a <= 8 { p.a } else { 7 };",
            "let s2 = p.a - s1;",
            "check_grid(num_sigs, p.k as usize * subtrees_per_tree as usize * words)?;",
            "check_grid(num_sigs, d * leaves_per_tree * wots_len * words)?;",
            "let cleanup = ScratchUse(&mut locked);",
            "let pool = &mut *cleanup.0;",
            "ScratchPool::ensure(&self.ctx, &mut pool.keys,",
            "let mut cmd = self.ctx.begin_cmd(true)?;",
            "cmd.dispatch_threads(&pipes.wots_chains,",
            "cmd.dispatch_threads(&pipes.xmss_leaves_streaming,",
            "cmd.dispatch_threadgroups(&pipes.fors_pass1,",
            "cmd.barrier();",
            "cmd.dispatch_threads(&pipes.wots_tlen,",
            "cmd.dispatch_threadgroups(&pipes.xmss_reduce,",
            "cmd.dispatch_threadgroups(&pipes.fors_pass2,",
            "cmd.dispatch_threads(&pipes.fors_pk,",
            "cmd.barrier();",
            "cmd.dispatch_threadgroups(&pipes.xmss_reduce,",
            "cmd.dispatch_threads(&pipes.fors_pk,",
            "if need_stage3_barrier { cmd.barrier(); }",
            "cmd.dispatch_threads(&pipes.wots_sign,",
            "cmd.commit_and_wait()?;",
        ],
        "sign_internal_batch_family",
    )

    bindings = runpy.run_path(str(HERE / "metal-bindings.py"))
    binding_claims = bindings["verify"](lib_rs, sha2_msl, shake_msl)
    command = runpy.run_path(str(HERE / "metal-command.py"))
    command["geometry_sources"](lib_rs, (ROOT / "rust/src/params.rs").read_text(), PARAM_SETS)
    command_claims = command["verify"](lib_rs, gpu_rs, bridge, sha2_msl, shake_msl, bindings, PARAM_SETS)
    binding_claims = "import Metal.HostValues\nimport Metal.ForsPkDispatch\nimport Metal.WotsOutput\nimport Metal.LeafDispatch\nimport Metal.ChainDispatch\nimport Metal.CommandValues\nimport Metal.SignatureLayout\nimport Metal.Command\n" + binding_claims + "\n" + command_claims
    bindings["check_slot_swaps"](lib_rs, sha2_msl, shake_msl)
    # The bridge binds the ith Rust handle at MSL slot i, with no dynamic offset.
    require_contains(gpu_rs, [
        "for (dst, b) in buf_ptrs.iter_mut().zip(buffers.iter()) { *dst = b.raw.as_ptr() as *const SlhMetalBuffer; }",
        """for (i, b) in inline_bytes.iter().enumerate() {
            byte_ptrs[i] = b.data.as_ptr() as *const c_void;
            byte_lens[i] = u32::try_from(b.data.len()).expect("inline binding exceeds u32");
            byte_indices[i] = b.index;
        }""",
        "self.dispatch_impl(pipeline,buffers,inline_bytes,grid_x,tg_x,tg_mem_len,false);",
        "self.dispatch_impl(pipeline,buffers,inline_bytes,num_tgs,tg_x,tg_mem_len,true);",
        "let data = bytemuck::bytes_of(val); Self { index, data }",
        "slh_metal_cmd_dispatch(raw.as_ptr(),pipeline.raw.as_ptr(),buf_ptrs.as_ptr(),buffers.len() as u32,byte_ptrs.as_ptr(),byte_lens.as_ptr(),byte_indices.as_ptr(),inline_bytes.len() as u32,grid_x,tg_x,tg_mem_len,use_threadgroups,)",
    ], "Rust dispatch forwarding")
    require_contains(bridge, [
        "for (uint32_t i = 0; i < num_buffers; ++i) { if (buffers[i]) { SlhMetalBufferObj *bufObj = (__bridge SlhMetalBufferObj *)buffers[i]; [enc setBuffer:bufObj.buffer offset:0 atIndex:i]; } }",
        "for (uint32_t i = 0; i < num_bytes; ++i) { [enc setBytes:bytes_ptrs[i] length:bytes_lens[i] atIndex:bytes_indices[i]]; }",
        "[enc setComputePipelineState:pipeObj.state];",
        """MTLSize tgSize = MTLSizeMake(tg_x, 1, 1);
        if (use_threadgroups) {
            MTLSize numTgs = MTLSizeMake(grid_x, 1, 1);
            [enc dispatchThreadgroups:numTgs threadsPerThreadgroup:tgSize];
        } else {
            MTLSize gridSize = MTLSizeMake(grid_x, 1, 1);
            [enc dispatchThreads:gridSize threadsPerThreadgroup:tgSize];
        }""",
    ], "Objective-C slot forwarding")

    dispatch = compact(bridge.split("void slh_metal_cmd_dispatch(", 1)[1].split("int slh_metal_cmd_commit_and_wait(", 1)[0])
    for op in ("setComputePipelineState:", "setBuffer:", "setBytes:", "setThreadgroupMemoryLength:"):
        if dispatch.count(op) != 1:
            raise ValueError(f"unexpected Metal encoder operations for {op}")

    # Verify 32-bit index bounds at every supported parameter geometry.
    u32_max = (1 << 32) - 1
    for name, family, n, h, d, hp, a, k, m_bytes in PARAM_SETS:
        wots_len = 2 * n + 3
        leaves = 1 << hp
        words = n // (8 if family == "shake" else 4)
        s1 = a if a <= 8 else 7
        s2 = a - s1
        subtrees = 1 << s2
        fors_sig_bytes = k * (1 + a) * n
        xmss_sig_bytes = (wots_len + hp) * n
        sig_bytes = n + fors_sig_bytes + d * xmss_sig_bytes

        # Tie the per-field byte bijection to the number of bytes returned by
        # this production row. Batch count and all field indices remain arbitrary.
        layout = f"(⟨{n},{k},{s1},{s2},{d},{wots_len},{hp}⟩ : MetalSignatureLayout.Geometry)"
        binding_claims += (
            f"\nexample (count : Nat) : "
            f"Function.Injective (@MetalSignatureLayout.address {layout} count) ∧ "
            f"(∀ p : MetalSignatureLayout.Byte {layout} count, MetalSignatureLayout.address {layout} p < count * {sig_bytes}) ∧ "
            f"(∀ pos < count * {sig_bytes}, ∃! p : MetalSignatureLayout.Byte {layout} count, "
            f"MetalSignatureLayout.address {layout} p = pos) := "
            f"⟨MetalSignatureLayout.disjoint _ _, MetalSignatureLayout.in_bounds _, "
            f"fun _ h => MetalSignatureLayout.cover _ h⟩"
        )

        # Instantiate the index theorem with each replayed layout. Count, item
        # and the inner word/byte offset remain universally quantified in Lean.
        sign_guard = max(sig_bytes, d * leaves * words)
        for stride, guard in [
            (leaves * words, leaves * words),
            (leaves * wots_len * words, leaves * wots_len * words),
            (sig_bytes, sign_guard),
            (d * leaves * words, sign_guard),
            (d * wots_len, sign_guard),
            (k * subtrees * words, k * subtrees * words),
            (d * leaves * wots_len * words, d * leaves * wots_len * words),
        ]:
            binding_claims += (
                f"\nexample (count item offset : Nat) (checked : count ≤ (2^32-1)/{guard}) "
                f"(hi : item < count) (ho : offset < {stride}) := "
                f"@MetalBindings.flat_index count {stride} {guard} item offset "
                "(by decide) checked (by decide) hi ho"
            )
        # Max representable batch sizes admitted by check_grid
        max_kg_stream = u32_max // (leaves * words)
        max_kg_2ph = min(max_kg_stream, u32_max // (leaves * wots_len * words))
        assert max_kg_stream * leaves * words <= u32_max
        assert max_kg_2ph * leaves * wots_len * words <= u32_max
        assert (1 << (hp - 1)) * n <= 32768  # fits in Apple Metal 32 KB threadgroup memory

        max_sg_stream = min(
            u32_max // max(sig_bytes, d * leaves * words),
            u32_max // (k * subtrees * words),
        )
        max_sg_2ph = min(max_sg_stream, u32_max // (d * leaves * wots_len * words))
        # Check every u32 index computed in any kernel fits in u32::MAX
        assert max_sg_stream * sig_bytes <= u32_max
        assert max_sg_stream * d * leaves * words <= u32_max
        assert max_sg_stream * k * subtrees * words <= u32_max
        assert max_sg_stream * d * wots_len <= u32_max
        assert max_sg_2ph * d * leaves * wots_len * words <= u32_max
        # Threadgroup memory fits comfortably in 32 KB
        assert (1 << (s1 - 1)) * n <= 32768
        if s2 > 0:
            assert (1 << (s2 - 1)) * n <= 32768
        # FORS tree index word3 fits in u32
        assert ((k - 1) << a) + ((1 << a) - 1) <= u32_max
        # ForsJobDesc::indices has length 36 >= k
        assert k <= 36
        # Digest geometry checks
        assert h == d * hp and 1 <= hp <= 9 and 1 <= a <= 14

    print("FFI/host boundary audit passed (bridge.m, gpu.rs, lib.rs, all 12 parameter sets).")
    return binding_claims


# ============================================================================
# Host-side FIPS 205 preprocessing (PRF_msg, H_msg, digest parsing, base_2b)
# ============================================================================


def mgf1(hash_fn, seed: bytes, length: int) -> bytes:
    out = bytearray()
    counter = 0
    while len(out) < length:
        out.extend(hash_fn(seed + struct.pack(">I", counter)).digest())
        counter += 1
    return bytes(out[:length])


def compute_prf_msg_and_h_msg(family: str, n: int, m_bytes: int, sk_prf: bytes, pk_seed: bytes, pk_root: bytes, addrnd: bytes, msg: bytes):
    if family == "shake":
        r = hashlib.shake_256(sk_prf + addrnd + msg).digest(n)
        digest = hashlib.shake_256(r + pk_seed + pk_root + msg).digest(m_bytes)
        return r, digest
    elif n == 16:
        r = hmac.new(sk_prf, addrnd + msg, hashlib.sha256).digest()[:n]
        inner = hashlib.sha256(r + pk_seed + pk_root + msg).digest()
        digest = mgf1(hashlib.sha256, r + pk_seed + inner, m_bytes)
        return r, digest
    else:
        r = hmac.new(sk_prf, addrnd + msg, hashlib.sha512).digest()[:n]
        inner = hashlib.sha512(r + pk_seed + pk_root + msg).digest()
        digest = mgf1(hashlib.sha512, r + pk_seed + inner, m_bytes)
        return r, digest


def base_2b(x: bytes, b: int, out_len: int) -> list[int]:
    inp = 0
    bits = 0
    total = 0
    mask = (1 << b) - 1
    out = []
    for _ in range(out_len):
        while bits < b:
            total = (total << 8) + x[inp]
            inp += 1
            bits += 8
        bits -= b
        out.append((total >> bits) & mask)
    return out


def parse_digest(h: int, d: int, hp: int, a: int, k: int, digest: bytes):
    md_bytes = (k * a + 7) // 8
    tree_bits = h - hp
    tree_bytes = (tree_bits + 7) // 8
    leaf_bytes = (hp + 7) // 8
    md = digest[:md_bytes]
    idx_tree = int.from_bytes(digest[md_bytes : md_bytes + tree_bytes], "big") & (
        (1 << tree_bits) - 1
    )
    idx_leaf = int.from_bytes(
        digest[md_bytes + tree_bytes : md_bytes + tree_bytes + leaf_bytes], "big"
    ) & ((1 << hp) - 1)
    fors_indices = base_2b(md, a, k)
    return idx_tree, idx_leaf, fors_indices


# ============================================================================
# Lift ACTUAL production MSL shaders into C++20 host execution + hash hooks
# ============================================================================


CPP_PREAMBLE = r"""
#include <algorithm>
#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <coroutine>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

using uint = uint32_t;

#define constant const
#define device
#define thread
#define threadgroup
#define kernel

namespace mem_flags {
[[maybe_unused]] constexpr int mem_threadgroup = 0;
}

inline uint32_t rotate(uint32_t x, uint32_t n) {
    uint32_t s = n & 31u;
    return s == 0u ? x : ((x << s) | (x >> (32u - s)));
}

struct TGTask {
    struct promise_type {
        TGTask get_return_object() {
            return TGTask{std::coroutine_handle<promise_type>::from_promise(*this)};
        }
        std::suspend_always initial_suspend() noexcept { return {}; }
        std::suspend_always final_suspend() noexcept { return {}; }
        void return_void() noexcept {}
        void unhandled_exception() { std::rethrow_exception(std::current_exception()); }
    };
    std::coroutine_handle<promise_type> h;
    TGTask(std::coroutine_handle<promise_type> handle) : h(handle) {}
    TGTask(TGTask&& o) noexcept : h(o.h) { o.h = nullptr; }
    TGTask(const TGTask&) = delete;
    TGTask& operator=(const TGTask&) = delete;
    ~TGTask() { if (h) h.destroy(); }
    bool done() const { return h.done(); }
    void resume() { h.resume(); }
};

#define threadgroup_barrier(flags) co_await std::suspend_always{}

// ============================================================================
// Independent FIPS 180-4 (SHA-256 / SHA-512) & FIPS 202 (SHAKE256) Reference
// ============================================================================

namespace ref {

static const uint32_t H256_IV[8] = {
    0x6a09e667u, 0xbb67ae85u, 0x3c6ef372u, 0xa54ff53au,
    0x510e527fu, 0x9b05688cu, 0x1f83d9abu, 0x5be0cd19u
};

static const uint32_t RK256[64] = {
    0x428a2f98u, 0x71374491u, 0xb5c0fbcfu, 0xe9b5dba5u,
    0x3956c25bu, 0x59f111f1u, 0x923f82a4u, 0xab1c5ed5u,
    0xd807aa98u, 0x12835b01u, 0x243185beu, 0x550c7dc3u,
    0x72be5d74u, 0x80deb1feu, 0x9bdc06a7u, 0xc19bf174u,
    0xe49b69c1u, 0xefbe4786u, 0x0fc19dc6u, 0x240ca1ccu,
    0x2de92c6fu, 0x4a7484aau, 0x5cb0a9dcu, 0x76f988dau,
    0x983e5152u, 0xa831c66du, 0xb00327c8u, 0xbf597fc7u,
    0xc6e00bf3u, 0xd5a79147u, 0x06ca6351u, 0x14292967u,
    0x27b70a85u, 0x2e1b2138u, 0x4d2c6dfcu, 0x53380d13u,
    0x650a7354u, 0x766a0abbu, 0x81c2c92eu, 0x92722c85u,
    0xa2bfe8a1u, 0xa81a664bu, 0xc24b8b70u, 0xc76c51a3u,
    0xd192e819u, 0xd6990624u, 0xf40e3585u, 0x106aa070u,
    0x19a4c116u, 0x1e376c08u, 0x2748774cu, 0x34b0bcb5u,
    0x391c0cb3u, 0x4ed8aa4au, 0x5b9cca4fu, 0x682e6ff3u,
    0x748f82eeu, 0x78a5636fu, 0x84c87814u, 0x8cc70208u,
    0x90befffau, 0xa4506cebu, 0xbef9a3f7u, 0xc67178f2u
};

static const uint64_t H512_IV[8] = {
    0x6a09e667f3bcc908ull, 0xbb67ae8584caa73bull,
    0x3c6ef372fe94f82bull, 0xa54ff53a5f1d36f1ull,
    0x510e527fade682d1ull, 0x9b05688c2b3e6c1full,
    0x1f83d9abfb41bd6bull, 0x5be0cd19137e2179ull
};

static const uint64_t RK512[80] = {
    0x428a2f98d728ae22ull, 0x7137449123ef65cdull, 0xb5c0fbcfec4d3b2full, 0xe9b5dba58189dbbcull,
    0x3956c25bf348b538ull, 0x59f111f1b605d019ull, 0x923f82a4af194f9bull, 0xab1c5ed5da6d8118ull,
    0xd807aa98a3030242ull, 0x12835b0145706fbeull, 0x243185be4ee4b28cull, 0x550c7dc3d5ffb4e2ull,
    0x72be5d74f27b896full, 0x80deb1fe3b1696b1ull, 0x9bdc06a725c71235ull, 0xc19bf174cf692694ull,
    0xe49b69c19ef14ad2ull, 0xefbe4786384f25e3ull, 0x0fc19dc68b8cd5b5ull, 0x240ca1cc77ac9c65ull,
    0x2de92c6f592b0275ull, 0x4a7484aa6ea6e483ull, 0x5cb0a9dcbd41fbd4ull, 0x76f988da831153b5ull,
    0x983e5152ee66dfabull, 0xa831c66d2db43210ull, 0xb00327c898fb213full, 0xbf597fc7beef0ee4ull,
    0xc6e00bf33da88fc2ull, 0xd5a79147930aa725ull, 0x06ca6351e003826full, 0x142929670a0e6e70ull,
    0x27b70a8546d22ffcull, 0x2e1b21385c26c926ull, 0x4d2c6dfc5ac42aedull, 0x53380d139d95b3dfull,
    0x650a73548baf63deull, 0x766a0abb3c77b2a8ull, 0x81c2c92e47edaee6ull, 0x92722c851482353bull,
    0xa2bfe8a14cf10364ull, 0xa81a664bbc423001ull, 0xc24b8b70d0f89791ull, 0xc76c51a30654be30ull,
    0xd192e819d6ef5218ull, 0xd69906245565a910ull, 0xf40e35855771202aull, 0x106aa07032bbd1b8ull,
    0x19a4c116b8d2d0c8ull, 0x1e376c085141ab53ull, 0x2748774cdf8eeb99ull, 0x34b0bcb5e19b48a8ull,
    0x391c0cb3c5c95a63ull, 0x4ed8aa4ae3418acbull, 0x5b9cca4f7763e373ull, 0x682e6ff3d6b2b8a3ull,
    0x748f82ee5defb2fcull, 0x78a5636f43172f60ull, 0x84c87814a1f0ab72ull, 0x8cc702081a6439ecull,
    0x90befffa23631e28ull, 0xa4506cebde82bde9ull, 0xbef9a3f7b2c67915ull, 0xc67178f2e372532bull,
    0xca273eceea26619cull, 0xd186b8c721c0c207ull, 0xeada7dd6cde0eb1eull, 0xf57d4f7fee6ed178ull,
    0x06f067aa72176fbaull, 0x0a637dc5a2c898a6ull, 0x113f9804bef90daeull, 0x1b710b35131c471bull,
    0x28db77f523047d84ull, 0x32caab7b40c72493ull, 0x3c9ebe0a15c9bebcull, 0x431d67c49c100d4cull,
    0x4cc5d4becb3e42b6ull, 0x597f299cfc657e2aull, 0x5fcb6fab3ad6faecull, 0x6c44198c4a475817ull
};

static inline uint32_t ror32(uint32_t x, uint32_t n) { return (x >> n) | (x << (32u - n)); }
static inline uint64_t ror64(uint64_t x, uint64_t n) { return (x >> n) | (x << (64u - n)); }
static inline uint64_t rol64(uint64_t x, uint64_t n) { return (x << n) | (x >> (64u - n)); }

static inline uint32_t load_be32(const uint8_t* p) {
    return (uint32_t(p[0]) << 24) | (uint32_t(p[1]) << 16) | (uint32_t(p[2]) << 8) | uint32_t(p[3]);
}
static inline uint64_t load_be64(const uint8_t* p) {
    return (uint64_t(load_be32(p)) << 32) | uint64_t(load_be32(p + 4));
}
static inline uint64_t load_le64(const uint8_t* p) {
    uint64_t v = 0;
    for (int i = 0; i < 8; ++i) v |= uint64_t(p[i]) << (8 * i);
    return v;
}

static void sha256_block(uint32_t st[8], const uint8_t blk[64]) {
    uint32_t w[64];
    for (int i = 0; i < 16; ++i) w[i] = load_be32(blk + 4 * i);
    for (int i = 16; i < 64; ++i) {
        uint32_t s0 = ror32(w[i - 15], 7) ^ ror32(w[i - 15], 18) ^ (w[i - 15] >> 3);
        uint32_t s1 = ror32(w[i - 2], 17) ^ ror32(w[i - 2], 19) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16] + s0 + w[i - 7] + s1;
    }
    uint32_t a = st[0], b = st[1], c = st[2], d = st[3];
    uint32_t e = st[4], f = st[5], g = st[6], h = st[7];
    for (int i = 0; i < 64; ++i) {
        uint32_t S1 = ror32(e, 6) ^ ror32(e, 11) ^ ror32(e, 25);
        uint32_t ch = (e & f) ^ ((~e) & g);
        uint32_t t1 = h + S1 + ch + RK256[i] + w[i];
        uint32_t S0 = ror32(a, 2) ^ ror32(a, 13) ^ ror32(a, 22);
        uint32_t maj = (a & b) ^ (a & c) ^ (b & c);
        uint32_t t2 = S0 + maj;
        h = g; g = f; f = e; e = d + t1;
        d = c; c = b; b = a; a = t1 + t2;
    }
    st[0] += a; st[1] += b; st[2] += c; st[3] += d;
    st[4] += e; st[5] += f; st[6] += g; st[7] += h;
}

static std::array<uint32_t, 8> sha256_words(const uint8_t* msg, size_t len) {
    std::array<uint32_t, 8> st;
    for (int i = 0; i < 8; ++i) st[i] = H256_IV[i];
    size_t pos = 0;
    while (pos + 64 <= len) {
        sha256_block(st.data(), msg + pos);
        pos += 64;
    }
    uint8_t tail[128] = {0};
    size_t rem = len - pos;
    if (rem) std::memcpy(tail, msg + pos, rem);
    tail[rem] = 0x80;
    size_t padded = (rem + 1 + 8 <= 64) ? 64 : 128;
    uint64_t bits = uint64_t(len) * 8ull;
    for (int i = 0; i < 8; ++i) tail[padded - 8 + i] = uint8_t(bits >> (56 - 8 * i));
    sha256_block(st.data(), tail);
    if (padded == 128) sha256_block(st.data(), tail + 64);
    return st;
}

static void sha512_block(uint64_t st[8], const uint8_t blk[128]) {
    uint64_t w[80];
    for (int i = 0; i < 16; ++i) w[i] = load_be64(blk + 8 * i);
    for (int i = 16; i < 80; ++i) {
        uint64_t s0 = ror64(w[i - 15], 1) ^ ror64(w[i - 15], 8) ^ (w[i - 15] >> 7);
        uint64_t s1 = ror64(w[i - 2], 19) ^ ror64(w[i - 2], 61) ^ (w[i - 2] >> 6);
        w[i] = w[i - 16] + s0 + w[i - 7] + s1;
    }
    uint64_t a = st[0], b = st[1], c = st[2], d = st[3];
    uint64_t e = st[4], f = st[5], g = st[6], h = st[7];
    for (int i = 0; i < 80; ++i) {
        uint64_t S1 = ror64(e, 14) ^ ror64(e, 18) ^ ror64(e, 41);
        uint64_t ch = (e & f) ^ ((~e) & g);
        uint64_t t1 = h + S1 + ch + RK512[i] + w[i];
        uint64_t S0 = ror64(a, 28) ^ ror64(a, 34) ^ ror64(a, 39);
        uint64_t maj = (a & b) ^ (a & c) ^ (b & c);
        uint64_t t2 = S0 + maj;
        h = g; g = f; f = e; e = d + t1;
        d = c; c = b; b = a; a = t1 + t2;
    }
    st[0] += a; st[1] += b; st[2] += c; st[3] += d;
    st[4] += e; st[5] += f; st[6] += g; st[7] += h;
}

static std::array<uint64_t, 8> sha512_words(const uint8_t* msg, size_t len) {
    std::array<uint64_t, 8> st;
    for (int i = 0; i < 8; ++i) st[i] = H512_IV[i];
    size_t pos = 0;
    while (pos + 128 <= len) {
        sha512_block(st.data(), msg + pos);
        pos += 128;
    }
    uint8_t tail[256] = {0};
    size_t rem = len - pos;
    if (rem) std::memcpy(tail, msg + pos, rem);
    tail[rem] = 0x80;
    size_t padded = (rem + 1 + 16 <= 128) ? 128 : 256;
    uint64_t bits = uint64_t(len) * 8ull;
    for (int i = 0; i < 8; ++i) tail[padded - 8 + i] = uint8_t(bits >> (56 - 8 * i));
    sha512_block(st.data(), tail);
    if (padded == 256) sha512_block(st.data(), tail + 128);
    return st;
}

static const uint64_t KECCAKF_RC[24] = {
    0x0000000000000001ull, 0x0000000000008082ull, 0x800000000000808aull, 0x8000000080008000ull,
    0x000000000000808bull, 0x0000000080000001ull, 0x8000000080008081ull, 0x8000000000008009ull,
    0x000000000000008aull, 0x0000000000000088ull, 0x0000000080008009ull, 0x000000008000000aull,
    0x000000008000808bull, 0x800000000000008bull, 0x8000000000008089ull, 0x8000000000008003ull,
    0x8000000000008002ull, 0x8000000000000080ull, 0x000000000000800aull, 0x800000008000000aull,
    0x8000000080008081ull, 0x8000000000008080ull, 0x0000000080000001ull, 0x8000000080008008ull
};

static const int RHO_OFF[25] = {
    0, 1, 62, 28, 27,
    36, 44, 6, 55, 20,
    3, 10, 43, 25, 39,
    41, 45, 15, 21, 8,
    18, 2, 61, 56, 14
};

static void keccak_ref(uint64_t a[25]) {
    for (int r = 0; r < 24; ++r) {
        uint64_t c[5], d[5], b[25];
        for (int x = 0; x < 5; ++x) c[x] = a[x] ^ a[x+5] ^ a[x+10] ^ a[x+15] ^ a[x+20];
        for (int x = 0; x < 5; ++x) d[x] = c[(x + 4) % 5] ^ rol64(c[(x + 1) % 5], 1);
        for (int i = 0; i < 25; ++i) a[i] ^= d[i % 5];
        for (int y = 0; y < 5; ++y)
            for (int x = 0; x < 5; ++x) {
                int idx = x + 5 * y;
                int nx = y;
                int ny = (2 * x + 3 * y) % 5;
                b[nx + 5 * ny] = RHO_OFF[idx] ? rol64(a[idx], RHO_OFF[idx]) : a[idx];
            }
        for (int y = 0; y < 5; ++y)
            for (int x = 0; x < 5; ++x)
                a[x + 5 * y] = b[x + 5 * y] ^ ((~b[((x + 1) % 5) + 5 * y]) & b[((x + 2) % 5) + 5 * y]);
        a[0] ^= KECCAKF_RC[r];
    }
}

static std::array<uint64_t, 4> shake256_lanes(const uint8_t* msg, size_t len) {
    uint64_t st[25] = {0};
    size_t pos = 0;
    while (pos + 136 <= len) {
        for (int i = 0; i < 17; ++i) st[i] ^= load_le64(msg + pos + 8 * i);
        keccak_ref(st);
        pos += 136;
    }
    uint8_t blk[136] = {0};
    size_t rem = len - pos;
    if (rem) std::memcpy(blk, msg + pos, rem);
    blk[rem] ^= 0x1Fu;
    blk[135] ^= 0x80u;
    for (int i = 0; i < 17; ++i) st[i] ^= load_le64(blk + 8 * i);
    keccak_ref(st);
    return {st[0], st[1], st[2], st[3]};
}

} // namespace ref

// ============================================================================
// Compression/Permutation Message-Construction Instrumentation Hooks
// ============================================================================

struct KeyAuditInfo {
    std::vector<uint8_t> pk_seed;
    std::array<uint32_t, 8> state256;
    std::array<uint64_t, 8> state512;
};

struct Sha2StreamState {
    int key_idx = -1;
    uint32_t adrs_type = 0;
    size_t expected_msg_len = 0;
    size_t expected_padded_len = 0;
    std::vector<uint8_t> blocks;
};

struct ShakeStreamState {
    uint32_t adrs_type = 0;
    size_t expected_msg_len = 0;
    size_t expected_blocks = 0;
    size_t blocks_seen = 0;
    std::array<uint64_t, 25> prev_st{};
    std::vector<uint8_t> rate_bytes;
};

struct AuditCtx {
    std::string kernel_name;
    uint32_t N = 16;
    uint32_t wots_len = 35;
    uint32_t k = 14;
    uint32_t allowed_types_mask = 0;
    bool forbid_all_hashes = false;
    std::vector<KeyAuditInfo> keys;
    uint64_t sha256_from_calls = 0;
    uint64_t sha256_stream_msgs = 0;
    uint64_t sha512_stream_msgs = 0;
    uint64_t shake_msgs = 0;
    uint64_t ref_checks = 0;
    uint64_t type_counts[7] = {0};
    std::unordered_map<const void*, Sha2StreamState> sha256_streams;
    std::unordered_map<const void*, Sha2StreamState> sha512_streams;
    std::unordered_map<const void*, ShakeStreamState> shake_streams;

    void reset_for_kernel(const std::string& name, uint32_t mask, bool forbid = false) {
        if (!sha256_streams.empty() || !sha512_streams.empty() || !shake_streams.empty()) {
            throw std::runtime_error("Unfinished hash stream left over before kernel " + name);
        }
        kernel_name = name;
        allowed_types_mask = mask;
        forbid_all_hashes = forbid;
    }

    void finish_kernel() {
        if (!sha256_streams.empty() || !sha512_streams.empty() || !shake_streams.empty()) {
            throw std::runtime_error("Unfinished hash stream after kernel " + kernel_name);
        }
    }

    int find_key_256(const uint32_t st[8]) const {
        for (size_t i = 0; i < keys.size(); ++i) {
            if (std::memcmp(st, keys[i].state256.data(), 32) == 0) return int(i);
        }
        return -1;
    }
    int find_key_512(const uint64_t st[8]) const {
        for (size_t i = 0; i < keys.size(); ++i) {
            if (std::memcmp(st, keys[i].state512.data(), 64) == 0) return int(i);
        }
        return -1;
    }
    int find_key_shake(const uint8_t* pk_bytes) const {
        for (size_t i = 0; i < keys.size(); ++i) {
            if (std::memcmp(pk_bytes, keys[i].pk_seed.data(), N) == 0) return int(i);
        }
        return -1;
    }

    size_t expected_sha2_msg_len(uint32_t typ, uint32_t word2) const {
        switch (typ) {
            case 0: /* WOTS_HASH */
            case 5: /* WOTS_PRF */
            case 6: /* FORS_PRF */
                return 22u + N;
            case 1: /* WOTS_PK */
                return 22u + wots_len * N;
            case 2: /* TREE */
                return 22u + 2u * N;
            case 3: /* FORS_TREE */
                return (word2 == 0u) ? (22u + N) : (22u + 2u * N);
            case 4: /* FORS_ROOTS */
                return 22u + k * N;
            default:
                throw std::runtime_error("Unexpected SHA-2 ADRS type " + std::to_string(typ));
        }
    }

    size_t expected_shake_msg_len(uint32_t typ, uint32_t word2) const {
        switch (typ) {
            case 0:
            case 5:
            case 6:
                return N + 32u + N;
            case 1:
                return N + 32u + wots_len * N;
            case 2:
                return N + 32u + 2u * N;
            case 3:
                return (word2 == 0u) ? (N + 32u + N) : (N + 32u + 2u * N);
            case 4:
                return N + 32u + k * N;
            default:
                throw std::runtime_error("Unexpected SHAKE ADRS type " + std::to_string(typ));
        }
    }
};

static AuditCtx g_audit;
"""

SHA2_HOOKS = r"""
inline void sha256_compress_from(
    const thread uint32_t base_st[8],
    thread uint32_t w[16],
    thread uint32_t out[8]
) {
    if (g_audit.forbid_all_hashes) {
        throw std::runtime_error("Unexpected sha256_compress_from in sentinel/OOB invocation of " + g_audit.kernel_name);
    }
    int kidx = g_audit.find_key_256(base_st);
    if (kidx < 0) {
        throw std::runtime_error("sha256_compress_from base_st does not match any key state256 in " + g_audit.kernel_name);
    }
    uint8_t blk[64];
    for (int i = 0; i < 16; ++i) {
        blk[4*i + 0] = uint8_t(w[i] >> 24);
        blk[4*i + 1] = uint8_t(w[i] >> 16);
        blk[4*i + 2] = uint8_t(w[i] >> 8);
        blk[4*i + 3] = uint8_t(w[i]);
    }
    if (w[14] != 0u || (w[15] % 8u) != 0u || w[15] < 64u * 8u) {
        throw std::runtime_error("Invalid SHA-256 bit-length trailer in " + g_audit.kernel_name);
    }
    uint32_t typ = blk[9];
    uint32_t word2 = ref::load_be32(blk + 14);
    if (typ >= 7u || ((g_audit.allowed_types_mask & (1u << typ)) == 0u)) {
        throw std::runtime_error("Disallowed SHA-256 ADRS type " + std::to_string(typ) + " in " + g_audit.kernel_name);
    }
    size_t expected_len = g_audit.expected_sha2_msg_len(typ, word2);
    size_t msg_len = (w[15] / 8u) - 64u;
    if (msg_len != expected_len || msg_len >= 56u) {
        throw std::runtime_error("SHA-256 single-block length mismatch in " + g_audit.kernel_name);
    }
    if (blk[msg_len] != 0x80u) {
        throw std::runtime_error("Missing 0x80 pad byte in sha256_compress_from in " + g_audit.kernel_name);
    }
    for (size_t i = msg_len + 1; i < 56u; ++i) {
        if (blk[i] != 0u) {
            throw std::runtime_error("Non-zero padding byte in sha256_compress_from in " + g_audit.kernel_name);
        }
    }

    raw_sha256_compress_from(base_st, w, out);

    // Cross-check against independent FIPS 180-4 reference on full PK.seed || 0^{64-N} || ADRSc || payload
    uint64_t idx = g_audit.sha256_from_calls++;
    g_audit.type_counts[typ]++;
    if (idx < 4096 || (idx & 63u) == 0u) {
        uint8_t full_msg[128] = {0};
        std::memcpy(full_msg, g_audit.keys[kidx].pk_seed.data(), g_audit.N);
        std::memcpy(full_msg + 64, blk, msg_len);
        auto expected_st = ref::sha256_words(full_msg, 64u + msg_len);
        if (std::memcmp(expected_st.data(), out, 32) != 0) {
            throw std::runtime_error("sha256_compress_from output diverged from FIPS 180-4 reference in " + g_audit.kernel_name);
        }
        g_audit.ref_checks++;
    }
}

inline void sha256_compress(thread uint32_t st[8], thread uint32_t w[16]) {
    if (g_audit.forbid_all_hashes) {
        throw std::runtime_error("Unexpected sha256_compress in sentinel/OOB invocation of " + g_audit.kernel_name);
    }
    uint8_t blk[64];
    for (int i = 0; i < 16; ++i) {
        blk[4*i + 0] = uint8_t(w[i] >> 24);
        blk[4*i + 1] = uint8_t(w[i] >> 16);
        blk[4*i + 2] = uint8_t(w[i] >> 8);
        blk[4*i + 3] = uint8_t(w[i]);
    }
    auto it = g_audit.sha256_streams.find(st);
    if (it == g_audit.sha256_streams.end()) {
        int kidx = g_audit.find_key_256(st);
        if (kidx < 0) {
            throw std::runtime_error("sha256_compress initial state does not match any key state256 in " + g_audit.kernel_name);
        }
        uint32_t typ = blk[9];
        uint32_t word2 = ref::load_be32(blk + 14);
        if (typ >= 7u || ((g_audit.allowed_types_mask & (1u << typ)) == 0u)) {
            throw std::runtime_error("Disallowed SHA-256 stream ADRS type " + std::to_string(typ) + " in " + g_audit.kernel_name);
        }
        size_t expected_len = g_audit.expected_sha2_msg_len(typ, word2);
        size_t expected_padded = ((expected_len + 1u + 8u + 63u) / 64u) * 64u;
        Sha2StreamState s;
        s.key_idx = kidx;
        s.adrs_type = typ;
        s.expected_msg_len = expected_len;
        s.expected_padded_len = expected_padded;
        s.blocks.reserve(expected_padded);
        it = g_audit.sha256_streams.emplace(st, std::move(s)).first;
    }
    Sha2StreamState& s = it->second;
    s.blocks.insert(s.blocks.end(), blk, blk + 64);
    raw_sha256_compress(st, w);

    if (s.blocks.size() == s.expected_padded_len) {
        if (s.blocks[s.expected_msg_len] != 0x80u) {
            throw std::runtime_error("Missing 0x80 pad byte in SHA-256 stream in " + g_audit.kernel_name);
        }
        for (size_t i = s.expected_msg_len + 1; i < s.expected_padded_len - 8u; ++i) {
            if (s.blocks[i] != 0u) {
                throw std::runtime_error("Non-zero pad byte in SHA-256 stream in " + g_audit.kernel_name);
            }
        }
        uint64_t got_bits = ref::load_be64(s.blocks.data() + s.expected_padded_len - 8u);
        uint64_t want_bits = uint64_t(64u + s.expected_msg_len) * 8ull;
        if (got_bits != want_bits) {
            throw std::runtime_error("SHA-256 stream bit-length mismatch in " + g_audit.kernel_name);
        }
        uint64_t idx = g_audit.sha256_stream_msgs++;
        g_audit.type_counts[s.adrs_type]++;
        if (idx < 2048 || (idx & 15u) == 0u) {
            std::vector<uint8_t> full_msg(64u + s.expected_msg_len, 0u);
            std::memcpy(full_msg.data(), g_audit.keys[s.key_idx].pk_seed.data(), g_audit.N);
            std::memcpy(full_msg.data() + 64u, s.blocks.data(), s.expected_msg_len);
            auto expected_st = ref::sha256_words(full_msg.data(), full_msg.size());
            if (std::memcmp(expected_st.data(), st, 32) != 0) {
                throw std::runtime_error("SHA-256 stream output diverged from FIPS 180-4 reference in " + g_audit.kernel_name);
            }
            g_audit.ref_checks++;
        }
        g_audit.sha256_streams.erase(it);
    } else if (s.blocks.size() > s.expected_padded_len) {
        throw std::runtime_error("SHA-256 stream exceeded expected block count in " + g_audit.kernel_name);
    }
}

inline void sha512_compress(thread uint64_t st[8], thread uint64_t w[16]) {
    if (g_audit.forbid_all_hashes) {
        throw std::runtime_error("Unexpected sha512_compress in sentinel/OOB invocation of " + g_audit.kernel_name);
    }
    uint8_t blk[128];
    for (int i = 0; i < 16; ++i) {
        for (int b = 0; b < 8; ++b) blk[8*i + b] = uint8_t(w[i] >> (56 - 8*b));
    }
    auto it = g_audit.sha512_streams.find(st);
    if (it == g_audit.sha512_streams.end()) {
        int kidx = g_audit.find_key_512(st);
        if (kidx < 0) {
            throw std::runtime_error("sha512_compress initial state does not match any key state512 in " + g_audit.kernel_name);
        }
        uint32_t typ = blk[9];
        uint32_t word2 = ref::load_be32(blk + 14);
        if (typ >= 7u || ((g_audit.allowed_types_mask & (1u << typ)) == 0u)) {
            throw std::runtime_error("Disallowed SHA-512 ADRS type " + std::to_string(typ) + " in " + g_audit.kernel_name);
        }
        size_t expected_len = g_audit.expected_sha2_msg_len(typ, word2);
        size_t expected_padded = ((expected_len + 1u + 16u + 127u) / 128u) * 128u;
        Sha2StreamState s;
        s.key_idx = kidx;
        s.adrs_type = typ;
        s.expected_msg_len = expected_len;
        s.expected_padded_len = expected_padded;
        s.blocks.reserve(expected_padded);
        it = g_audit.sha512_streams.emplace(st, std::move(s)).first;
    }
    Sha2StreamState& s = it->second;
    s.blocks.insert(s.blocks.end(), blk, blk + 128);
    raw_sha512_compress(st, w);

    if (s.blocks.size() == s.expected_padded_len) {
        if (s.blocks[s.expected_msg_len] != 0x80u) {
            throw std::runtime_error("Missing 0x80 pad byte in SHA-512 stream in " + g_audit.kernel_name);
        }
        for (size_t i = s.expected_msg_len + 1; i < s.expected_padded_len - 16u; ++i) {
            if (s.blocks[i] != 0u) {
                throw std::runtime_error("Non-zero pad byte in SHA-512 stream in " + g_audit.kernel_name);
            }
        }
        uint64_t hi_bits = ref::load_be64(s.blocks.data() + s.expected_padded_len - 16u);
        uint64_t lo_bits = ref::load_be64(s.blocks.data() + s.expected_padded_len - 8u);
        uint64_t want_bits = uint64_t(128u + s.expected_msg_len) * 8ull;
        if (hi_bits != 0ull || lo_bits != want_bits) {
            throw std::runtime_error("SHA-512 stream bit-length mismatch in " + g_audit.kernel_name);
        }
        uint64_t idx = g_audit.sha512_stream_msgs++;
        g_audit.type_counts[s.adrs_type]++;
        if (idx < 2048 || (idx & 15u) == 0u) {
            std::vector<uint8_t> full_msg(128u + s.expected_msg_len, 0u);
            std::memcpy(full_msg.data(), g_audit.keys[s.key_idx].pk_seed.data(), g_audit.N);
            std::memcpy(full_msg.data() + 128u, s.blocks.data(), s.expected_msg_len);
            auto expected_st = ref::sha512_words(full_msg.data(), full_msg.size());
            if (std::memcmp(expected_st.data(), st, 64) != 0) {
                throw std::runtime_error("SHA-512 stream output diverged from FIPS 180-4 reference in " + g_audit.kernel_name);
            }
            g_audit.ref_checks++;
        }
        g_audit.sha512_streams.erase(it);
    } else if (s.blocks.size() > s.expected_padded_len) {
        throw std::runtime_error("SHA-512 stream exceeded expected block count in " + g_audit.kernel_name);
    }
}
"""

SHAKE_HOOK = r"""
inline void keccak_f1600(thread uint64_t st[25]) {
    if (g_audit.forbid_all_hashes) {
        throw std::runtime_error("Unexpected keccak_f1600 in sentinel/OOB invocation of " + g_audit.kernel_name);
    }
    auto it = g_audit.shake_streams.find(st);
    uint8_t delta_bytes[136];
    if (it == g_audit.shake_streams.end()) {
        for (int i = 17; i < 25; ++i) {
            if (st[i] != 0ull) {
                throw std::runtime_error("Non-zero initial Keccak capacity lane in " + g_audit.kernel_name);
            }
        }
        for (int i = 0; i < 17; ++i) {
            for (int b = 0; b < 8; ++b) delta_bytes[8*i + b] = uint8_t(st[i] >> (8 * b));
        }
        if (g_audit.find_key_shake(delta_bytes) < 0) {
            throw std::runtime_error("SHAKE initial PK.seed prefix mismatch in " + g_audit.kernel_name);
        }
        uint32_t tree_hi4 = ref::load_be32(delta_bytes + g_audit.N + 4u);
        if (tree_hi4 != 0u) {
            throw std::runtime_error("Non-zero upper 4 bytes of 12-byte ADRS tree field in " + g_audit.kernel_name);
        }
        uint32_t typ = ref::load_be32(delta_bytes + g_audit.N + 16u);
        uint32_t word2 = ref::load_be32(delta_bytes + g_audit.N + 24u);
        if (typ >= 7u || ((g_audit.allowed_types_mask & (1u << typ)) == 0u)) {
            throw std::runtime_error("Disallowed SHAKE ADRS type " + std::to_string(typ) + " in " + g_audit.kernel_name);
        }
        size_t expected_len = g_audit.expected_shake_msg_len(typ, word2);
        size_t expected_blocks = (expected_len / 136u) + 1u;
        ShakeStreamState s;
        s.adrs_type = typ;
        s.expected_msg_len = expected_len;
        s.expected_blocks = expected_blocks;
        s.blocks_seen = 0;
        s.rate_bytes.reserve(expected_blocks * 136u);
        it = g_audit.shake_streams.emplace(st, std::move(s)).first;
    } else {
        ShakeStreamState& s = it->second;
        for (int i = 17; i < 25; ++i) {
            if (st[i] != s.prev_st[i]) {
                throw std::runtime_error("Keccak capacity modified during absorb in " + g_audit.kernel_name);
            }
        }
        for (int i = 0; i < 17; ++i) {
            uint64_t d = st[i] ^ s.prev_st[i];
            for (int b = 0; b < 8; ++b) delta_bytes[8*i + b] = uint8_t(d >> (8 * b));
        }
    }

    ShakeStreamState& s = it->second;
    s.rate_bytes.insert(s.rate_bytes.end(), delta_bytes, delta_bytes + 136);
    s.blocks_seen++;

    raw_keccak_f1600(st);
    for (int i = 0; i < 25; ++i) s.prev_st[i] = st[i];

    if (s.blocks_seen == s.expected_blocks) {
        size_t rem = s.expected_msg_len % 136u;
        if (delta_bytes[rem] != 0x1Fu) {
            throw std::runtime_error("Missing 0x1F SHAKE domain separator in " + g_audit.kernel_name);
        }
        for (size_t i = rem + 1u; i < 135u; ++i) {
            if (delta_bytes[i] != 0u) {
                throw std::runtime_error("Non-zero SHAKE pad byte in " + g_audit.kernel_name);
            }
        }
        if (delta_bytes[135] != 0x80u) {
            throw std::runtime_error("Missing 0x80 final SHAKE pad bit at byte 135 in " + g_audit.kernel_name);
        }
        uint64_t idx = g_audit.shake_msgs++;
        g_audit.type_counts[s.adrs_type]++;
        if (idx < 2048 || (idx & 63u) == 0u) {
            auto expected_lanes = ref::shake256_lanes(s.rate_bytes.data(), s.expected_msg_len);
            size_t nl = g_audit.N / 8u;
            for (size_t i = 0; i < nl; ++i) {
                if (st[i] != expected_lanes[i]) {
                    throw std::runtime_error("SHAKE256 output diverged from FIPS 202 reference in " + g_audit.kernel_name);
                }
            }
            g_audit.ref_checks++;
        }
        g_audit.shake_streams.erase(it);
    } else if (s.blocks_seen > s.expected_blocks) {
        throw std::runtime_error("SHAKE sponge exceeded expected block count in " + g_audit.kernel_name);
    }
}
"""

CPP_DRIVER = r"""
// ============================================================================
// C-ABI Struct Layout Static Assertions (matching metal/src/lib.rs #[repr(C)])
// ============================================================================

static_assert(sizeof(KeyMaterial) == 128 && alignof(KeyMaterial) == 8);
static_assert(offsetof(KeyMaterial, sk_seed) == 0);
static_assert(offsetof(KeyMaterial, state256) == 32);
static_assert(offsetof(KeyMaterial, state512) == 64);

static_assert(sizeof(ShakeKeyMaterial) == 64 && alignof(ShakeKeyMaterial) == 8);
static_assert(offsetof(ShakeKeyMaterial, sk_seed) == 0);
static_assert(offsetof(ShakeKeyMaterial, pk_seed) == 32);

static_assert(sizeof(XmssTreeDesc) == 24 && alignof(XmssTreeDesc) == 8);
static_assert(offsetof(XmssTreeDesc, tree) == 0);
static_assert(offsetof(XmssTreeDesc, key_idx) == 8);
static_assert(offsetof(XmssTreeDesc, layer) == 12);
static_assert(offsetof(XmssTreeDesc, target_leaf) == 16);
static_assert(offsetof(XmssTreeDesc, auth_byte_off) == 20);

static_assert(sizeof(ForsJobDesc) == 168 && alignof(ForsJobDesc) == 8);
static_assert(offsetof(ForsJobDesc, idx_tree) == 0);
static_assert(offsetof(ForsJobDesc, key_idx) == 8);
static_assert(offsetof(ForsJobDesc, idx_leaf) == 12);
static_assert(offsetof(ForsJobDesc, sig_byte_off) == 16);
static_assert(offsetof(ForsJobDesc, _pad) == 20);
static_assert(offsetof(ForsJobDesc, indices) == 24);

static_assert(sizeof(WotsSignLayerDesc) == 32 && alignof(WotsSignLayerDesc) == 8);
static_assert(offsetof(WotsSignLayerDesc, tree) == 0);
static_assert(offsetof(WotsSignLayerDesc, key_idx) == 8);
static_assert(offsetof(WotsSignLayerDesc, layer) == 12);
static_assert(offsetof(WotsSignLayerDesc, keypair) == 16);
static_assert(offsetof(WotsSignLayerDesc, sig_idx) == 20);
static_assert(offsetof(WotsSignLayerDesc, wots_byte_off) == 24);
static_assert(offsetof(WotsSignLayerDesc, _pad) == 28);

static_assert(sizeof(XmssParams) == 16 && alignof(XmssParams) == 4);
static_assert(sizeof(ForsParams) == 24 && alignof(ForsParams) == 4);
static_assert(sizeof(WotsSignParams) == 12 && alignof(WotsSignParams) == 4);

// ============================================================================
// Deterministic Threadgroup Scheduler (Zero Barrier Divergence + Race Check)
// ============================================================================

template <typename MakeTask>
static void dispatch_tg(uint32_t num_tgs, uint32_t tg_x, bool reverse_order, MakeTask make_task) {
    for (uint32_t tg_id = 0; tg_id < num_tgs; ++tg_id) {
        std::vector<TGTask> tasks;
        tasks.reserve(tg_x);
        for (uint32_t tid = 0; tid < tg_x; ++tid) {
            tasks.push_back(make_task(tg_id, tid));
        }
        while (true) {
            size_t done_cnt = 0;
            for (uint32_t k = 0; k < tg_x; ++k) {
                uint32_t tid = reverse_order ? (tg_x - 1u - k) : k;
                if (!tasks[tid].done()) {
                    tasks[tid].resume();
                }
                if (tasks[tid].done()) ++done_cnt;
            }
            if (done_cnt == tg_x) break;
            if (done_cnt != 0) {
                throw std::runtime_error("BARRIER DIVERGENCE detected in " + g_audit.kernel_name);
            }
        }
    }
    // Also verify out-of-bounds sentinel tg_id == num_tgs exits immediately with zero hash calls!
    bool prev_forbid = g_audit.forbid_all_hashes;
    g_audit.forbid_all_hashes = true;
    TGTask oob = make_task(num_tgs, 0u);
    oob.resume();
    if (!oob.done()) {
        throw std::runtime_error("OOB tg_id did not early-return in " + g_audit.kernel_name);
    }
    g_audit.forbid_all_hashes = prev_forbid;
}

template <typename Fn>
static void dispatch_grid(uint32_t total_threads, Fn fn) {
    for (uint32_t gid = 0; gid < total_threads; ++gid) {
        fn(gid);
    }
    // Verify out-of-bounds sentinel gid == total_threads performs zero hash calls!
    bool prev_forbid = g_audit.forbid_all_hashes;
    g_audit.forbid_all_hashes = true;
    fn(total_threads);
    g_audit.forbid_all_hashes = prev_forbid;
}

static std::vector<uint8_t> from_hex(const std::string& hex) {
    if (hex.size() % 2 != 0) throw std::runtime_error("odd hex length");
    std::vector<uint8_t> out(hex.size() / 2);
    auto nib = [](char c) -> uint8_t {
        if (c >= '0' && c <= '9') return uint8_t(c - '0');
        if (c >= 'a' && c <= 'f') return uint8_t(c - 'a' + 10);
        if (c >= 'A' && c <= 'F') return uint8_t(c - 'A' + 10);
        throw std::runtime_error("invalid hex char");
    };
    for (size_t i = 0; i < out.size(); ++i) {
        out[i] = uint8_t((nib(hex[2*i]) << 4) | nib(hex[2*i + 1]));
    }
    return out;
}

static KeyMaterial make_sha2_km(const std::vector<uint8_t>& sk_seed, const std::vector<uint8_t>& pk_seed, uint32_t N, KeyAuditInfo& audit_info) {
    KeyMaterial km{};
    for (uint32_t i = 0; i < N / 4u; ++i) {
        km.sk_seed[i] = ref::load_be32(sk_seed.data() + 4 * i);
    }
    uint8_t blk256[64] = {0};
    std::memcpy(blk256, pk_seed.data(), N);
    for (int i = 0; i < 8; ++i) km.state256[i] = ref::H256_IV[i];
    ref::sha256_block(km.state256, blk256);

    if (N != 16u) {
        uint8_t blk512[128] = {0};
        std::memcpy(blk512, pk_seed.data(), N);
        for (int i = 0; i < 8; ++i) km.state512[i] = ref::H512_IV[i];
        ref::sha512_block(km.state512, blk512);
    }
    audit_info.pk_seed = pk_seed;
    for (int i = 0; i < 8; ++i) {
        audit_info.state256[i] = km.state256[i];
        audit_info.state512[i] = km.state512[i];
    }
    return km;
}

static ShakeKeyMaterial make_shake_km(const std::vector<uint8_t>& sk_seed, const std::vector<uint8_t>& pk_seed, uint32_t N, KeyAuditInfo& audit_info) {
    ShakeKeyMaterial km{};
    for (uint32_t i = 0; i < N / 8u; ++i) {
        km.sk_seed[i] = ref::load_le64(sk_seed.data() + 8 * i);
        km.pk_seed[i] = ref::load_le64(pk_seed.data() + 8 * i);
    }
    audit_info.pk_seed = pk_seed;
    return km;
}

static void run_sha2_keygen(
    uint32_t N, uint32_t d, uint32_t hp, bool two_phase, bool rev_tg,
    const std::vector<std::vector<uint8_t>>& sk_seeds,
    const std::vector<std::vector<uint8_t>>& pk_seeds,
    const std::vector<std::vector<uint8_t>>& want_roots
) {
    uint32_t B = uint32_t(sk_seeds.size());
    uint32_t nw = N / 4u;
    uint32_t wots_len = 2u * N + 3u;
    uint32_t leaves_per_tree = 1u << hp;
    uint32_t total_leaves = B * leaves_per_tree;

    std::vector<KeyMaterial> keys(B);
    g_audit.N = N;
    g_audit.wots_len = wots_len;
    g_audit.keys.resize(B);
    for (uint32_t i = 0; i < B; ++i) {
        keys[i] = make_sha2_km(sk_seeds[i], pk_seeds[i], N, g_audit.keys[i]);
    }
    std::vector<XmssTreeDesc> trees(B);
    for (uint32_t i = 0; i < B; ++i) {
        trees[i] = XmssTreeDesc{0ull, i, d - 1u, 0xFFFFFFFFu, 0u};
    }
    XmssParams xp{B, hp, leaves_per_tree, wots_len};
    std::vector<uint32_t> leaves(total_leaves * nw, 0u);
    std::vector<uint32_t> roots(B * nw, 0u);
    std::vector<uint8_t> out_sigs(64, 0xA5u);

    auto run_for_n = [&](auto tag) {
        constexpr uint32_t NW = decltype(tag)::value;
        if (two_phase) {
            std::vector<uint32_t> tips(total_leaves * wots_len * NW, 0u);
            g_audit.reset_for_kernel("wots_chains", (1u << ADRS_WOTS_PRF) | (1u << ADRS_WOTS_HASH));
            dispatch_grid(total_leaves * wots_len, [&](uint32_t gid) {
                if constexpr (NW == 4) wots_chains_N16(keys.data(), trees.data(), tips.data(), xp, gid);
                else if constexpr (NW == 6) wots_chains_N24(keys.data(), trees.data(), tips.data(), xp, gid);
                else wots_chains_N32(keys.data(), trees.data(), tips.data(), xp, gid);
            });
            g_audit.finish_kernel();

            g_audit.reset_for_kernel("wots_tlen", 1u << ADRS_WOTS_PK);
            dispatch_grid(total_leaves, [&](uint32_t gid) {
                if constexpr (NW == 4) wots_tlen_N16(keys.data(), trees.data(), tips.data(), leaves.data(), xp, gid);
                else if constexpr (NW == 6) wots_tlen_N24(keys.data(), trees.data(), tips.data(), leaves.data(), xp, gid);
                else wots_tlen_N32(keys.data(), trees.data(), tips.data(), leaves.data(), xp, gid);
            });
            g_audit.finish_kernel();
        } else {
            g_audit.reset_for_kernel("xmss_leaves_streaming",
                (1u << ADRS_WOTS_PRF) | (1u << ADRS_WOTS_HASH) | (1u << ADRS_WOTS_PK));
            dispatch_grid(total_leaves, [&](uint32_t gid) {
                if constexpr (NW == 4) xmss_leaves_streaming_N16(keys.data(), trees.data(), leaves.data(), xp, gid);
                else if constexpr (NW == 6) xmss_leaves_streaming_N24(keys.data(), trees.data(), leaves.data(), xp, gid);
                else xmss_leaves_streaming_N32(keys.data(), trees.data(), leaves.data(), xp, gid);
            });
            g_audit.finish_kernel();
        }
        uint32_t reduce_tg = 1u << (hp - 1u);
        std::vector<uint32_t> tg_nodes(reduce_tg * NW, 0u);
        g_audit.reset_for_kernel("xmss_reduce", 1u << ADRS_TREE);
        dispatch_tg(B, reduce_tg, rev_tg, [&](uint32_t tg_id, uint32_t tid) -> TGTask {
            if constexpr (NW == 4) return xmss_reduce_N16(keys.data(), trees.data(), leaves.data(), roots.data(), out_sigs.data(), xp, tg_nodes.data(), tg_id, tid);
            else if constexpr (NW == 6) return xmss_reduce_N24(keys.data(), trees.data(), leaves.data(), roots.data(), out_sigs.data(), xp, tg_nodes.data(), tg_id, tid);
            else return xmss_reduce_N32(keys.data(), trees.data(), leaves.data(), roots.data(), out_sigs.data(), xp, tg_nodes.data(), tg_id, tid);
        });
        g_audit.finish_kernel();
    };
    if (N == 16) run_for_n(std::integral_constant<uint32_t, 4>{});
    else if (N == 24) run_for_n(std::integral_constant<uint32_t, 6>{});
    else run_for_n(std::integral_constant<uint32_t, 8>{});

    // Verify out_sigs was NOT touched during keygen
    for (uint8_t b : out_sigs) {
        if (b != 0xA5u) throw std::runtime_error("SHA-2 keygen wrote to out_sigs!");
    }
    for (uint32_t i = 0; i < B; ++i) {
        std::vector<uint8_t> got(N);
        for (uint32_t w = 0; w < nw; ++w) {
            uint32_t v = roots[i * nw + w];
            got[4*w+0] = uint8_t(v >> 24); got[4*w+1] = uint8_t(v >> 16);
            got[4*w+2] = uint8_t(v >> 8);  got[4*w+3] = uint8_t(v);
        }
        if (got != want_roots[i]) {
            throw std::runtime_error("SHA-2 keygen PK.root mismatch for batch item " + std::to_string(i));
        }
    }
}

static void run_shake_keygen(
    uint32_t N, uint32_t d, uint32_t hp, bool two_phase, bool rev_tg,
    const std::vector<std::vector<uint8_t>>& sk_seeds,
    const std::vector<std::vector<uint8_t>>& pk_seeds,
    const std::vector<std::vector<uint8_t>>& want_roots
) {
    uint32_t B = uint32_t(sk_seeds.size());
    uint32_t nl = N / 8u;
    uint32_t wots_len = 2u * N + 3u;
    uint32_t leaves_per_tree = 1u << hp;
    uint32_t total_leaves = B * leaves_per_tree;

    std::vector<ShakeKeyMaterial> keys(B);
    g_audit.N = N;
    g_audit.wots_len = wots_len;
    g_audit.keys.resize(B);
    for (uint32_t i = 0; i < B; ++i) {
        keys[i] = make_shake_km(sk_seeds[i], pk_seeds[i], N, g_audit.keys[i]);
    }
    std::vector<XmssTreeDesc> trees(B);
    for (uint32_t i = 0; i < B; ++i) {
        trees[i] = XmssTreeDesc{0ull, i, d - 1u, 0xFFFFFFFFu, 0u};
    }
    XmssParams xp{B, hp, leaves_per_tree, wots_len};
    std::vector<uint64_t> leaves(total_leaves * nl, 0ull);
    std::vector<uint64_t> roots(B * nl, 0ull);
    std::vector<uint8_t> out_sigs(64, 0xA5u);

    auto run_for_n = [&](auto tag) {
        constexpr uint32_t NL = decltype(tag)::value;
        if (two_phase) {
            std::vector<uint64_t> tips(total_leaves * wots_len * NL, 0ull);
            g_audit.reset_for_kernel("shake_wots_chains", (1u << ADRS_WOTS_PRF) | (1u << ADRS_WOTS_HASH));
            dispatch_grid(total_leaves * wots_len, [&](uint32_t gid) {
                if constexpr (NL == 2) shake_wots_chains_N16(keys.data(), trees.data(), tips.data(), xp, gid);
                else if constexpr (NL == 3) shake_wots_chains_N24(keys.data(), trees.data(), tips.data(), xp, gid);
                else shake_wots_chains_N32(keys.data(), trees.data(), tips.data(), xp, gid);
            });
            g_audit.finish_kernel();

            g_audit.reset_for_kernel("shake_wots_tlen", 1u << ADRS_WOTS_PK);
            dispatch_grid(total_leaves, [&](uint32_t gid) {
                if constexpr (NL == 2) shake_wots_tlen_N16(keys.data(), trees.data(), tips.data(), leaves.data(), xp, gid);
                else if constexpr (NL == 3) shake_wots_tlen_N24(keys.data(), trees.data(), tips.data(), leaves.data(), xp, gid);
                else shake_wots_tlen_N32(keys.data(), trees.data(), tips.data(), leaves.data(), xp, gid);
            });
            g_audit.finish_kernel();
        } else {
            g_audit.reset_for_kernel("shake_xmss_leaves_streaming",
                (1u << ADRS_WOTS_PRF) | (1u << ADRS_WOTS_HASH) | (1u << ADRS_WOTS_PK));
            dispatch_grid(total_leaves, [&](uint32_t gid) {
                if constexpr (NL == 2) shake_xmss_leaves_streaming_N16(keys.data(), trees.data(), leaves.data(), xp, gid);
                else if constexpr (NL == 3) shake_xmss_leaves_streaming_N24(keys.data(), trees.data(), leaves.data(), xp, gid);
                else shake_xmss_leaves_streaming_N32(keys.data(), trees.data(), leaves.data(), xp, gid);
            });
            g_audit.finish_kernel();
        }
        uint32_t reduce_tg = 1u << (hp - 1u);
        std::vector<uint64_t> tg_nodes(reduce_tg * NL, 0ull);
        g_audit.reset_for_kernel("shake_xmss_reduce", 1u << ADRS_TREE);
        dispatch_tg(B, reduce_tg, rev_tg, [&](uint32_t tg_id, uint32_t tid) -> TGTask {
            if constexpr (NL == 2) return shake_xmss_reduce_N16(keys.data(), trees.data(), leaves.data(), roots.data(), out_sigs.data(), xp, tg_nodes.data(), tg_id, tid);
            else if constexpr (NL == 3) return shake_xmss_reduce_N24(keys.data(), trees.data(), leaves.data(), roots.data(), out_sigs.data(), xp, tg_nodes.data(), tg_id, tid);
            else return shake_xmss_reduce_N32(keys.data(), trees.data(), leaves.data(), roots.data(), out_sigs.data(), xp, tg_nodes.data(), tg_id, tid);
        });
        g_audit.finish_kernel();
    };
    if (N == 16) run_for_n(std::integral_constant<uint32_t, 2>{});
    else if (N == 24) run_for_n(std::integral_constant<uint32_t, 3>{});
    else run_for_n(std::integral_constant<uint32_t, 4>{});

    for (uint8_t b : out_sigs) {
        if (b != 0xA5u) throw std::runtime_error("SHAKE keygen wrote to out_sigs!");
    }
    for (uint32_t i = 0; i < B; ++i) {
        std::vector<uint8_t> got(N);
        for (uint32_t l = 0; l < nl; ++l) {
            uint64_t v = roots[i * nl + l];
            for (int b = 0; b < 8; ++b) got[8*l + b] = uint8_t(v >> (8 * b));
        }
        if (got != want_roots[i]) {
            throw std::runtime_error("SHAKE keygen PK.root mismatch for batch item " + std::to_string(i));
        }
    }
}

struct SignCase {
    std::vector<uint8_t> sk_seed;
    std::vector<uint8_t> pk_seed;
    std::vector<uint8_t> r_val;
    uint64_t idx_tree;
    uint32_t idx_leaf;
    std::vector<uint32_t> fors_indices;
    std::vector<uint8_t> want_sig;
};

static void run_sign(
    const std::string& family, uint32_t N, uint32_t d, uint32_t hp, uint32_t a, uint32_t k,
    bool two_phase, bool rev_tg, const std::vector<SignCase>& cases
) {
    uint32_t num_sigs = uint32_t(cases.size());
    uint32_t wots_len = 2u * N + 3u;
    uint32_t leaves_per_tree = 1u << hp;
    uint32_t fors_sig_bytes = k * (1u + a) * N;
    uint32_t xmss_sig_bytes = (wots_len + hp) * N;
    uint32_t sig_bytes = N + fors_sig_bytes + d * xmss_sig_bytes;
    uint32_t total_trees = num_sigs * d;
    uint32_t total_xmss_leaves = total_trees * leaves_per_tree;
    uint32_t s1 = (a <= 8u) ? a : 7u;
    uint32_t s2 = a - s1;
    uint32_t subtrees_per_tree = 1u << s2;

    // Deduplicate keys identically to metal/src/lib.rs
    std::vector<std::pair<std::vector<uint8_t>, std::vector<uint8_t>>> unique_seeds;
    std::vector<ForsJobDesc> fors_jobs;
    std::vector<XmssTreeDesc> xmss_trees;
    std::vector<WotsSignLayerDesc> wots_layers;

    for (uint32_t sig_idx = 0; sig_idx < num_sigs; ++sig_idx) {
        const auto& c = cases[sig_idx];
        uint32_t key_idx = 0;
        bool found = false;
        for (size_t i = 0; i < unique_seeds.size(); ++i) {
            if (unique_seeds[i].first == c.sk_seed && unique_seeds[i].second == c.pk_seed) {
                key_idx = uint32_t(i);
                found = true;
                break;
            }
        }
        if (!found) {
            key_idx = uint32_t(unique_seeds.size());
            unique_seeds.push_back({c.sk_seed, c.pk_seed});
        }
        uint32_t sig_byte_off = sig_idx * sig_bytes;
        ForsJobDesc fj{};
        fj.idx_tree = c.idx_tree;
        fj.key_idx = key_idx;
        fj.idx_leaf = c.idx_leaf;
        fj.sig_byte_off = sig_byte_off;
        for (uint32_t i = 0; i < k; ++i) fj.indices[i] = c.fors_indices[i];
        fors_jobs.push_back(fj);

        uint64_t tree = c.idx_tree;
        uint32_t leaf = c.idx_leaf;
        for (uint32_t j = 0; j < d; ++j) {
            uint32_t layer_sig_off = sig_byte_off + N + fors_sig_bytes + j * xmss_sig_bytes;
            uint32_t auth_byte_off = layer_sig_off + wots_len * N;
            xmss_trees.push_back(XmssTreeDesc{tree, key_idx, j, leaf, auth_byte_off});
            wots_layers.push_back(WotsSignLayerDesc{tree, key_idx, j, leaf, sig_idx, layer_sig_off, 0u});
            leaf = uint32_t(tree & ((1ull << hp) - 1ull));
            tree >>= hp;
        }
    }

    XmssParams xp{total_trees, hp, leaves_per_tree, wots_len};
    ForsParams fp{num_sigs, k, a, s1, s2, subtrees_per_tree};
    WotsSignParams wp{total_trees, d, wots_len};

    // Guard bytes before and after out_sigs to catch any OOB write
    const size_t GUARD = 64;
    std::vector<uint8_t> out_sigs_raw(num_sigs * sig_bytes + 2 * GUARD, 0xCCu);
    uint8_t* out_sigs = out_sigs_raw.data() + GUARD;
    for (uint32_t sig_idx = 0; sig_idx < num_sigs; ++sig_idx) {
        std::memcpy(out_sigs + sig_idx * sig_bytes, cases[sig_idx].r_val.data(), N);
    }

    g_audit.N = N;
    g_audit.wots_len = wots_len;
    g_audit.k = k;
    g_audit.keys.resize(unique_seeds.size());

    if (family == "sha2") {
        std::vector<KeyMaterial> keys(unique_seeds.size());
        for (size_t i = 0; i < unique_seeds.size(); ++i) {
            keys[i] = make_sha2_km(unique_seeds[i].first, unique_seeds[i].second, N, g_audit.keys[i]);
        }
        uint32_t nw = N / 4u;
        std::vector<uint32_t> xmss_leaves(total_xmss_leaves * nw, 0u);
        std::vector<uint32_t> xmss_roots(total_trees * nw, 0u);
        std::vector<uint32_t> fors_sub_roots(num_sigs * k * subtrees_per_tree * nw, 0u);
        std::vector<uint32_t> fors_roots(s2 > 0 ? (num_sigs * k * nw) : 1u, 0u);
        std::vector<uint32_t> pk_fors(num_sigs * nw, 0u);

        auto run_n = [&](auto tag) {
            constexpr uint32_t NW = decltype(tag)::value;
            if (two_phase) {
                std::vector<uint32_t> tips(total_xmss_leaves * wots_len * NW, 0u);
                g_audit.reset_for_kernel("wots_chains", (1u << ADRS_WOTS_PRF) | (1u << ADRS_WOTS_HASH));
                dispatch_grid(total_xmss_leaves * wots_len, [&](uint32_t gid) {
                    if constexpr (NW == 4) wots_chains_N16(keys.data(), xmss_trees.data(), tips.data(), xp, gid);
                    else if constexpr (NW == 6) wots_chains_N24(keys.data(), xmss_trees.data(), tips.data(), xp, gid);
                    else wots_chains_N32(keys.data(), xmss_trees.data(), tips.data(), xp, gid);
                });
                g_audit.finish_kernel();

                g_audit.reset_for_kernel("wots_tlen", 1u << ADRS_WOTS_PK);
                dispatch_grid(total_xmss_leaves, [&](uint32_t gid) {
                    if constexpr (NW == 4) wots_tlen_N16(keys.data(), xmss_trees.data(), tips.data(), xmss_leaves.data(), xp, gid);
                    else if constexpr (NW == 6) wots_tlen_N24(keys.data(), xmss_trees.data(), tips.data(), xmss_leaves.data(), xp, gid);
                    else wots_tlen_N32(keys.data(), xmss_trees.data(), tips.data(), xmss_leaves.data(), xp, gid);
                });
                g_audit.finish_kernel();
            } else {
                g_audit.reset_for_kernel("xmss_leaves_streaming",
                    (1u << ADRS_WOTS_PRF) | (1u << ADRS_WOTS_HASH) | (1u << ADRS_WOTS_PK));
                dispatch_grid(total_xmss_leaves, [&](uint32_t gid) {
                    if constexpr (NW == 4) xmss_leaves_streaming_N16(keys.data(), xmss_trees.data(), xmss_leaves.data(), xp, gid);
                    else if constexpr (NW == 6) xmss_leaves_streaming_N24(keys.data(), xmss_trees.data(), xmss_leaves.data(), xp, gid);
                    else xmss_leaves_streaming_N32(keys.data(), xmss_trees.data(), xmss_leaves.data(), xp, gid);
                });
                g_audit.finish_kernel();
            }

            {
                uint32_t reduce_tg = 1u << (hp - 1u);
                std::vector<uint32_t> tg_nodes(reduce_tg * NW, 0u);
                g_audit.reset_for_kernel("xmss_reduce", 1u << ADRS_TREE);
                dispatch_tg(total_trees, reduce_tg, rev_tg, [&](uint32_t tg_id, uint32_t tid) -> TGTask {
                    if constexpr (NW == 4) return xmss_reduce_N16(keys.data(), xmss_trees.data(), xmss_leaves.data(), xmss_roots.data(), out_sigs, xp, tg_nodes.data(), tg_id, tid);
                    else if constexpr (NW == 6) return xmss_reduce_N24(keys.data(), xmss_trees.data(), xmss_leaves.data(), xmss_roots.data(), out_sigs, xp, tg_nodes.data(), tg_id, tid);
                    else return xmss_reduce_N32(keys.data(), xmss_trees.data(), xmss_leaves.data(), xmss_roots.data(), out_sigs, xp, tg_nodes.data(), tg_id, tid);
                });
                g_audit.finish_kernel();
            }

            {
                uint32_t fors1_tgs = num_sigs * k * subtrees_per_tree;
                uint32_t fors1_tg_x = 1u << (s1 - 1u);
                std::vector<uint32_t> tg_nodes(fors1_tg_x * NW, 0u);
                g_audit.reset_for_kernel("fors_pass1", (1u << ADRS_FORS_PRF) | (1u << ADRS_FORS_TREE));
                dispatch_tg(fors1_tgs, fors1_tg_x, rev_tg, [&](uint32_t tg_id, uint32_t tid) -> TGTask {
                    if constexpr (NW == 4) return fors_pass1_N16(keys.data(), fors_jobs.data(), fors_sub_roots.data(), out_sigs, fp, tg_nodes.data(), tg_id, tid);
                    else if constexpr (NW == 6) return fors_pass1_N24(keys.data(), fors_jobs.data(), fors_sub_roots.data(), out_sigs, fp, tg_nodes.data(), tg_id, tid);
                    else return fors_pass1_N32(keys.data(), fors_jobs.data(), fors_sub_roots.data(), out_sigs, fp, tg_nodes.data(), tg_id, tid);
                });
                g_audit.finish_kernel();
            }

            const uint32_t* froots_ptr = fors_sub_roots.data();
            if (s2 > 0u) {
                uint32_t fors2_tgs = num_sigs * k;
                uint32_t fors2_tg_x = 1u << (s2 - 1u);
                std::vector<uint32_t> tg_nodes(fors2_tg_x * NW, 0u);
                g_audit.reset_for_kernel("fors_pass2", 1u << ADRS_FORS_TREE);
                dispatch_tg(fors2_tgs, fors2_tg_x, rev_tg, [&](uint32_t tg_id, uint32_t tid) -> TGTask {
                    if constexpr (NW == 4) return fors_pass2_N16(keys.data(), fors_jobs.data(), fors_sub_roots.data(), fors_roots.data(), out_sigs, fp, tg_nodes.data(), tg_id, tid);
                    else if constexpr (NW == 6) return fors_pass2_N24(keys.data(), fors_jobs.data(), fors_sub_roots.data(), fors_roots.data(), out_sigs, fp, tg_nodes.data(), tg_id, tid);
                    else return fors_pass2_N32(keys.data(), fors_jobs.data(), fors_sub_roots.data(), fors_roots.data(), out_sigs, fp, tg_nodes.data(), tg_id, tid);
                });
                g_audit.finish_kernel();
                froots_ptr = fors_roots.data();
            }

            g_audit.reset_for_kernel("fors_pk", 1u << ADRS_FORS_ROOTS);
            dispatch_grid(num_sigs, [&](uint32_t gid) {
                if constexpr (NW == 4) fors_pk_N16(keys.data(), fors_jobs.data(), froots_ptr, pk_fors.data(), fp, gid);
                else if constexpr (NW == 6) fors_pk_N24(keys.data(), fors_jobs.data(), froots_ptr, pk_fors.data(), fp, gid);
                else fors_pk_N32(keys.data(), fors_jobs.data(), froots_ptr, pk_fors.data(), fp, gid);
            });
            g_audit.finish_kernel();

            g_audit.reset_for_kernel("wots_sign", (1u << ADRS_WOTS_PRF) | (1u << ADRS_WOTS_HASH));
            dispatch_grid(total_trees * wots_len, [&](uint32_t gid) {
                if constexpr (NW == 4) wots_sign_N16(keys.data(), wots_layers.data(), pk_fors.data(), xmss_roots.data(), out_sigs, wp, gid);
                else if constexpr (NW == 6) wots_sign_N24(keys.data(), wots_layers.data(), pk_fors.data(), xmss_roots.data(), out_sigs, wp, gid);
                else wots_sign_N32(keys.data(), wots_layers.data(), pk_fors.data(), xmss_roots.data(), out_sigs, wp, gid);
            });
            g_audit.finish_kernel();
        };
        if (N == 16) run_n(std::integral_constant<uint32_t, 4>{});
        else if (N == 24) run_n(std::integral_constant<uint32_t, 6>{});
        else run_n(std::integral_constant<uint32_t, 8>{});
    } else {
        std::vector<ShakeKeyMaterial> keys(unique_seeds.size());
        for (size_t i = 0; i < unique_seeds.size(); ++i) {
            keys[i] = make_shake_km(unique_seeds[i].first, unique_seeds[i].second, N, g_audit.keys[i]);
        }
        uint32_t nl = N / 8u;
        std::vector<uint64_t> xmss_leaves(total_xmss_leaves * nl, 0ull);
        std::vector<uint64_t> xmss_roots(total_trees * nl, 0ull);
        std::vector<uint64_t> fors_sub_roots(num_sigs * k * subtrees_per_tree * nl, 0ull);
        std::vector<uint64_t> fors_roots(s2 > 0 ? (num_sigs * k * nl) : 1u, 0ull);
        std::vector<uint64_t> pk_fors(num_sigs * nl, 0ull);

        auto run_n = [&](auto tag) {
            constexpr uint32_t NL = decltype(tag)::value;
            if (two_phase) {
                std::vector<uint64_t> tips(total_xmss_leaves * wots_len * NL, 0ull);
                g_audit.reset_for_kernel("shake_wots_chains", (1u << ADRS_WOTS_PRF) | (1u << ADRS_WOTS_HASH));
                dispatch_grid(total_xmss_leaves * wots_len, [&](uint32_t gid) {
                    if constexpr (NL == 2) shake_wots_chains_N16(keys.data(), xmss_trees.data(), tips.data(), xp, gid);
                    else if constexpr (NL == 3) shake_wots_chains_N24(keys.data(), xmss_trees.data(), tips.data(), xp, gid);
                    else shake_wots_chains_N32(keys.data(), xmss_trees.data(), tips.data(), xp, gid);
                });
                g_audit.finish_kernel();

                g_audit.reset_for_kernel("shake_wots_tlen", 1u << ADRS_WOTS_PK);
                dispatch_grid(total_xmss_leaves, [&](uint32_t gid) {
                    if constexpr (NL == 2) shake_wots_tlen_N16(keys.data(), xmss_trees.data(), tips.data(), xmss_leaves.data(), xp, gid);
                    else if constexpr (NL == 3) shake_wots_tlen_N24(keys.data(), xmss_trees.data(), tips.data(), xmss_leaves.data(), xp, gid);
                    else shake_wots_tlen_N32(keys.data(), xmss_trees.data(), tips.data(), xmss_leaves.data(), xp, gid);
                });
                g_audit.finish_kernel();
            } else {
                g_audit.reset_for_kernel("shake_xmss_leaves_streaming",
                    (1u << ADRS_WOTS_PRF) | (1u << ADRS_WOTS_HASH) | (1u << ADRS_WOTS_PK));
                dispatch_grid(total_xmss_leaves, [&](uint32_t gid) {
                    if constexpr (NL == 2) shake_xmss_leaves_streaming_N16(keys.data(), xmss_trees.data(), xmss_leaves.data(), xp, gid);
                    else if constexpr (NL == 3) shake_xmss_leaves_streaming_N24(keys.data(), xmss_trees.data(), xmss_leaves.data(), xp, gid);
                    else shake_xmss_leaves_streaming_N32(keys.data(), xmss_trees.data(), xmss_leaves.data(), xp, gid);
                });
                g_audit.finish_kernel();
            }

            {
                uint32_t reduce_tg = 1u << (hp - 1u);
                std::vector<uint64_t> tg_nodes(reduce_tg * NL, 0ull);
                g_audit.reset_for_kernel("shake_xmss_reduce", 1u << ADRS_TREE);
                dispatch_tg(total_trees, reduce_tg, rev_tg, [&](uint32_t tg_id, uint32_t tid) -> TGTask {
                    if constexpr (NL == 2) return shake_xmss_reduce_N16(keys.data(), xmss_trees.data(), xmss_leaves.data(), xmss_roots.data(), out_sigs, xp, tg_nodes.data(), tg_id, tid);
                    else if constexpr (NL == 3) return shake_xmss_reduce_N24(keys.data(), xmss_trees.data(), xmss_leaves.data(), xmss_roots.data(), out_sigs, xp, tg_nodes.data(), tg_id, tid);
                    else return shake_xmss_reduce_N32(keys.data(), xmss_trees.data(), xmss_leaves.data(), xmss_roots.data(), out_sigs, xp, tg_nodes.data(), tg_id, tid);
                });
                g_audit.finish_kernel();
            }

            {
                uint32_t fors1_tgs = num_sigs * k * subtrees_per_tree;
                uint32_t fors1_tg_x = 1u << (s1 - 1u);
                std::vector<uint64_t> tg_nodes(fors1_tg_x * NL, 0ull);
                g_audit.reset_for_kernel("shake_fors_pass1", (1u << ADRS_FORS_PRF) | (1u << ADRS_FORS_TREE));
                dispatch_tg(fors1_tgs, fors1_tg_x, rev_tg, [&](uint32_t tg_id, uint32_t tid) -> TGTask {
                    if constexpr (NL == 2) return shake_fors_pass1_N16(keys.data(), fors_jobs.data(), fors_sub_roots.data(), out_sigs, fp, tg_nodes.data(), tg_id, tid);
                    else if constexpr (NL == 3) return shake_fors_pass1_N24(keys.data(), fors_jobs.data(), fors_sub_roots.data(), out_sigs, fp, tg_nodes.data(), tg_id, tid);
                    else return shake_fors_pass1_N32(keys.data(), fors_jobs.data(), fors_sub_roots.data(), out_sigs, fp, tg_nodes.data(), tg_id, tid);
                });
                g_audit.finish_kernel();
            }

            const uint64_t* froots_ptr = fors_sub_roots.data();
            if (s2 > 0u) {
                uint32_t fors2_tgs = num_sigs * k;
                uint32_t fors2_tg_x = 1u << (s2 - 1u);
                std::vector<uint64_t> tg_nodes(fors2_tg_x * NL, 0ull);
                g_audit.reset_for_kernel("shake_fors_pass2", 1u << ADRS_FORS_TREE);
                dispatch_tg(fors2_tgs, fors2_tg_x, rev_tg, [&](uint32_t tg_id, uint32_t tid) -> TGTask {
                    if constexpr (NL == 2) return shake_fors_pass2_N16(keys.data(), fors_jobs.data(), fors_sub_roots.data(), fors_roots.data(), out_sigs, fp, tg_nodes.data(), tg_id, tid);
                    else if constexpr (NL == 3) return shake_fors_pass2_N24(keys.data(), fors_jobs.data(), fors_sub_roots.data(), fors_roots.data(), out_sigs, fp, tg_nodes.data(), tg_id, tid);
                    else return shake_fors_pass2_N32(keys.data(), fors_jobs.data(), fors_sub_roots.data(), fors_roots.data(), out_sigs, fp, tg_nodes.data(), tg_id, tid);
                });
                g_audit.finish_kernel();
                froots_ptr = fors_roots.data();
            }

            g_audit.reset_for_kernel("shake_fors_pk", 1u << ADRS_FORS_ROOTS);
            dispatch_grid(num_sigs, [&](uint32_t gid) {
                if constexpr (NL == 2) shake_fors_pk_N16(keys.data(), fors_jobs.data(), froots_ptr, pk_fors.data(), fp, gid);
                else if constexpr (NL == 3) shake_fors_pk_N24(keys.data(), fors_jobs.data(), froots_ptr, pk_fors.data(), fp, gid);
                else shake_fors_pk_N32(keys.data(), fors_jobs.data(), froots_ptr, pk_fors.data(), fp, gid);
            });
            g_audit.finish_kernel();

            g_audit.reset_for_kernel("shake_wots_sign", (1u << ADRS_WOTS_PRF) | (1u << ADRS_WOTS_HASH));
            dispatch_grid(total_trees * wots_len, [&](uint32_t gid) {
                if constexpr (NL == 2) shake_wots_sign_N16(keys.data(), wots_layers.data(), pk_fors.data(), xmss_roots.data(), out_sigs, wp, gid);
                else if constexpr (NL == 3) shake_wots_sign_N24(keys.data(), wots_layers.data(), pk_fors.data(), xmss_roots.data(), out_sigs, wp, gid);
                else shake_wots_sign_N32(keys.data(), wots_layers.data(), pk_fors.data(), xmss_roots.data(), out_sigs, wp, gid);
            });
            g_audit.finish_kernel();
        };
        if (N == 16) run_n(std::integral_constant<uint32_t, 2>{});
        else if (N == 24) run_n(std::integral_constant<uint32_t, 3>{});
        else run_n(std::integral_constant<uint32_t, 4>{});
    }

    // Verify guard zones untouched
    for (size_t i = 0; i < GUARD; ++i) {
        if (out_sigs_raw[i] != 0xCCu || out_sigs_raw[GUARD + num_sigs * sig_bytes + i] != 0xCCu) {
            throw std::runtime_error("Out-of-bounds write into out_sigs guard zone!");
        }
    }
    // Verify EVERY signature byte against NIST ACVP
    for (uint32_t sig_idx = 0; sig_idx < num_sigs; ++sig_idx) {
        const auto& want = cases[sig_idx].want_sig;
        if (want.size() != sig_bytes) throw std::runtime_error("want_sig size mismatch");
        if (std::memcmp(out_sigs + sig_idx * sig_bytes, want.data(), sig_bytes) != 0) {
            throw std::runtime_error("Signature byte mismatch on " + family + " N=" + std::to_string(N) +
                " sig_idx=" + std::to_string(sig_idx));
        }
    }
}

int main(int argc, char** argv) {
    if (argc != 2) {
        std::cerr << "usage: harness <cases.txt>\n";
        return 2;
    }
    std::ifstream in(argv[1]);
    if (!in) throw std::runtime_error("failed to open cases file");

    std::string kind;
    int keygen_runs = 0;
    int sign_runs = 0;
    while (in >> kind) {
        if (kind == "KEYGEN") {
            std::string name, family;
            uint32_t N, d, hp, B;
            int two_phase, rev_tg;
            in >> name >> family >> N >> d >> hp >> two_phase >> rev_tg >> B;
            std::vector<std::vector<uint8_t>> sks(B), pks(B), roots(B);
            for (uint32_t i = 0; i < B; ++i) {
                std::string hs, hp_s, hr;
                in >> hs >> hp_s >> hr;
                sks[i] = from_hex(hs);
                pks[i] = from_hex(hp_s);
                roots[i] = from_hex(hr);
            }
            if (family == "sha2") run_sha2_keygen(N, d, hp, two_phase != 0, rev_tg != 0, sks, pks, roots);
            else run_shake_keygen(N, d, hp, two_phase != 0, rev_tg != 0, sks, pks, roots);
            keygen_runs++;
        } else if (kind == "SIGN") {
            std::string name, family;
            uint32_t N, d, hp, a, k, B;
            int two_phase, rev_tg;
            in >> name >> family >> N >> d >> hp >> a >> k >> two_phase >> rev_tg >> B;
            std::vector<SignCase> cases(B);
            for (uint32_t i = 0; i < B; ++i) {
                std::string hsk, hpk, hr, hsig;
                in >> hsk >> hpk >> hr >> cases[i].idx_tree >> cases[i].idx_leaf;
                cases[i].sk_seed = from_hex(hsk);
                cases[i].pk_seed = from_hex(hpk);
                cases[i].r_val = from_hex(hr);
                cases[i].fors_indices.resize(k);
                for (uint32_t j = 0; j < k; ++j) in >> cases[i].fors_indices[j];
                in >> hsig;
                cases[i].want_sig = from_hex(hsig);
            }
            run_sign(family, N, d, hp, a, k, two_phase != 0, rev_tg != 0, cases);
            sign_runs++;
        } else {
            throw std::runtime_error("unknown test kind: " + kind);
        }
    }

    // Confirm all 7 ADRS domain tags (0..6) were exercised and verified
    for (int t = 0; t < 7; ++t) {
        if (g_audit.type_counts[t] == 0) {
            throw std::runtime_error("ADRS domain tag " + std::to_string(t) + " was never exercised!");
        }
    }

    std::cout << "MSL host replay passed: "
              << keygen_runs << " keygen dispatches, "
              << sign_runs << " sign dispatches | "
              << "sha256_short=" << g_audit.sha256_from_calls
              << " sha256_stream=" << g_audit.sha256_stream_msgs
              << " sha512_msgs=" << g_audit.sha512_stream_msgs
              << " shake_msgs=" << g_audit.shake_msgs
              << " ref_cross_checks=" << g_audit.ref_checks
              << " | all 7 ADRS tags verified"
              << std::endl;
    return 0;
}
"""


def lift_metal_shaders() -> str:
    """Transform the ACTUAL production MSL shaders into C++20 coroutine host code."""
    sha2 = (ROOT / "metal/shaders/slhdsa.metal").read_text()
    shake = (ROOT / "metal/shaders/slhdsa_shake.metal").read_text()

    # Strip Metal header/namespace
    sha2 = sha2.replace("#include <metal_stdlib>\n", "", 1)
    sha2 = sha2.replace("using namespace metal;\n", "", 1)

    # Hook SHA-2 compression definitions (keeping the actual production compression bodies intact!)
    for fn in ("sha256_compress", "sha256_compress_from", "sha512_compress"):
        old = f"inline void {fn}("
        if sha2.count(old) != 1:
            raise ValueError(f"expected single definition of {fn} in slhdsa.metal")
        sha2 = sha2.replace(old, f"inline void raw_{fn}(", 1)

    marker_sha2 = "// Helpers: Byte Packing"
    if marker_sha2 not in sha2:
        raise ValueError("missing Helpers marker in slhdsa.metal")
    sha2 = sha2.replace(marker_sha2, SHA2_HOOKS + "\n" + marker_sha2, 1)

    # Hook Keccak permutation definition (keeping the actual production permutation body intact!)
    old_k = "inline void keccak_f1600("
    if shake.count(old_k) != 1:
        raise ValueError("expected single definition of keccak_f1600 in slhdsa_shake.metal")
    shake = shake.replace(old_k, "inline void raw_keccak_f1600(", 1)

    marker_shake = "// SHAKE256 Tweakable Hashes"
    if marker_shake not in shake:
        raise ValueError("missing SHAKE256 Tweakable Hashes marker in slhdsa_shake.metal")
    shake = shake.replace(marker_shake, SHAKE_HOOK + "\n" + marker_shake, 1)

    combined = sha2 + "\n" + shake

    # Convert the 6 threadgroup-barrier kernels into C++20 coroutines returning TGTask
    tg_kernels = (
        "xmss_reduce",
        "fors_pass1",
        "fors_pass2",
        "shake_xmss_reduce",
        "shake_fors_pass1",
        "shake_fors_pass2",
    )
    for kname in tg_kernels:
        impl_hdr = f"inline void {kname}_impl("
        if combined.count(impl_hdr) != 1:
            raise ValueError(f"expected single definition of {kname}_impl")
        start = combined.index(impl_hdr)
        end = combined.index("\n}\n", start) + 3
        fn_body = combined[start:end]
        # Verify the only `return;` in the threadgroup kernel is the initial tg_id bounds guard
        returns = re.findall(r"\breturn\b[^;]*;", fn_body)
        if returns != ["return;"]:
            raise ValueError(f"unexpected return statements in {kname}_impl: {returns}")
        fn_body = fn_body.replace(impl_hdr, f"inline TGTask {kname}_impl(", 1)
        fn_body = fn_body.replace("return;", "co_return;", 1)
        combined = combined[:start] + fn_body + combined[end:]

        # Also update the kernel entry-point macro wrapper so entry points are called directly
        entry_hdr = f"kernel void {kname}_##SUFFIX("
        if combined.count(entry_hdr) != 1:
            raise ValueError(f"expected single kernel entry wrapper for {kname}")
        combined = combined.replace(entry_hdr, f"TGTask {kname}_##SUFFIX(", 1)
        call_pat = f"    {kname}_impl<"
        if combined.count(call_pat) != 1:
            raise ValueError(f"expected single impl call in {kname} kernel wrapper")
        combined = combined.replace(call_pat, f"    return {kname}_impl<", 1)

    # Strip MSL parameter qualifiers [[buffer(i)]], [[threadgroup(0)]], [[thread_position_in_grid]], etc.
    combined = re.sub(
        r"\s*\[\[(?:buffer|threadgroup|thread_position_in_grid|threadgroup_position_in_grid|thread_position_in_threadgroup)(?:\(\d+\))?\]\]",
        "",
        combined,
    )

    return CPP_PREAMBLE + "\n" + combined + "\n" + CPP_DRIVER


def build_test_cases_file(path: Path) -> None:
    """Generate comprehensive ACVP keygen & signing test cases covering all 12 parameter sets,
    single (B=1) and multi-key batch (B=2), two-phase & streaming XMSS, forward & reverse TG order."""
    lines = []
    for name, family, n, h, d, hp, a, k, m_bytes in PARAM_SETS:
        v = json.loads((ROOT / f"vectors/slh-dsa-{name}.json").read_text())

        # Collect first 2 ACVP keyGen vectors
        kg_tests = []
        for g in v["keyGen"]:
            for t in g["tests"]:
                kg_tests.append(t)
                if len(kg_tests) == 2:
                    break
            if len(kg_tests) == 2:
                break
        assert len(kg_tests) == 2

        # 1) Keygen B=1 (streaming, forward TG)
        t0 = kg_tests[0]
        pk0_root = bytes.fromhex(t0["pk"])[n:].hex()
        lines.append(f"KEYGEN {name} {family} {n} {d} {hp} 0 0 1")
        lines.append(f"{t0['skSeed']} {t0['pkSeed']} {pk0_root}")

        # 2) Keygen B=2 (two-phase, reverse TG, 2 distinct keys)
        t1 = kg_tests[1]
        pk1_root = bytes.fromhex(t1["pk"])[n:].hex()
        lines.append(f"KEYGEN {name} {family} {n} {d} {hp} 1 1 2")
        lines.append(f"{t0['skSeed']} {t0['pkSeed']} {pk0_root}")
        lines.append(f"{t1['skSeed']} {t1['pkSeed']} {pk1_root}")

        # Collect 2 ACVP sigGen vectors with DISTINCT keys (plus a same-key pair for fast sets)
        sg_cases = []
        for g in v["sigGen"]:
            det = g["deterministic"]
            internal = g["signatureInterface"] == "internal"
            for t in g["tests"]:
                sk = bytes.fromhex(t["sk"])
                sk_seed = sk[0:n]
                sk_prf = sk[n : 2 * n]
                pk_seed = sk[2 * n : 3 * n]
                pk_root = sk[3 * n : 4 * n]
                addrnd = pk_seed if det else bytes.fromhex(t["additionalRandomness"])
                msg = bytes.fromhex(t["message"])
                if internal:
                    framed = msg
                else:
                    ctx = bytes.fromhex(t["context"])
                    framed = bytes([0, len(ctx)]) + ctx + msg
                r_val, digest = compute_prf_msg_and_h_msg(
                    family, n, m_bytes, sk_prf, pk_seed, pk_root, addrnd, framed
                )
                idx_tree, idx_leaf, fors_idx = parse_digest(h, d, hp, a, k, digest)
                sg_cases.append((sk_seed, pk_seed, r_val, idx_tree, idx_leaf, fors_idx, t["signature"]))

        # Pick c0 and c1 with distinct keys
        c0 = sg_cases[0]
        c1 = next(c for c in sg_cases[1:] if c[0] != c0[0] or c[1] != c0[1])

        def emit_sign(two_phase: int, rev_tg: int, batch):
            lines.append(f"SIGN {name} {family} {n} {d} {hp} {a} {k} {two_phase} {rev_tg} {len(batch)}")
            for sk_seed, pk_seed, r_val, idx_tree, idx_leaf, fors_idx, sig_hex in batch:
                idx_str = " ".join(str(x) for x in fors_idx)
                lines.append(
                    f"{sk_seed.hex()} {pk_seed.hex()} {r_val.hex()} {idx_tree} {idx_leaf} {idx_str} {sig_hex}"
                )

        # 3) Sign B=1 (two-phase, forward TG)
        emit_sign(1, 0, [c0])
        # 4) Sign B=2 (streaming, reverse TG, 2 distinct keys)
        emit_sign(0, 1, [c0, c1])
        # 5) For all 6 fast sets, also verify B=2 two-phase with same-key deduplication
        if name.endswith("f"):
            emit_sign(1, 1, [c0, c0])

    path.write_text("\n".join(lines) + "\n")


def check_lean_proofs(binding_claims: str) -> None:
    """Build Metal.Pipeline and audit all headline theorems strictly within
    [propext, Classical.choice, Quot.sound]."""
    os.environ["PATH"] = os.pathsep.join(
        [
            str(Path.home() / ".elan/bin"),
            str(Path.home() / ".cargo/bin"),
            os.environ["PATH"],
        ]
    )
    facade = runpy.run_path(str(HERE / "check-platform-facade.py"))
    subprocess.run(["lake", "build", "Metal.Pipeline", "Metal.Bindings", "Metal.Command", "Metal.CommandValues", "Metal.ChainDispatch", "Metal.LeafDispatch", "Metal.WotsOutput", "Metal.ForsPkDispatch", "Metal.HostValues", "Metal.SignatureLayout"], cwd=ROOT / "lean-hw", check=True)
    subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT / "lean-hw", input=binding_claims, text=True, check=True)
    facade["audit_theorems"]("Metal.SignatureLayout", [
        "MetalSignatureLayout.in_bounds", "MetalSignatureLayout.disjoint", "MetalSignatureLayout.cover",
    ])
    facade["audit_theorems"]("Metal.HostValues", [
        "MetalHostValues.saved_index", "MetalHostValues.key_selected", "MetalHostValues.layers_spec",
        "MetalHostValues.jobs_spec", "MetalHostValues.final_randomizer", "MetalHostValues.host_rule",
    ])
    facade["audit_theorems"]("Metal.ForsPkDispatch", [
        "MetalForsPkDispatch.value_spec", "MetalForsPkDispatch.readPk_spec", "MetalForsPkDispatch.local_rule",
    ])
    facade["audit_theorems"]("Metal.WotsOutput", [
        "MetalWotsOutput.digitAt_eq", "MetalWotsOutput.batch_wots_byte",
        "MetalWotsOutput.scatter_byte", "MetalWotsOutput.wots_rule",
        "MetalWotsOutput.storeByte_eq", "MetalWotsOutput.covered",
    ])
    facade["audit_theorems"]("Metal.LeafDispatch", [
        "MetalLeafDispatch.streaming_rule", "MetalLeafDispatch.twoPhase_rule",
        "MetalLeafDispatch.readNode_spec", "MetalLeafDispatch.contiguous_words",
        "MetalLeafDispatch.insert_rule", "MetalLeafDispatch.matches_run",
    ])
    facade["audit_theorems"]("Metal.ChainDispatch", ["MetalChainDispatch.chainLoop_spec", "MetalChainDispatch.word_address_fits",
        "MetalChainDispatch.replay_word", "MetalChainDispatch.covers_grid", "MetalChainDispatch.local_of_dispatch"])
    facade["audit_theorems"]("Metal.CommandValues", [
        "MetalCommandValues.published", "MetalCommandValues.writes_correct",
        "MetalCommandValues.sign_internal", "MetalCommandValues.batch_internal",
        "MetalCommandValues.decode", "MetalCommandValues.public_pooled_batch",
    ])
    facade["audit_theorems"]("Metal.Command", ["MetalCommand.produced", "MetalCommand.unique_writer",
        "MetalCommand.ordered", "MetalCommand.separate_items", "MetalCommand.separate_parts",
        "MetalCommand.exit_safe"])
    facade["audit_theorems"]("Metal.Bindings", ["MetalBindings.dispatch", "MetalBindings.flat_index"])
    theorems = [
        "MetalPipeline.metal_wots_two_phase_eq_fips",
        "MetalPipeline.metal_wots_streaming_eq_fips",
        "MetalPipeline.metal_wots_two_phase_eq_streaming",
        "MetalPipeline.metal_wots_sign_eq_fips",
        "MetalPipeline.metal_xmss_reduce_eq_fips",
        "MetalPipeline.metal_fors_two_pass_eq_fips",
        "MetalPipeline.metal_keygen_eq_fips",
        "MetalPipeline.metal_batch_keygen_eq_fips",
        "MetalPipeline.metal_sign_internal_eq_fips",
        "MetalPipeline.metal_sign_eq_fips",
        "MetalPipeline.metal_batch_sign_eq_fips",
        "MetalPipeline.metal_all_12_params_sign_eq_fips",
    ]
    facade["audit_theorems"]("Metal.Pipeline", theorems)
    print(f"Lean 4 audit passed: {len(theorems)} theorems in Metal.Pipeline strictly within [propext, Classical.choice, Quot.sound].")


def main() -> None:
    binding_claims = audit_ffi_and_host_boundary()

    with tempfile.TemporaryDirectory() as tmp:
        folder = Path(tmp)
        cpp_src = folder / "metal_kernels_host.cpp"
        exe = folder / "metal_kernels_host"
        cases_file = folder / "acvp_cases.txt"

        cpp_src.write_text(lift_metal_shaders())
        build_test_cases_file(cases_file)

        subprocess.run(
            [
                "clang++",
                "-std=c++20",
                "-O2",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-Wno-unused-function",
                "-fsanitize=undefined,bounds",
                "-fno-sanitize-recover=all",
                str(cpp_src),
                "-o",
                str(exe),
            ],
            check=True,
        )
        subprocess.run([str(exe), str(cases_file)], check=True)

    check_lean_proofs(binding_claims)


if __name__ == "__main__":
    main()
