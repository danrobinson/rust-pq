import Ct.SignFacts

/-!
# Signing leaks only what the signature shows

The simulators (`slhdsa_leak.Sim.*`) take the public key, the message (and context) and the
signature, and no secret. They run the instrumented functions in the order the signer does,
with

* every secret input replaced by zeros (the private key by `skOf pk = 0³² ‖ pk`, the
  randomness by `zero16`), and
* every value the signer derives from secrets replaced by what a verifier recomputes from the
  signature: `R` is the first block of the signature, the digest is `H_msg(R, PK.seed, PK.root,
  M)`, the FORS public key is `fors_pk_from_sig` of the FORS part, and the message signed by
  each hypertree layer is the root `xmss_pk_from_sig` recomputes from the layer below.

The signature is cut into its parts at the lengths of the simulator's own outputs (which equal
the signer's: the layer lemmas say so).

Theorems: if a signer returns a signature `sig` with trace `t`, the simulator on
`(pk, m, ctx, sig)` returns with the same trace `t`.
-/

open Aeneas Aeneas.Std Ct

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace slhdsa_leak.Sim

open Aeneas.Std.ControlFlow
open slhdsa

/-- Zero bytes, in place of a secret seed. -/
def zero16 : Std.Array Std.U8 16#usize := Std.Array.repeat 16#usize 0#u8

/-- The private key the simulator uses: zero seeds, then the public key. -/
def skOf (pk : Std.Array Std.U8 32#usize) : Std.Array Std.U8 64#usize :=
  Std.Array.make 64#usize (List.replicate 32 0#u8 ++ pk.val) (by simp)

/-- `s[off .. off + len]` (clamped): cutting the signature into its parts. -/
def chunk (s : Slice Std.U8) (off len : Nat) : Slice Std.U8 :=
  Slice.from ((s.val.drop off).take len) (by
    have := s.property; simp only [List.length_take, List.length_drop]; omega)

/-- `s[off ..]`. -/
def dropS (s : Slice Std.U8) (off : Nat) : Slice Std.U8 :=
  Slice.from (s.val.drop off) (by have := s.property; simp only [List.length_drop]; omega)

/-- One layer of `ht_sign`, simulated: `node` is the message of this layer (recomputed),
`acc` the simulator's own XMSS signatures so far (for the lengths). -/
def htBody (sigHt : Slice Std.U8) (seed : hash.Seed) (acc : alloc.vec.Vec Std.U8)
    (node : Std.Array Std.U8 16#usize) (tree : Std.U64) (leaf : Std.U32) (j : Std.U32) :
    Result (ControlFlow ((alloc.vec.Vec Std.U8) × (Std.Array Std.U8 16#usize) × Std.U64 ×
      Std.U32 × Std.U32) (alloc.vec.Vec Std.U8)) := do
  if j < params.D
  then
    let a ← address.Adrs.new
    let a1 ← address.Adrs.with_layer a j
    let adrs ← address.Adrs.with_tree a1 tree
    let s ← xmss.xmss_sign node zero16 leaf seed adrs
    let s1 := chunk sigHt acc.length s.length
    let root1 ← xmss.xmss_pk_from_sig leaf s1 node seed adrs
    let s2 := alloc.vec.Vec.deref s
    let acc1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 acc s2
    let i ← 1#u64 <<< params.HP
    let i1 ← i - 1#u64
    let i2 ← lift (tree &&& i1)
    let leaf1 ← lift (UScalar.cast .U32 i2)
    let tree1 ← tree >>> params.HP
    let j1 ← j + 1#u32
    ok (cont (acc1, root1, tree1, leaf1, j1))
  else ok (done acc)

/-- `ht_sign`, simulated on the hypertree part `sigHt` of the signature. -/
def htSign (sigHt : Slice Std.U8) (seed : hash.Seed) (m : Std.Array Std.U8 16#usize)
    (idx_tree : Std.U64) (idx_leaf : Std.U32) : Result (alloc.vec.Vec Std.U8) := do
  loop (fun (acc, node, tree, leaf, j) => htBody sigHt seed acc node tree leaf j)
    (alloc.vec.Vec.new Std.U8, m, idx_tree, idx_leaf, 0#u32)

/-- One layer of `ht_sign_checked`, simulated. The two roots the signer compares are both the
recomputed root (they are equal in every run that returns a signature); the second route
(`xmss_node`) is run on zeros, for its trace. -/
def htcBody (sigHt : Slice Std.U8) (seed : hash.Seed) (pk_root : Std.Array Std.U8 16#usize)
    (acc : alloc.vec.Vec Std.U8) (node : Std.Array Std.U8 16#usize) (tree : Std.U64)
    (leaf : Std.U32) (j : Std.U32) :
    Result (ControlFlow ((alloc.vec.Vec Std.U8) × (Std.Array Std.U8 16#usize) × Std.U64 ×
      Std.U32 × Std.U32) (alloc.vec.Vec Std.U8)) := do
  if j < params.D
  then
    let a ← address.Adrs.new
    let a1 ← address.Adrs.with_layer a j
    let adrs ← address.Adrs.with_tree a1 tree
    let s ← xmss.xmss_sign node zero16 leaf seed adrs
    let s1 := chunk sigHt acc.length s.length
    let root_a ← xmss.xmss_pk_from_sig leaf s1 node seed adrs
    let i ← j + 1#u32
    let _ ←
      if i < params.D
      then xmss.xmss_node zero16 0#u32 params.HP seed adrs
      else ok pk_root
    let b ←
      core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 root_a root_a
    let _ ← if b
              then ok true
              else ok false
    let s2 := alloc.vec.Vec.deref s
    let acc1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 acc s2
    let i1 ← 1#u64 <<< params.HP
    let i2 ← i1 - 1#u64
    let i3 ← lift (tree &&& i2)
    let leaf1 ← lift (UScalar.cast .U32 i3)
    let tree1 ← tree >>> params.HP
    ok (cont (acc1, root_a, tree1, leaf1, i))
  else ok (done acc)

/-- `ht_sign_checked`, simulated: the message `m` is the recomputed FORS public key. -/
def htcSign (sigHt : Slice Std.U8) (m : Std.Array Std.U8 16#usize) (seed : hash.Seed)
    (idx_tree : Std.U64) (idx_leaf : Std.U32) (pk_root : Std.Array Std.U8 16#usize) :
    Result (alloc.vec.Vec Std.U8) := do
  let b ← core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 m m
  let _ ← if b
            then ok true
            else ok false
  loop (fun (acc, node, tree, leaf, j) => htcBody sigHt seed pk_root acc node tree leaf j)
    (alloc.vec.Vec.new Std.U8, m, idx_tree, idx_leaf, 0#u32)

/-- `slh_sign_internal`, simulated from the public key, the message and the signature. -/
def signInternal (pk : Std.Array Std.U8 32#usize) (m : Slice Std.U8) (sig : Slice Std.U8) :
    Result Unit := do
  let sk := skOf pk
  let s ← lift (Std.Array.to_slice sk)
  let sk_seed ← util.block s 0#usize
  let s1 ← lift (Std.Array.to_slice sk)
  let sk_prf ← util.block s1 1#usize
  let s2 ← lift (Std.Array.to_slice sk)
  let pk_seed ← util.block s2 2#usize
  let s3 ← lift (Std.Array.to_slice sk)
  let pk_root ← util.block s3 3#usize
  let _ ← hash.prf_msg sk_prf zero16 m
  let r ← slhdsa.util.block sig 0#usize
  let digest ← hash.h_msg r pk_seed pk_root m
  let s4 ← lift (Std.Array.to_slice digest)
  let idx_tree ← slh.digest_tree s4
  let s5 ← lift (Std.Array.to_slice digest)
  let idx_leaf ← slh.digest_leaf s5
  let a ← address.Adrs.new
  let a1 ← address.Adrs.with_tree a idx_tree
  let a2 ← address.Adrs.with_type a1 address.FORS_TREE
  let adrs ← address.Adrs.with_keypair a2 idx_leaf
  let seed ← hash.seed_ctx pk_seed
  let s6 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) digest
      { start := 0#usize, «end» := params.MD_BYTES }
  let sig_fors ← fors.fors_sign s6 sk_seed seed adrs
  let s7 := chunk sig 16 sig_fors.length
  let pk_fors ← fors.fors_pk_from_sig s7 s6 seed adrs
  let sig_ht ← htSign (dropS sig (16 + sig_fors.length)) seed pk_fors idx_tree idx_leaf
  let s8 ← lift (Std.Array.to_slice r)
  let sig0 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 (alloc.vec.Vec.new Std.U8) s8
  let s9 := alloc.vec.Vec.deref sig_fors
  let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig0 s9
  let s10 := alloc.vec.Vec.deref sig_ht
  let _ ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig1 s10
  ok ()

/-- `slh_sign_internal_checked`, simulated. The FORS public key computed the second way
(`fors_pk_gen`) is run on zeros for its trace; the final test passed. -/
def signInternalChecked (pk : Std.Array Std.U8 32#usize) (m : Slice Std.U8) (sig : Slice Std.U8) :
    Result Unit := do
  let sk := skOf pk
  let s ← lift (Std.Array.to_slice sk)
  let sk_seed ← util.block s 0#usize
  let s1 ← lift (Std.Array.to_slice sk)
  let sk_prf ← util.block s1 1#usize
  let s2 ← lift (Std.Array.to_slice sk)
  let pk_seed ← util.block s2 2#usize
  let s3 ← lift (Std.Array.to_slice sk)
  let pk_root ← util.block s3 3#usize
  let _ ← hash.prf_msg sk_prf zero16 m
  let r ← slhdsa.util.block sig 0#usize
  let digest ← hash.h_msg r pk_seed pk_root m
  let s4 ← lift (Std.Array.to_slice digest)
  let idx_tree ← slh.digest_tree s4
  let s5 ← lift (Std.Array.to_slice digest)
  let idx_leaf ← slh.digest_leaf s5
  let a ← address.Adrs.new
  let a1 ← address.Adrs.with_tree a idx_tree
  let a2 ← address.Adrs.with_type a1 address.FORS_TREE
  let adrs ← address.Adrs.with_keypair a2 idx_leaf
  let seed ← hash.seed_ctx pk_seed
  let s6 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) digest
      { start := 0#usize, «end» := params.MD_BYTES }
  let sig_fors ← fors.fors_sign s6 sk_seed seed adrs
  let s7 := chunk sig 16 sig_fors.length
  let pk_fors ← fors.fors_pk_from_sig s7 s6 seed adrs
  let _ ← fors.fors_pk_gen sk_seed seed adrs
  let sig_ht ← htcSign (dropS sig (16 + sig_fors.length)) pk_fors seed idx_tree idx_leaf pk_root
  let _ ← Ct.Leak.emit [Ct.Event.branch true]
  let s8 ← lift (Std.Array.to_slice r)
  let sig0 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 (alloc.vec.Vec.new Std.U8) s8
  let s9 := alloc.vec.Vec.deref sig_fors
  let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig0 s9
  let s10 := alloc.vec.Vec.deref sig_ht
  let _ ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig1 s10
  ok ()

/-- `slh_sign` (pure signing with a context string), simulated. -/
def sign (pk : Std.Array Std.U8 32#usize) (m ctx sig : Slice Std.U8) : Result Unit := do
  let i := Slice.len ctx
  if i > 255#usize
  then ok ()
  else
    let mp ← slh.with_context m ctx
    let s := alloc.vec.Vec.deref mp
    signInternal pk s sig

/-- `slh_sign_checked`, simulated. -/
def signChecked (pk : Std.Array Std.U8 32#usize) (m ctx sig : Slice Std.U8) : Result Unit := do
  let i := Slice.len ctx
  if i > 255#usize
  then ok ()
  else
    let mp ← slh.with_context m ctx
    let s := alloc.vec.Vec.deref mp
    signInternalChecked pk s sig

/-- `api.sign_deterministic`, simulated (`PK.seed` as the randomness: read from the key). -/
def signDeterministic (pk : Std.Array Std.U8 32#usize) (m ctx sig : Slice Std.U8) :
    Result Unit := do
  let s ← lift (Std.Array.to_slice (skOf pk))
  let _ ← util.block s 2#usize
  sign pk m ctx sig

/-- `api.sign_deterministic_checked`, simulated. -/
def signDeterministicChecked (pk : Std.Array Std.U8 32#usize) (m ctx sig : Slice Std.U8) :
    Result Unit := do
  let s ← lift (Std.Array.to_slice (skOf pk))
  let _ ← util.block s 2#usize
  signChecked pk m ctx sig

end slhdsa_leak.Sim

namespace Ct.Sign

open slhdsa_leak slhdsa_leak.Sim

/-- Invert one `bind` of a returning run. -/
macro "inv " h:ident " => " x:ident hx:ident : tactic =>
  `(tactic| (rw [Leak.bind_eq_ok] at $h:ident; obtain ⟨$x:ident, _, _, $hx:ident, $h:ident, ht⟩ := $h:ident; subst ht))

theorem ht_sign_loop_post (sk : Std.Array U8 16#usize) (seed : slhdsa.hash.Seed)
    (sig : alloc.vec.Vec U8) (root : Std.Array U8 16#usize) (tree : U64) (leaf j : U32)
    (b : alloc.vec.Vec U8) (t : Trace)
    (h : (ht.ht_sign_loop sk seed sig root tree leaf j).run = .ok (b, t)) :
    ∃ rest, b.val = sig.val ++ rest := by
  unfold ht.ht_sign_loop at h
  refine loop_post (P := fun (x : alloc.vec.Vec U8 × Std.Array U8 16#usize × U64 × U32 × U32)
    (b : alloc.vec.Vec U8) => ∃ rest, b.val = x.1.val ++ rest) ?_ _ b t h
  rintro ⟨sig, root, tree, leaf, j⟩ c t₁ h
  unfold ht.ht_sign_loop.body at h
  rw [Leak.cond_eq_ok] at h
  obtain ⟨t', -, h⟩ := h
  split at h
  · simp only [address.Adrs.new, address.Adrs.with_layer, address.Adrs.with_tree,
      Leak.pure_bind] at h
    inv h => s hs
    inv h => root1 hr
    inv h => sig1 hsig1
    inv h => i hi
    inv h => i1 hi1
    inv h => tree1 htree1
    inv h => j1 hj1
    obtain ⟨rfl, -⟩ := Leak.pure_eq_ok.mp h
    refine ⟨?_, fun b hb => by cases hb⟩
    rintro y b hy ⟨rest, hrest⟩
    simp only [ControlFlow.cont.injEq] at hy
    subst hy
    have := (SignFacts.extend_run hsig1).1
    exact ⟨s.val ++ rest, by rw [hrest]; simp [this, alloc.vec.Vec.deref]⟩
  · obtain ⟨rfl, -⟩ := Leak.pure_eq_ok.mp h
    constructor
    · intro y b hy; cases hy
    · intro b hb
      simp only [ControlFlow.done.injEq] at hb
      subst hb
      exact ⟨[], by simp⟩

theorem chunk_eq (a b c : List U8) (s : Slice U8) (h : s.val = a ++ b ++ c) (x : Slice U8)
    (hx : x.val = b) : chunk s a.length b.length = x := by
  apply SignFacts.slice_ext
  simp [chunk, h, hx]

/-- The simulated hypertree signer: if `ht_sign_loop` returns `final` with trace `t`, the
simulated loop (on `final` as the hypertree signature, with the same message) returns with the
same trace. -/
theorem ht_sign_loop_sim (sk : Std.Array U8 16#usize) (seed : slhdsa.hash.Seed)
    (hseed : slhdsa.SeedOk seed) (final : alloc.vec.Vec U8) :
    ∀ sig root tree leaf j t,
      (ht.ht_sign_loop sk seed sig root tree leaf j).run = .ok (final, t) →
      ∀ acc, acc.length = sig.length → leaf.val < 2 ^ 9 →
      ∃ b', (Leak.loop (fun (p : alloc.vec.Vec U8 × Std.Array U8 16#usize × U64 × U32 × U32) =>
          match p with
          | (acc, node, tree, leaf, j) => htBody final.deref seed acc node tree leaf j)
          (acc, root, tree, leaf, j)).run = .ok (b', t) ∧ b'.length = final.length := by
  intro sig root tree leaf j t h acc hacc hl
  unfold ht.ht_sign_loop at h
  have := loop_sim (body' := fun (p : alloc.vec.Vec U8 × Std.Array U8 16#usize × U64 × U32 × U32) =>
          match p with
          | (acc, node, tree, leaf, j) => htBody final.deref seed acc node tree leaf j)
    final
    (fun x x' => x.1.length = x'.1.length ∧ x.2 = x'.2 ∧ x.2.2.2.1.val < 2 ^ 9)
    (fun b b' => b'.length = b.length) ?_ _ t h (acc, root, tree, leaf, j) ⟨hacc.symm, rfl, hl⟩
  · exact this
  rintro ⟨sig, root, tree, leaf, j⟩ ⟨acc, node, tree', leaf', j'⟩ c t₁ ⟨hlen, heq, hl⟩ hb hcont hdone
  simp only [Prod.mk.injEq] at heq hlen hl
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
  simp only at hb ⊢
  unfold ht.ht_sign_loop.body at hb
  unfold htBody
  rw [Leak.cond_eq_ok] at hb
  obtain ⟨t', rfl, hb⟩ := hb
  split at hb
  · rename_i hj
    simp only [address.Adrs.new, address.Adrs.with_layer, address.Adrs.with_tree,
      Leak.pure_bind] at hb ⊢
    inv hb => s hs
    inv hb => root1 hr
    inv hb => sig1 hsig1
    inv hb => i hi
    inv hb => i1 hi1
    inv hb => tree1 htree1
    inv hb => j1 hj1
    obtain ⟨rfl, rfl⟩ := Leak.pure_eq_ok.mp hb
    obtain ⟨t₂, hrest⟩ := hcont _ rfl
    obtain ⟨rest, hfinal⟩ := ht_sign_loop_post sk seed _ _ _ _ _ _ _ (by unfold ht.ht_sign_loop; exact hrest)
    have hsig1v := (SignFacts.extend_run hsig1).1
    obtain ⟨s', hs', hss', -⟩ := SignFacts.sim_of_spec
      (Ct.Xmss.xmss_sign root sk zero16 leaf seed seed _) hs
      (slhdsa_leak.xmss.xmss_sign.erase_eq _ _ _ _ _)
      (slhdsa.xmss_sign_spec root zero16 leaf seed hseed _ hl)
    have hch : chunk final.deref acc.length s'.length = s.deref := by
      have e1 : acc.length = sig.val.length := hlen.symm
      have e2 : s'.length = s.deref.val.length := by
        rw [← hss']; simp [alloc.vec.Vec.deref]
      rw [e1, e2]
      refine chunk_eq _ _ rest _ ?_ _ rfl
      simp [alloc.vec.Vec.deref, hfinal, hsig1v]
    obtain ⟨acc1, hacc1, hacc1v⟩ := SignFacts.extend_sim hsig1 hlen
      (show s.deref.length = s'.deref.length by simp [alloc.vec.Vec.deref, hss'])
    refine ⟨.cont (acc1, root1, tree1, UScalar.cast UScalarTy.U32 (tree &&& i1), j1), ?_, ?_⟩
    · rw [Leak.cond_eq_ok]
      refine ⟨_, rfl, ?_⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true hj)]
      simp only [Leak.run_bind, hs', hch, hr, hacc1, hi, hi1, htree1, hj1, bind_ok, Leak.run_pure]
    · refine ⟨?_, rfl, ?_⟩
      · simp [alloc.vec.Vec.length, hacc1v, hsig1v, hlen, alloc.vec.Vec.deref, hss']
      · exact SignFacts.leaf_bound tree i i1 (Leak.prim_eq_ok.mp hi).1 (Leak.prim_eq_ok.mp hi1).1
  · rename_i hj
    obtain ⟨rfl, rfl⟩ := Leak.pure_eq_ok.mp hb
    refine ⟨.done acc, ?_, ?_⟩
    · rw [Leak.cond_eq_ok]
      refine ⟨_, rfl, ?_⟩
      rw [ite_eq_right_of_eq_false _ _ (eq_false hj)]
      rfl
    · have := hdone _ rfl
      subst this
      exact hlen.symm

theorem pk_val {sk : Std.Array U8 64#usize} {pk : Std.Array U8 32#usize}
    (h : slhdsa.api.public_key sk = .ok pk) : pk.val = sk.val.drop 32 := by
  obtain ⟨v, hv, hp⟩ := slhdsa.spec_imp_exists (slhdsa.api_public_key_spec sk)
  rw [hv] at h
  simp only [Result.ok.injEq] at h
  subst h
  apply slhdsa.ht_bytes_injective
  rw [hp]
  simp [Spec.skPk, Spec.n, slhdsa.bytes, List.map_drop]

theorem seed_ok {p : Std.Array U8 16#usize} {seed : slhdsa.hash.Seed} {t : Trace}
    (h : (hash.seed_ctx p).run = .ok (seed, t)) : slhdsa.SeedOk seed :=
  (SignFacts.spec_of_run (slhdsa_leak.hash.seed_ctx.erase_eq p) (slhdsa.seed_ctx_spec p) h).2

theorem md_len {d : Std.Array U8 30#usize} {s : Slice U8} {t : Trace}
    (h : (slhdsa_leak.core.array.Array.index (slhdsa_leak.core.ops.index.IndexSlice
      (slhdsa_leak.core.slice.index.SliceIndexRangeUsizeSlice U8)) d
      { start := 0#usize, «end» := params.MD_BYTES }).run = .ok (s, t)) : s.length = 21 := by
  have := Ct.Facts.array_range_index_ok (Leak.prim_eq_ok.mp h).1
  rw [this]; simp [params.MD_BYTES]

theorem leaf_lt {d : Slice U8} {l : U32} {t : Trace} (hd : d.length = 30)
    (h : (slh.digest_leaf d).run = .ok (l, t)) : l.val < 2 ^ 9 :=
  (SignFacts.spec_of_run (slhdsa_leak.slh.digest_leaf.erase_eq d) (slhdsa.digest_leaf_spec d hd) h).2

theorem sk_block_sim (sk : Std.Array U8 64#usize) (pk : Std.Array U8 32#usize) (i : Usize)
    (hi : (i.val + 1) * 16 ≤ 64) {r : Std.Array U8 16#usize} {t : Trace}
    (h : (util.block sk.to_slice i).run = .ok (r, t)) :
    ∃ r', (util.block (skOf pk).to_slice i).run = .ok (r', t) ∧
      r'.val = ((skOf pk).val.drop (i.val * 16)).take 16 := by
  obtain ⟨r', t', h', hv⟩ := SignFacts.block_run_ok (skOf pk).to_slice i (by simpa using hi)
  obtain ⟨rfl, -⟩ := (Ct.Wots.block sk.to_slice (skOf pk).to_slice i (by simp)) r t r' t' h h'
  exact ⟨r', h', by simpa using hv⟩

/-- **Signing, `slh_sign_internal`.** -/
theorem sign_internal (m : Slice U8) (sk : Std.Array U8 64#usize) (addrnd : Std.Array U8 16#usize)
    (pk : Std.Array U8 32#usize) (hpk : slhdsa.api.public_key sk = .ok pk)
    (hm : slhdsa.Room m.length 152) (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (slh.slh_sign_internal m sk addrnd).run = .ok (sig, t)) :
    (signInternal pk m sig.deref).run = .ok ((), t) := by
  unfold slh.slh_sign_internal at h
  simp only [address.Adrs.new, address.Adrs.with_tree, address.Adrs.with_type,
    address.Adrs.with_keypair, Leak.pure_bind] at h
  inv h => sk_seed h1
  inv h => sk_prf h2
  inv h => pk_seed h3
  inv h => pk_root h4
  inv h => r h5
  inv h => digest h6
  inv h => idx_tree h7
  inv h => idx_leaf h8
  inv h => seed h9
  inv h => s6 h10
  inv h => sig_fors h11
  inv h => pk_fors h12
  inv h => sig_ht h13
  inv h => sig0 h14
  inv h => sig1 h15
  have hpkv := pk_val hpk
  have hseed := seed_ok h9
  have hmd := md_len h10
  have hleaf := leaf_lt (by simp) h8
  -- the signature: `R ‖ SIG_FORS ‖ SIG_HT`
  have e14 := (SignFacts.extend_run h14).1
  have e15 := (SignFacts.extend_run h15).1
  have e16 := (SignFacts.extend_run h).1
  have hsigv : sig.val = r.val ++ sig_fors.val ++ sig_ht.val := by
    rw [e16, e15, e14]; simp [alloc.vec.Vec.deref]
  -- the simulator's key blocks
  obtain ⟨k0, hk0, -⟩ := sk_block_sim sk pk 0#usize (by simp) h1
  obtain ⟨k1, hk1, -⟩ := sk_block_sim sk pk 1#usize (by simp) h2
  obtain ⟨k2, hk2, hk2v⟩ := sk_block_sim sk pk 2#usize (by simp) h3
  obtain ⟨k3, hk3, hk3v⟩ := sk_block_sim sk pk 3#usize (by simp) h4
  have ek2 : k2 = pk_seed := by
    apply Std.Array.ext
    rw [hk2v, SignFacts.block_run_val h3 (by simp)]
    simp [skOf, hpkv, List.drop_drop]
  have ek3 : k3 = pk_root := by
    apply Std.Array.ext
    rw [hk3v, SignFacts.block_run_val h4 (by simp)]
    simp [skOf, hpkv, List.drop_drop]
  subst ek2 ek3
  -- `PRF_msg` on zeros
  obtain ⟨r', hr', -, -⟩ := SignFacts.sim_of_spec (Ct.Hash.prf_msg sk_prf k1 addrnd zero16 m m rfl)
    h5 (slhdsa_leak.hash.prf_msg.erase_eq _ _ _) (slhdsa.prf_msg_spec k1 zero16 m hm)
  -- `R` from the signature
  obtain ⟨rr, hrr, hrrv⟩ := SignFacts.block_ok sig.deref 0#usize
    (by simp [alloc.vec.Vec.deref, hsigv])
  have err : rr = r := by
    apply Std.Array.ext
    rw [hrrv]; simp [alloc.vec.Vec.deref, hsigv]
  subst err
  -- FORS on zeros
  obtain ⟨sf, hsf, hsfl, -⟩ := SignFacts.sim_of_spec
    (Ct.Fors.fors_sign s6 sk_seed k0 seed seed _) h11
    (slhdsa_leak.fors.fors_sign.erase_eq _ _ _ _) (slhdsa.fors_sign_spec s6 k0 seed hseed _ hmd)
  have hch : chunk sig.deref 16 sf.length = sig_fors.deref := by
    have : (16 : Nat) = rr.val.length := by simp
    rw [this, ← hsfl]
    exact chunk_eq _ _ sig_ht.val _ (by simp [alloc.vec.Vec.deref, hsigv]) _
      (by simp [alloc.vec.Vec.deref])
  -- the hypertree
  have hdrop : dropS sig.deref (16 + sf.length) = sig_ht.deref := by
    apply SignFacts.slice_ext
    simp only [dropS, alloc.vec.Vec.deref, Slice.from_val, hsigv, ← hsfl, alloc.vec.Vec.length]
    rw [show 16 + sig_fors.val.length = (rr.val ++ sig_fors.val).length by simp, List.drop_left]
  obtain ⟨sh, hsh, hshl⟩ := ht_sign_loop_sim sk_seed seed hseed sig_ht _ _ _ _ _ _ h13
    (alloc.vec.Vec.new U8) rfl hleaf
  -- the final extensions
  obtain ⟨v1, hv1, -⟩ := SignFacts.extend_sim h15 rfl
    (show sig_fors.deref.length = sf.deref.length by simp [alloc.vec.Vec.deref, hsfl])
  obtain ⟨v2, hv2, -⟩ := SignFacts.extend_sim h
    (show sig1.length = v1.length by
      have := (SignFacts.extend_run hv1).1
      simp [alloc.vec.Vec.length, e15, this, alloc.vec.Vec.deref, hsfl])
    (show sig_ht.deref.length = sh.deref.length by simp [alloc.vec.Vec.deref, hshl])
  -- run the simulator
  unfold signInternal htSign
  simp only [address.Adrs.new, address.Adrs.with_tree, address.Adrs.with_type,
    address.Adrs.with_keypair, Leak.pure_bind]
  simp only [Leak.run_bind, hk0, hk1, hk2, hk3, hr', Ct.Facts.liftM_run_ok hrr, h6, h7, h8, h9,
    h10, hsf, hch, h12, hdrop, hsh, h14, hv1, hv2, bind_ok, Leak.run_pure]
  simp

theorem ht_sign_checked_loop_post (sk : Std.Array U8 16#usize) (seed : slhdsa.hash.Seed)
    (pk_root : Std.Array U8 16#usize) (sig : alloc.vec.Vec U8) (ma mb : Std.Array U8 16#usize)
    (ok1 : Bool) (tree : U64) (leaf j : U32) (b : alloc.vec.Vec U8 × Bool) (t : Trace)
    (h : (ht.ht_sign_checked_loop sk seed pk_root sig ma mb ok1 tree leaf j).run = .ok (b, t)) :
    (∃ rest, b.1.val = sig.val ++ rest) ∧ (b.2 = true → ok1 = true) := by
  unfold ht.ht_sign_checked_loop at h
  refine loop_post (P := fun (x : alloc.vec.Vec U8 × Std.Array U8 16#usize ×
      Std.Array U8 16#usize × Bool × U64 × U32 × U32) (b : alloc.vec.Vec U8 × Bool) =>
      (∃ rest, b.1.val = x.1.val ++ rest) ∧ (b.2 = true → x.2.2.2.1 = true)) ?_ _ b t h
  rintro ⟨sig, ma, mb, ok1, tree, leaf, j⟩ c t₁ h
  unfold ht.ht_sign_checked_loop.body at h
  rw [Leak.cond_eq_ok] at h
  obtain ⟨t', -, h⟩ := h
  split at h
  · simp only [address.Adrs.new, address.Adrs.with_layer, address.Adrs.with_tree,
      Leak.pure_bind] at h
    inv h => s hs
    inv h => ra hra
    inv h => i hi
    inv h => rb hrb
    inv h => bb hbb
    inv h => ok2 hok
    inv h => sig1 hsig1
    inv h => i1 hi1
    inv h => i2 hi2
    inv h => tree1 htree1
    obtain ⟨rfl, -⟩ := Leak.pure_eq_ok.mp h
    have hok2 : ok2 = true → ok1 = true := by
      intro h2
      rw [Leak.cond_eq_ok] at hok
      obtain ⟨_, -, hok⟩ := hok
      split at hok
      · exact ((Leak.pure_eq_ok.mp hok).1).trans h2
      · have := (Leak.pure_eq_ok.mp hok).1; subst this; cases h2
    refine ⟨?_, fun b hb => by cases hb⟩
    rintro y b hy ⟨⟨rest, hrest⟩, hb2⟩
    simp only [ControlFlow.cont.injEq] at hy
    subst hy
    have := (SignFacts.extend_run hsig1).1
    exact ⟨⟨s.val ++ rest, by rw [hrest]; simp [this, alloc.vec.Vec.deref]⟩,
      fun h2 => hok2 (hb2 h2)⟩
  · obtain ⟨rfl, -⟩ := Leak.pure_eq_ok.mp h
    constructor
    · intro y b hy; cases hy
    · intro b hb
      simp only [ControlFlow.done.injEq] at hb
      subst hb
      exact ⟨⟨[], by simp⟩, id⟩

theorem cond_bool_true {α : Type} {b : Bool} {x y : α} {r : α} {t : Trace}
    (h : (Leak.cond (b = true) (Leak.pure x) (Leak.pure y)).run = .ok (r, t)) (hr : r ≠ y)
    : b = true ∧ t = [.branch true] := by
  rw [Leak.cond_eq_ok] at h
  obtain ⟨t', rfl, h⟩ := h
  split at h
  · rename_i hb
    obtain ⟨-, rfl⟩ := Leak.pure_eq_ok.mp h
    simp [hb]
  · obtain ⟨rfl, -⟩ := Leak.pure_eq_ok.mp h
    exact absurd rfl hr

theorem cond_true_run {α : Type} (x y : α) :
    (Leak.cond (true = true) (Leak.pure x) (Leak.pure y)).run = .ok (x, [.branch true]) := by
  rw [Leak.cond_eq, Leak.run_bind]; simp

theorem cond_True_run {α : Type} (x y : α) :
    (Leak.cond True (Leak.pure x) (Leak.pure y)).run = .ok (x, [.branch true]) := by
  rw [Leak.cond_eq, Leak.run_bind]; simp

theorem cond_node_sim (sk : Std.Array U8 16#usize) (seed : slhdsa.hash.Seed)
    (hseed : slhdsa.SeedOk seed) (i : U32) (adrs : slhdsa.address.Adrs)
    (pk_root : Std.Array U8 16#usize) {rb : Std.Array U8 16#usize} {T : Trace}
    (h : (Leak.cond (i < params.D) (xmss.xmss_node sk 0#u32 params.HP seed adrs)
      (Leak.pure pk_root)).run = .ok (rb, T)) :
    ∃ rb', (Leak.cond (i < params.D) (xmss.xmss_node zero16 0#u32 params.HP seed adrs)
      (Leak.pure pk_root)).run = .ok (rb', T) := by
  rw [Leak.cond_eq_ok] at h
  obtain ⟨t3, rfl, h⟩ := h
  split at h
  · rename_i hi'
    obtain ⟨rb', hrb', -, -⟩ := SignFacts.sim_of_spec
      (Ct.Xmss.xmss_node sk zero16 0#u32 params.HP seed seed _) h
      (slhdsa_leak.xmss.xmss_node.erase_eq _ _ _ _ _)
      (slhdsa.xmss_node_spec zero16 0#u32 params.HP seed hseed adrs (by simp [params.HP]))
    refine ⟨rb', ?_⟩
    rw [Leak.cond_eq_ok]
    exact ⟨_, rfl, by rw [ite_eq_left_of_eq_true _ _ (eq_true hi')]; exact hrb'⟩
  · rename_i hi'
    refine ⟨rb, ?_⟩
    rw [Leak.cond_eq_ok]
    exact ⟨_, rfl, by rw [ite_eq_right_of_eq_false _ _ (eq_false hi')]; exact h⟩

/-- The simulated checked hypertree signer, one layer at a time (see `ht_sign_loop_sim`). In a
run whose final verdict is `true`, the two roots compared at each layer are equal. -/
theorem ht_sign_checked_loop_sim (sk : Std.Array U8 16#usize) (seed : slhdsa.hash.Seed)
    (hseed : slhdsa.SeedOk seed) (pk_root : Std.Array U8 16#usize) (final : alloc.vec.Vec U8) :
    ∀ sig ma mb ok1 tree leaf j t,
      (ht.ht_sign_checked_loop sk seed pk_root sig ma mb ok1 tree leaf j).run =
        .ok ((final, true), t) →
      ∀ acc, acc.length = sig.length → ma = mb → leaf.val < 2 ^ 9 →
      ∃ b', (Leak.loop (fun (p : alloc.vec.Vec U8 × Std.Array U8 16#usize × U64 × U32 × U32) =>
          match p with
          | (acc, node, tree, leaf, j) => htcBody final.deref seed pk_root acc node tree leaf j)
          (acc, ma, tree, leaf, j)).run = .ok (b', t) ∧ b'.length = final.length := by
  intro sig ma mb ok1 tree leaf j t h acc hacc hab hl
  subst hab
  unfold ht.ht_sign_checked_loop at h
  have := loop_sim (body' := fun (p : alloc.vec.Vec U8 × Std.Array U8 16#usize × U64 × U32 × U32) =>
          match p with
          | (acc, node, tree, leaf, j) => htcBody final.deref seed pk_root acc node tree leaf j)
    (final, true)
    (fun x x' => x.1.length = x'.1.length ∧ x.2.1 = x'.2.1 ∧ x.2.2.1 = x'.2.1 ∧
      x.2.2.2.2 = x'.2.2 ∧ x.2.2.2.2.2.1.val < 2 ^ 9)
    (fun b b' => b'.length = b.1.length) ?_ _ t h (acc, ma, tree, leaf, j)
    ⟨hacc.symm, rfl, rfl, rfl, hl⟩
  · exact this
  rintro ⟨sig, ma, mb, ok1, tree, leaf, j⟩ ⟨acc, node, tree', leaf', j'⟩ c t₁
    ⟨hlen, hma, hmb, heq, hl⟩ hb hcont hdone
  simp only [Prod.mk.injEq] at heq hlen hl hma hmb
  obtain ⟨rfl, rfl, rfl⟩ := heq
  subst hma hmb
  simp only at hb ⊢
  unfold ht.ht_sign_checked_loop.body at hb
  unfold htcBody
  rw [Leak.cond_eq_ok] at hb
  obtain ⟨t', rfl, hb⟩ := hb
  split at hb
  · rename_i hj
    simp only [address.Adrs.new, address.Adrs.with_layer, address.Adrs.with_tree,
      Leak.pure_bind] at hb ⊢
    inv hb => s hs
    inv hb => ra hra
    inv hb => i hi
    inv hb => rb hrb
    inv hb => bb hbb
    inv hb => ok2 hok
    inv hb => sig1 hsig1
    inv hb => i1 hi1
    inv hb => i2 hi2
    inv hb => tree1 htree1
    obtain ⟨rfl, rfl⟩ := Leak.pure_eq_ok.mp hb
    obtain ⟨t₂, hrest⟩ := hcont _ rfl
    obtain ⟨⟨rest, hfinal⟩, hok2⟩ := ht_sign_checked_loop_post sk seed pk_root _ _ _ _ _ _ _ _ _
      (by unfold ht.ht_sign_checked_loop; exact hrest)
    have hok2 := hok2 rfl
    simp only at hfinal hok2
    subst hok2
    -- the comparison succeeded
    obtain ⟨hbt, htok⟩ := cond_bool_true hok (by simp)
    subst hbt
    obtain ⟨hbb', htb⟩ := SignFacts.eq_run hbb
    have hrab : ra = rb := Std.Array.ext _ _ (of_decide_eq_true hbb'.symm)
    subst hrab htb htok
    have hsig1v := (SignFacts.extend_run hsig1).1
    obtain ⟨s', hs', hss', -⟩ := SignFacts.sim_of_spec
      (Ct.Xmss.xmss_sign mb sk zero16 leaf seed seed _) hs
      (slhdsa_leak.xmss.xmss_sign.erase_eq _ _ _ _ _)
      (slhdsa.xmss_sign_spec mb zero16 leaf seed hseed _ hl)
    have hch : chunk final.deref acc.length s'.length = s.deref := by
      have e1 : acc.length = sig.val.length := hlen.symm
      have e2 : s'.length = s.deref.val.length := by
        rw [← hss']; simp [alloc.vec.Vec.deref]
      rw [e1, e2]
      refine chunk_eq _ _ rest _ ?_ _ rfl
      simp [alloc.vec.Vec.deref, hfinal, hsig1v]
    -- the second route, on zeros
    obtain ⟨rb', hrb'⟩ := cond_node_sim sk seed hseed _ _ pk_root hrb
    obtain ⟨acc1, hacc1, hacc1v⟩ := SignFacts.extend_sim hsig1 hlen
      (show s.deref.length = s'.deref.length by simp [alloc.vec.Vec.deref, hss'])
    refine ⟨.cont (acc1, ra, tree1, UScalar.cast UScalarTy.U32 (tree &&& i2), i), ?_, ?_⟩
    · rw [Leak.cond_eq_ok]
      refine ⟨_, rfl, ?_⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true hj)]
      simp only [Leak.run_bind, hs', hch, hra, hi, hrb', SignFacts.eq_self_run, hacc1, hi1, hi2,
        htree1, bind_ok, Leak.run_pure, cond_true_run, cond_True_run]
      simp [SignFacts.commonPrefix_self]
    · refine ⟨?_, rfl, rfl, rfl, ?_⟩
      · simp [alloc.vec.Vec.length, hacc1v, hsig1v, hlen, alloc.vec.Vec.deref, hss']
      · exact SignFacts.leaf_bound tree i1 i2 (Leak.prim_eq_ok.mp hi1).1 (Leak.prim_eq_ok.mp hi2).1
  · rename_i hj
    obtain ⟨rfl, rfl⟩ := Leak.pure_eq_ok.mp hb
    refine ⟨.done acc, ?_, ?_⟩
    · rw [Leak.cond_eq_ok]
      refine ⟨_, rfl, ?_⟩
      rw [ite_eq_right_of_eq_false _ _ (eq_false hj)]
      rfl
    · have := hdone _ rfl
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, -⟩ := this
      exact hlen.symm

theorem ht_sign_checked_sim (sk : Std.Array U8 16#usize) (seed : slhdsa.hash.Seed)
    (hseed : slhdsa.SeedOk seed) (ma mb : Std.Array U8 16#usize) (tree : U64) (leaf : U32)
    (pk_root : Std.Array U8 16#usize) (hl : leaf.val < 2 ^ 9) (final : alloc.vec.Vec U8)
    (t : Trace)
    (h : (ht.ht_sign_checked ma mb sk seed tree leaf pk_root).run = .ok ((final, true), t)) :
    ma = mb ∧ ∃ b', (htcSign final.deref ma seed tree leaf pk_root).run = .ok (b', t) ∧
      b'.length = final.length := by
  unfold ht.ht_sign_checked at h
  inv h => bb hbb
  inv h => ok1 hok
  have hok1 := (ht_sign_checked_loop_post sk seed pk_root _ _ _ _ _ _ _ _ _ h).2 rfl
  try simp only at hok1
  subst hok1
  obtain ⟨hbt, htok⟩ := cond_bool_true hok (by simp)
  subst hbt htok
  obtain ⟨hbb', htb⟩ := SignFacts.eq_run hbb
  have hab : ma = mb := Std.Array.ext _ _ (of_decide_eq_true hbb'.symm)
  subst hab htb
  obtain ⟨b', hb', hbl⟩ := ht_sign_checked_loop_sim sk seed hseed pk_root final _ _ _ _ _ _ _ _ h
    (alloc.vec.Vec.new U8) rfl rfl hl
  refine ⟨rfl, b', ?_, hbl⟩
  unfold htcSign
  simp only [Leak.run_bind, SignFacts.eq_self_run, cond_true_run, cond_True_run, hb', bind_ok]
  simp [SignFacts.commonPrefix_self]

/-- **Signing, `slh_sign_internal_checked`**, when it returns a signature. -/
theorem sign_internal_checked (m : Slice U8) (sk : Std.Array U8 64#usize)
    (addrnd : Std.Array U8 16#usize) (pk : Std.Array U8 32#usize)
    (hpk : slhdsa.api.public_key sk = .ok pk) (hm : slhdsa.Room m.length 152)
    (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (slh.slh_sign_internal_checked m sk addrnd).run = .ok (some sig, t)) :
    (signInternalChecked pk m sig.deref).run = .ok ((), t) := by
  unfold slh.slh_sign_internal_checked at h
  simp only [address.Adrs.new, address.Adrs.with_tree, address.Adrs.with_type,
    address.Adrs.with_keypair, Leak.pure_bind] at h
  inv h => sk_seed h1
  inv h => sk_prf h2
  inv h => pk_seed h3
  inv h => pk_root h4
  inv h => r h5
  inv h => digest h6
  inv h => idx_tree h7
  inv h => idx_leaf h8
  inv h => seed h9
  inv h => s6 h10
  inv h => sig_fors h11
  inv h => pk_fors h12
  inv h => pk_fors_b h12b
  inv h => p h13
  obtain ⟨sig_ht, ok1⟩ := p
  simp only [Aeneas.Std.uncurry_apply_pair] at h
  rw [Leak.cond_eq_ok] at h
  obtain ⟨t', rfl, h⟩ := h
  split at h
  swap
  · have := (Leak.pure_eq_ok.mp h).1; cases this
  rename_i hok1
  subst hok1
  try simp only [Leak.pure_bind] at h
  inv h => sig0 h14
  inv h => sig1 h15
  inv h => sig2 h16
  obtain ⟨hsig, htl⟩ := Leak.pure_eq_ok.mp h
  simp only [Option.some.injEq] at hsig
  subst hsig htl
  have hpkv := pk_val hpk
  have hseed := seed_ok h9
  have hmd := md_len h10
  have hleaf := leaf_lt (by simp) h8
  have e14 := (SignFacts.extend_run h14).1
  have e15 := (SignFacts.extend_run h15).1
  have e16 := (SignFacts.extend_run h16).1
  have hsigv : sig2.val = r.val ++ sig_fors.val ++ sig_ht.val := by
    rw [e16, e15, e14]; simp [alloc.vec.Vec.deref]
  obtain ⟨k0, hk0, -⟩ := sk_block_sim sk pk 0#usize (by simp) h1
  obtain ⟨k1, hk1, -⟩ := sk_block_sim sk pk 1#usize (by simp) h2
  obtain ⟨k2, hk2, hk2v⟩ := sk_block_sim sk pk 2#usize (by simp) h3
  obtain ⟨k3, hk3, hk3v⟩ := sk_block_sim sk pk 3#usize (by simp) h4
  have ek2 : k2 = pk_seed := by
    apply Std.Array.ext
    rw [hk2v, SignFacts.block_run_val h3 (by simp)]
    simp [skOf, hpkv, List.drop_drop]
  have ek3 : k3 = pk_root := by
    apply Std.Array.ext
    rw [hk3v, SignFacts.block_run_val h4 (by simp)]
    simp [skOf, hpkv, List.drop_drop]
  subst ek2 ek3
  obtain ⟨r', hr', -, -⟩ := SignFacts.sim_of_spec (Ct.Hash.prf_msg sk_prf k1 addrnd zero16 m m rfl)
    h5 (slhdsa_leak.hash.prf_msg.erase_eq _ _ _) (slhdsa.prf_msg_spec k1 zero16 m hm)
  obtain ⟨rr, hrr, hrrv⟩ := SignFacts.block_ok sig2.deref 0#usize
    (by simp [alloc.vec.Vec.deref, hsigv])
  have err : rr = r := by
    apply Std.Array.ext
    rw [hrrv]; simp [alloc.vec.Vec.deref, hsigv]
  subst err
  obtain ⟨sf, hsf, hsfl, -⟩ := SignFacts.sim_of_spec
    (Ct.Fors.fors_sign s6 sk_seed k0 seed seed _) h11
    (slhdsa_leak.fors.fors_sign.erase_eq _ _ _ _) (slhdsa.fors_sign_spec s6 k0 seed hseed _ hmd)
  have hch : chunk sig2.deref 16 sf.length = sig_fors.deref := by
    have : (16 : Nat) = rr.val.length := by simp
    rw [this, ← hsfl]
    exact chunk_eq _ _ sig_ht.val _ (by simp [alloc.vec.Vec.deref, hsigv]) _
      (by simp [alloc.vec.Vec.deref])
  obtain ⟨pb, hpb, -, -⟩ := SignFacts.sim_of_spec
    (Ct.Fors.fors_pk_gen sk_seed k0 seed seed _) h12b
    (slhdsa_leak.fors.fors_pk_gen.erase_eq _ _ _) (slhdsa.fors_pk_gen_spec k0 seed hseed _)
  have hdrop : dropS sig2.deref (16 + sf.length) = sig_ht.deref := by
    apply SignFacts.slice_ext
    simp only [dropS, alloc.vec.Vec.deref, Slice.from_val, hsigv, ← hsfl, alloc.vec.Vec.length]
    rw [show 16 + sig_fors.val.length = (rr.val ++ sig_fors.val).length by simp, List.drop_left]
  obtain ⟨-, sh, hsh, hshl⟩ := ht_sign_checked_sim sk_seed seed hseed _ _ _ _ _ hleaf _ _ h13
  obtain ⟨v1, hv1, -⟩ := SignFacts.extend_sim h15 rfl
    (show sig_fors.deref.length = sf.deref.length by simp [alloc.vec.Vec.deref, hsfl])
  obtain ⟨v2, hv2, -⟩ := SignFacts.extend_sim h16
    (show sig1.length = v1.length by
      have := (SignFacts.extend_run hv1).1
      simp [alloc.vec.Vec.length, e15, this, alloc.vec.Vec.deref, hsfl])
    (show sig_ht.deref.length = sh.deref.length by simp [alloc.vec.Vec.deref, hshl])
  unfold signInternalChecked
  simp only [address.Adrs.new, address.Adrs.with_tree, address.Adrs.with_type,
    address.Adrs.with_keypair, Leak.pure_bind]
  simp only [Leak.run_bind, hk0, hk1, hk2, hk3, hr', Ct.Facts.liftM_run_ok hrr, h6, h7, h8, h9,
    h10, hsf, hch, h12, hpb, hdrop, hsh, Leak.run_emit, h14, hv1, hv2, bind_ok, Leak.run_pure]
  simp

theorem room_ctx {m ctx : Slice U8} (hm : slhdsa.Room m.length 409) (hc : ctx.length ≤ 255)
    {mp : alloc.vec.Vec U8} {t : Trace} (h : (slh.with_context m ctx).run = .ok (mp, t)) :
    slhdsa.Room mp.deref.length 152 := by
  have hm' := hm
  simp only [slhdsa.Room] at hm'
  have := (SignFacts.spec_of_run (slhdsa_leak.slh.with_context.erase_eq m ctx)
    (slhdsa.with_context_spec m ctx hc (by omega)) h).2
  simp only [slhdsa.Room, alloc.vec.Vec.deref, Slice.length, Slice.from_val]
  simp only [alloc.vec.Vec.length] at this
  omega

theorem len_gt {ctx : Slice U8} : (Slice.len ctx > 255#usize) ↔ 255 < ctx.length := by
  simp [GT.gt, UScalar.lt_equiv]

/-- **Signing, `slh_sign`.** -/
theorem slh_sign (m ctx : Slice U8) (sk : Std.Array U8 64#usize) (addrnd : Std.Array U8 16#usize)
    (pk : Std.Array U8 32#usize) (hpk : slhdsa.api.public_key sk = .ok pk)
    (hm : slhdsa.Room m.length 409) (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (slh.slh_sign m ctx sk addrnd).run = .ok (some sig, t)) :
    (Sim.sign pk m ctx sig.deref).run = .ok ((), t) := by
  unfold slh.slh_sign at h
  rw [Leak.cond_eq_ok] at h
  obtain ⟨t', rfl, h⟩ := h
  split at h
  · have := (Leak.pure_eq_ok.mp h).1; cases this
  rename_i hc
  inv h => mp hmp
  inv h => v hv
  obtain ⟨hvs, htl⟩ := Leak.pure_eq_ok.mp h
  simp only [Option.some.injEq] at hvs
  subst hvs htl
  have hc' : ctx.length ≤ 255 := by rw [len_gt] at hc; omega
  have := sign_internal _ sk addrnd pk hpk (room_ctx hm hc' hmp) _ _ hv
  unfold Sim.sign
  rw [Leak.cond_eq_ok]
  refine ⟨_, rfl, ?_⟩
  rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
  simp only [Leak.run_bind, hmp, this, bind_ok]
  simp

/-- **Signing, `slh_sign_checked`**, when it returns a signature. -/
theorem slh_sign_checked (m ctx : Slice U8) (sk : Std.Array U8 64#usize)
    (addrnd : Std.Array U8 16#usize) (pk : Std.Array U8 32#usize)
    (hpk : slhdsa.api.public_key sk = .ok pk) (hm : slhdsa.Room m.length 409)
    (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (slh.slh_sign_checked m ctx sk addrnd).run = .ok (some sig, t)) :
    (Sim.signChecked pk m ctx sig.deref).run = .ok ((), t) := by
  unfold slh.slh_sign_checked at h
  rw [Leak.cond_eq_ok] at h
  obtain ⟨t', rfl, h⟩ := h
  split at h
  · have := (Leak.pure_eq_ok.mp h).1; cases this
  rename_i hc
  inv h => mp hmp
  have hc' : ctx.length ≤ 255 := by rw [len_gt] at hc; omega
  have := sign_internal_checked _ sk addrnd pk hpk (room_ctx hm hc' hmp) _ _ h
  unfold Sim.signChecked
  rw [Leak.cond_eq_ok]
  refine ⟨_, rfl, ?_⟩
  rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
  simp only [Leak.run_bind, hmp, this, bind_ok]

/-- The early exit: a context string longer than 255 bytes. -/
theorem slh_sign_long_ctx (m ctx : Slice U8) (sk : Std.Array U8 64#usize)
    (addrnd : Std.Array U8 16#usize) (hc : 255 < ctx.length) :
    (slh.slh_sign m ctx sk addrnd).run = .ok (none, [.branch true]) ∧
    (slh.slh_sign_checked m ctx sk addrnd).run = .ok (none, [.branch true]) := by
  have hc' : Slice.len ctx > 255#usize := len_gt.mpr hc
  constructor
  · unfold slh.slh_sign
    rw [Leak.cond_eq_ok]
    exact ⟨[], by simp [hc'], by rw [ite_eq_left_of_eq_true _ _ (eq_true hc')]; rfl⟩
  · unfold slh.slh_sign_checked
    rw [Leak.cond_eq_ok]
    exact ⟨[], by simp [hc'], by rw [ite_eq_left_of_eq_true _ _ (eq_true hc')]; rfl⟩

theorem api_sign (m ctx : Slice U8) (sk : Std.Array U8 64#usize) (addrnd : Std.Array U8 16#usize)
    (pk : Std.Array U8 32#usize) (hpk : slhdsa.api.public_key sk = .ok pk)
    (hm : slhdsa.Room m.length 409) (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (api.sign m ctx sk addrnd).run = .ok (some sig, t)) :
    (Sim.sign pk m ctx sig.deref).run = .ok ((), t) := by
  unfold api.sign at h
  exact slh_sign m ctx sk addrnd pk hpk hm sig t h

theorem api_sign_checked (m ctx : Slice U8) (sk : Std.Array U8 64#usize)
    (addrnd : Std.Array U8 16#usize) (pk : Std.Array U8 32#usize)
    (hpk : slhdsa.api.public_key sk = .ok pk) (hm : slhdsa.Room m.length 409)
    (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (api.sign_checked m ctx sk addrnd).run = .ok (some sig, t)) :
    (Sim.signChecked pk m ctx sig.deref).run = .ok ((), t) := by
  unfold api.sign_checked at h
  exact slh_sign_checked m ctx sk addrnd pk hpk hm sig t h

theorem api_sign_deterministic (m ctx : Slice U8) (sk : Std.Array U8 64#usize)
    (pk : Std.Array U8 32#usize) (hpk : slhdsa.api.public_key sk = .ok pk)
    (hm : slhdsa.Room m.length 409) (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (api.sign_deterministic m ctx sk).run = .ok (some sig, t)) :
    (Sim.signDeterministic pk m ctx sig.deref).run = .ok ((), t) := by
  unfold api.sign_deterministic at h
  simp only [Leak.pure_bind] at h
  inv h => ps hps
  obtain ⟨k2, hk2, -⟩ := sk_block_sim sk pk 2#usize (by simp) hps
  have := slh_sign m ctx sk ps pk hpk hm sig _ h
  unfold Sim.signDeterministic
  simp only [Leak.pure_bind, Leak.run_bind, hk2, this, bind_ok]

theorem api_sign_deterministic_checked (m ctx : Slice U8) (sk : Std.Array U8 64#usize)
    (pk : Std.Array U8 32#usize) (hpk : slhdsa.api.public_key sk = .ok pk)
    (hm : slhdsa.Room m.length 409) (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (api.sign_deterministic_checked m ctx sk).run = .ok (some sig, t)) :
    (Sim.signDeterministicChecked pk m ctx sig.deref).run = .ok ((), t) := by
  unfold api.sign_deterministic_checked at h
  simp only [Leak.pure_bind] at h
  inv h => ps hps
  obtain ⟨k2, hk2, -⟩ := sk_block_sim sk pk 2#usize (by simp) hps
  have := slh_sign_checked m ctx sk ps pk hpk hm sig _ h
  unfold Sim.signDeterministicChecked
  simp only [Leak.pure_bind, Leak.run_bind, hk2, this, bind_ok]

/-- The early exit of the four `api` signers: the trace is the simulator's (whatever signature
it is given), which depends on nothing but the context length. -/
theorem api_long_ctx (m ctx : Slice U8) (sk : Std.Array U8 64#usize)
    (addrnd : Std.Array U8 16#usize) (pk : Std.Array U8 32#usize) (s : Slice U8)
    (hc : 255 < ctx.length) :
    (∀ t, (api.sign m ctx sk addrnd).run = .ok (none, t) ↔ t = [.branch true]) ∧
    (∀ t, (api.sign_checked m ctx sk addrnd).run = .ok (none, t) ↔ t = [.branch true]) ∧
    (∃ t, (api.sign_deterministic m ctx sk).run = .ok (none, t) ∧
      (Sim.signDeterministic pk m ctx s).run = .ok ((), t)) ∧
    (∃ t, (api.sign_deterministic_checked m ctx sk).run = .ok (none, t) ∧
      (Sim.signDeterministicChecked pk m ctx s).run = .ok ((), t)) := by
  obtain ⟨h1, h2⟩ := slh_sign_long_ctx m ctx sk addrnd hc
  have hc' : Slice.len ctx > 255#usize := len_gt.mpr hc
  obtain ⟨b2, t2, hb2, -⟩ := SignFacts.block_run_ok sk.to_slice 2#usize (by simp)
  obtain ⟨k2, hk2, -⟩ := sk_block_sim sk pk 2#usize (by simp) hb2
  have hs1 : (Sim.sign pk m ctx s).run = .ok ((), [.branch true]) := by
    unfold Sim.sign; rw [Leak.cond_eq_ok]
    exact ⟨[], by simp [hc'], by rw [ite_eq_left_of_eq_true _ _ (eq_true hc')]; rfl⟩
  have hs2 : (Sim.signChecked pk m ctx s).run = .ok ((), [.branch true]) := by
    unfold Sim.signChecked; rw [Leak.cond_eq_ok]
    exact ⟨[], by simp [hc'], by rw [ite_eq_left_of_eq_true _ _ (eq_true hc')]; rfl⟩
  have e1 := (slh_sign_long_ctx m ctx sk b2 hc).1
  have e2 := (slh_sign_long_ctx m ctx sk b2 hc).2
  refine ⟨?_, ?_, ⟨t2 ++ [.branch true], ?_, ?_⟩, ⟨t2 ++ [.branch true], ?_, ?_⟩⟩
  · intro t; unfold api.sign; rw [h1]; simp [eq_comm]
  · intro t; unfold api.sign_checked; rw [h2]; simp [eq_comm]
  · unfold api.sign_deterministic
    simp only [Leak.pure_bind, Leak.run_bind, hb2, e1, bind_ok]
  · unfold Sim.signDeterministic
    simp only [Leak.pure_bind, Leak.run_bind, hk2, hs1, bind_ok]
  · unfold api.sign_deterministic_checked
    simp only [Leak.pure_bind, Leak.run_bind, hb2, e2, bind_ok]
  · unfold Sim.signDeterministicChecked
    simp only [Leak.pure_bind, Leak.run_bind, hk2, hs2, bind_ok]

end Ct.Sign
