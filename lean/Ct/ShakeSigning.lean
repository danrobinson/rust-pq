import Ct.ShakeTrees
import Ct.Sign
import Slhdsa.Proofs.ShakeApi

/-! The SHAKE signer’s public trace simulator runs on the public key, message, context
and returned signature. It replays the XMSS and FORS secret computations on zero seeds,
and takes the next public message and indices from the real signature. -/

open Aeneas Aeneas.Std Ct
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace slhdsa_leak.ShakeSim
open Aeneas.Std.ControlFlow slhdsa slhdsa_leak.Sim
/-- One layer of `ht_sign`, simulated: `node` is the message of this layer (recomputed),
`acc` the simulator's own XMSS signatures so far (for the lengths). -/
def htBody {N : Std.Usize} (p : params.Params) (sigHt : Slice Std.U8) (seed : Std.Array U8 N)
    (acc : alloc.vec.Vec Std.U8) (node : Std.Array Std.U8 N) (tree : Std.U64) (leaf : Std.U32)
    (j : Std.U32) :
    Result (ControlFlow ((alloc.vec.Vec Std.U8) × (Std.Array Std.U8 N) × Std.U64 ×
      Std.U32 × Std.U32) (alloc.vec.Vec Std.U8)) := do
  if j < p.d
  then
    let a ← address.Adrs.new
    let a1 ← address.Adrs.with_layer a j
    let adrs ← address.Adrs.with_tree a1 tree
    let s ← shake.xmss.xmss_sign p node (zeroN N) leaf seed adrs
    let s1 := chunk sigHt acc.length s.length
    let root1 ← shake.ht.next_message p j leaf s1 node seed adrs
    let s2 := alloc.vec.Vec.deref s
    let acc1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 acc s2
    let i ← 1#u64 <<< p.hp
    let i1 ← i - 1#u64
    let i2 ← lift (tree &&& i1)
    let leaf1 ← lift (UScalar.cast .U32 i2)
    let tree1 ← tree >>> p.hp
    let j1 ← j + 1#u32
    ok (cont (acc1, root1, tree1, leaf1, j1))
  else ok (done acc)

/-- `ht_sign`, simulated on the hypertree part `sigHt` of the signature. -/
def htSign {N : Std.Usize} (p : params.Params) (sigHt : Slice Std.U8) (seed : Std.Array U8 N)
    (m : Std.Array Std.U8 N) (idx_tree : Std.U64) (idx_leaf : Std.U32) :
    Result (alloc.vec.Vec Std.U8) := do
  loop (fun (acc, node, tree, leaf, j) => htBody p sigHt seed acc node tree leaf j)
    (alloc.vec.Vec.new Std.U8, m, idx_tree, idx_leaf, 0#u32)

/-- `slh_sign_internal`, simulated from the parameter set, the public key, the message and the
signature. -/
def signInternal (N : Std.Usize) (p : params.Params) (pk : Slice Std.U8) (m : Slice Std.U8)
    (sig : Slice Std.U8) : Result Unit := do
  let sk := skOf pk
  let sk_seed ← util.block N sk 0#usize
  let sk_prf ← util.block N sk 1#usize
  let pk_seed ← util.block N sk 2#usize
  let pk_root ← util.block N sk 3#usize
  let _ ← shake.hash.prf_msg sk_prf (zeroN N) m
  let r ← slhdsa.util.block N sig 0#usize
  let digest ← shake.hash.h_msg p r pk_seed pk_root m
  let s := alloc.vec.Vec.deref digest
  let idx_tree ← shake.slh.digest_tree p s
  let s1 := alloc.vec.Vec.deref digest
  let idx_leaf ← shake.slh.digest_leaf p s1
  let a ← address.Adrs.new
  let a1 ← address.Adrs.with_tree a idx_tree
  let a2 ← address.Adrs.with_type a1 address.FORS_TREE
  let adrs ← address.Adrs.with_keypair a2 idx_leaf
  let seed ← shake.hash.seed_ctx pk_seed
  let i ← params.Params.md_bytes p
  let md ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
      digest { start := 0#usize, «end» := i }
  let sig_fors ← shake.fors.fors_sign p md sk_seed seed adrs
  let s2 := chunk sig N.val sig_fors.length
  let pk_fors ← shake.fors.fors_pk_from_sig p s2 md seed adrs
  let sig_ht ← htSign p (dropS sig (N.val + sig_fors.length)) seed pk_fors idx_tree idx_leaf
  let s3 ← lift (Std.Array.to_slice r)
  let sig0 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 (alloc.vec.Vec.new Std.U8) s3
  let s4 := alloc.vec.Vec.deref sig_fors
  let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig0 s4
  let s5 := alloc.vec.Vec.deref sig_ht
  let _ ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig1 s5
  ok ()

/-- `slh_sign` (pure signing with a context string), simulated. -/
def sign (N : Std.Usize) (p : params.Params) (pk : Slice Std.U8) (m ctx sig : Slice Std.U8) :
    Result Unit := do
  let i := Slice.len ctx
  if i > 255#usize
  then ok ()
  else
    let mp ← shake.slh.with_context m ctx
    let s := alloc.vec.Vec.deref mp
    signInternal N p pk s sig

/-- `shake.api.sign_deterministic`, simulated (`PK.seed` as the randomness: read from the key). -/
def signDeterministic (N : Std.Usize) (p : params.Params) (pk : Slice Std.U8)
    (m ctx sig : Slice Std.U8) : Result Unit := do
  let _ ← util.block N (skOf pk) 2#usize
  sign N p pk m ctx sig

end slhdsa_leak.ShakeSim

namespace Ct.ShakeSigning
open slhdsa_leak slhdsa_leak.ShakeSim
open slhdsa_leak.Sim (chunk zeroN skOf dropS)
open Ct.Sign (chunk_eq hp_le skOf_len pk_len skOf_val sk_block_sim len_gt md_len)

theorem ht_sign_loop_post {N : Usize} (p : slhdsa.params.Params) (sk : Std.Array U8 N)
    (seed : Std.Array U8 N) (sig : alloc.vec.Vec U8) (root : Std.Array U8 N) (tree : U64)
    (leaf j : U32) (b : alloc.vec.Vec U8) (t : Trace)
    (h : (shake.ht.ht_sign_loop p sk seed sig root tree leaf j).run = .ok (b, t)) :
    ∃ rest, b.val = sig.val ++ rest := by
  unfold shake.ht.ht_sign_loop at h
  refine loop_post (P := fun (x : alloc.vec.Vec U8 × Std.Array U8 N × U64 × U32 × U32)
    (b : alloc.vec.Vec U8) => ∃ rest, b.val = x.1.val ++ rest) ?_ _ b t h
  rintro ⟨sig, root, tree, leaf, j⟩ c t₁ h
  unfold shake.ht.ht_sign_loop.body at h
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

/-- The simulated hypertree signer: if `ht_sign_loop` returns `final` with trace `t`, the
simulated loop (on `final` as the hypertree signature, with the same message) returns with the
same trace. -/
theorem ht_sign_loop_sim {N : Usize} (p : slhdsa.params.Params) (hp : slhdsa.PN p N)
    (sk : Std.Array U8 N) (seed : Std.Array U8 N)
    (final : alloc.vec.Vec U8) :
    ∀ sig root tree leaf j t,
      (shake.ht.ht_sign_loop p sk seed sig root tree leaf j).run = .ok (final, t) →
      ∀ acc, acc.length = sig.length → leaf.val < 2 ^ p.hp.val →
      ∃ b', (Leak.loop (fun (q : alloc.vec.Vec U8 × Std.Array U8 N × U64 × U32 × U32) =>
          match q with
          | (acc, node, tree, leaf, j) => htBody p final.deref seed acc node tree leaf j)
          (acc, root, tree, leaf, j)).run = .ok (b', t) ∧ b'.length = final.length := by
  intro sig root tree leaf j t h acc hacc hl
  unfold shake.ht.ht_sign_loop at h
  have := loop_sim (body' := fun (q : alloc.vec.Vec U8 × Std.Array U8 N × U64 × U32 × U32) =>
          match q with
          | (acc, node, tree, leaf, j) => htBody p final.deref seed acc node tree leaf j)
    final
    (fun x x' => x.1.length = x'.1.length ∧ x.2 = x'.2 ∧ x.2.2.2.1.val < 2 ^ p.hp.val)
    (fun b b' => b'.length = b.length) ?_ _ t h (acc, root, tree, leaf, j) ⟨hacc.symm, rfl, hl⟩
  · exact this
  rintro ⟨sig, root, tree, leaf, j⟩ ⟨acc, node, tree', leaf', j'⟩ c t₁ ⟨hlen, heq, hl⟩ hb hcont hdone
  simp only [Prod.mk.injEq] at heq hlen hl
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
  simp only at hb ⊢
  unfold shake.ht.ht_sign_loop.body at hb
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
    obtain ⟨rest, hfinal⟩ := ht_sign_loop_post p sk seed _ _ _ _ _ _ _
      (by unfold shake.ht.ht_sign_loop; exact hrest)
    have hsig1v := (SignFacts.extend_run hsig1).1
    obtain ⟨s', hs', hss', -⟩ := SignFacts.sim_of_spec
      (Ct.Shake.xmss_sign p root sk (zeroN N) leaf seed seed _) hs
      (slhdsa_leak.shake.xmss.xmss_sign.erase_eq _ _ _ _ _ _)
      (slhdsa.Shake.xmss_sign_spec p hp root (zeroN N) leaf seed _ hl)
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
      · exact SignFacts.leaf_bound p (hp_le hp) tree i i1 (Leak.prim_eq_ok.mp hi).1
          (Leak.prim_eq_ok.mp hi1).1
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


private theorem digest_facts {N : Usize} (p : slhdsa.params.Params)
    {r ps pr : Std.Array U8 N} {m : Slice U8} {d : alloc.vec.Vec U8} {t : Trace}
    (h : (shake.hash.h_msg p r ps pr m).run = .ok (d,t)) : d.length = p.m.val := by
  have e := SignFacts.spec_of_run (slhdsa_leak.shake.hash.h_msg.erase_eq _ _ _ _ _)
    (slhdsa.Shake.h_msg_spec p r ps pr m) h
  simpa [slhdsa.bytes, alloc.vec.Vec.length] using congrArg List.length e

theorem leaf_lt (p : slhdsa.params.Params) (hv : (slhdsa.paramsS p).Valid) {d : Slice U8}
    {l : U32} {t : Trace} (hd : d.length = p.m.val)
    (h : (shake.slh.digest_leaf p d).run = .ok (l, t)) : l.val < 2 ^ p.hp.val :=
  (SignFacts.spec_of_run (slhdsa_leak.shake.slh.digest_leaf.erase_eq p d)
    (slhdsa.Shake.digest_leaf_spec p d hv hd) h).2

/-- **Signing, `slh_sign_internal`.** -/
theorem sign_internal {N : Usize} (p : slhdsa.params.Params) (hp : slhdsa.PN p N)
    (m sk : Slice U8) (hsk : sk.length = 4 * N.val) (addrnd : Std.Array U8 N) (pk : Slice U8)
    (hpk : pk.val = sk.val.drop (2 * N.val))
    (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (shake.slh.slh_sign_internal p m sk addrnd).run = .ok (sig, t)) :
    (signInternal N p pk m sig.deref).run = .ok ((), t) := by
  unfold shake.slh.slh_sign_internal at h
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
  inv h => i hi
  inv h => md h10
  inv h => sig_fors h11
  inv h => pk_fors h12
  inv h => sig_ht h13
  inv h => sig0 h14
  inv h => sig1 h15
  have hN := hp.nok
  have hN16 := hN.ge16
  have hlen := skOf_len hsk hpk
  have hpl := pk_len hsk hpk
  have hmd := md_len p hp.valid hi h10
  have hdl := digest_facts p h6
  have hleaf := leaf_lt p hp.valid (by simpa using hdl) h8
  -- the signature: `R ‖ SIG_FORS ‖ SIG_HT`
  have e14 := (SignFacts.extend_run h14).1
  have e15 := (SignFacts.extend_run h15).1
  have e16 := (SignFacts.extend_run h).1
  have hsigv : sig.val = r.val ++ sig_fors.val ++ sig_ht.val := by
    rw [e16, e15, e14]; simp [alloc.vec.Vec.deref]
  -- the simulator's key blocks
  have hsl : sk.length + 0 = sk.length := rfl
  obtain ⟨k0, hk0, -⟩ := sk_block_sim (N := N) sk pk hlen 0#usize (by simp [hsk]; try omega) h1
  obtain ⟨k1, hk1, -⟩ := sk_block_sim (N := N) sk pk hlen 1#usize (by simp [hsk]; try omega) h2
  obtain ⟨k2, hk2, hk2v⟩ := sk_block_sim (N := N) sk pk hlen 2#usize (by simp [hsk]; try omega) h3
  obtain ⟨k3, hk3, hk3v⟩ := sk_block_sim (N := N) sk pk hlen 3#usize (by simp [hsk]; try omega) h4
  have hpl2 : pk.length + pk.length ≤ Usize.max := by
    have := sk.property; simp only [Slice.length] at hsk hpl ⊢; omega
  have ek2 : k2 = pk_seed := by
    apply Std.Array.ext
    rw [hk2v, SignFacts.block_run_val h3 (by simp [hsk]; try omega), skOf_val hpl2, hpl]
    rw [show (2#usize : Usize).val * N.val = 2 * N.val by simp]
    rw [List.drop_append_of_le_length (by simp), List.drop_replicate]
    simp only [Nat.sub_self, List.replicate_zero, List.nil_append, hpk]
  have ek3 : k3 = pk_root := by
    apply Std.Array.ext
    rw [hk3v, SignFacts.block_run_val h4 (by simp [hsk]; try omega), skOf_val hpl2, hpl]
    rw [show (3#usize : Usize).val * N.val = 2 * N.val + N.val by simp; ring]
    rw [← List.drop_drop, List.drop_append_of_le_length (by simp), List.drop_replicate]
    simp only [Nat.sub_self, List.replicate_zero, List.nil_append, hpk, List.drop_drop]
  subst ek2 ek3
  -- `PRF_msg` on zeros
  obtain ⟨r', hr', -, -⟩ := SignFacts.sim_of_spec
    (Ct.Shake.prf_msg sk_prf k1 addrnd (zeroN N) m m rfl)
    h5 (slhdsa_leak.shake.hash.prf_msg.erase_eq _ _ _)
    (slhdsa.Shake.prf_msg_spec k1 (zeroN N) m)
  -- `R` from the signature
  obtain ⟨rr, hrr, hrrv⟩ := SignFacts.block_ok N sig.deref 0#usize
    (by simp [alloc.vec.Vec.deref, hsigv, Slice.length])
  have err : rr = r := by
    apply Std.Array.ext
    rw [hrrv]; simp [alloc.vec.Vec.deref, hsigv]
  subst err
  -- FORS on zeros
  obtain ⟨sf, hsf, hsfl, -⟩ := SignFacts.sim_of_spec
    (Ct.Shake.fors_sign p md sk_seed k0 seed seed _) h11
    (slhdsa_leak.shake.fors.fors_sign.erase_eq _ _ _ _ _) (slhdsa.Shake.fors_sign_spec p hp md k0 seed _ hmd)
  have hch : chunk sig.deref N.val sf.length = sig_fors.deref := by
    have : N.val = rr.val.length := by simp
    rw [this, ← hsfl]
    exact chunk_eq _ _ sig_ht.val _ (by simp [alloc.vec.Vec.deref, hsigv]) _
      (by simp [alloc.vec.Vec.deref])
  -- the hypertree
  have hdrop : dropS sig.deref (N.val + sf.length) = sig_ht.deref := by
    apply SignFacts.slice_ext
    simp only [dropS, alloc.vec.Vec.deref, Slice.from_val, hsigv, ← hsfl, alloc.vec.Vec.length]
    rw [show N.val + sig_fors.val.length = (rr.val ++ sig_fors.val).length by simp, List.drop_left]
  obtain ⟨sh, hsh, hshl⟩ := ht_sign_loop_sim p hp sk_seed seed sig_ht _ _ _ _ _ _ h13
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
    hi, h10, hsf, hch, h12, hdrop, hsh, h14, hv1, hv2, bind_ok, Leak.run_pure]
  simp


/-- **Signing, `slh_sign`.** -/
theorem slh_sign {N : Usize} (p : slhdsa.params.Params) (hp : slhdsa.PN p N)
    (m ctx sk : Slice U8) (hsk : sk.length = 4 * N.val) (addrnd : Std.Array U8 N) (pk : Slice U8)
    (hpk : pk.val = sk.val.drop (2 * N.val))
    (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (shake.slh.slh_sign p m ctx sk addrnd).run = .ok (some sig, t)) :
    (ShakeSim.sign N p pk m ctx sig.deref).run = .ok ((), t) := by
  unfold shake.slh.slh_sign at h
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
  have := sign_internal p hp _ sk hsk addrnd pk hpk _ _ hv
  unfold ShakeSim.sign
  rw [Leak.cond_eq_ok]
  refine ⟨_, rfl, ?_⟩
  rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
  simp only [Leak.run_bind, hmp, this, bind_ok]
  simp

/-- The early exit: a context string longer than 255 bytes. -/
theorem slh_sign_long_ctx {N : Usize} (p : slhdsa.params.Params) (m ctx sk : Slice U8)
    (addrnd : Std.Array U8 N) (hc : 255 < ctx.length) :
    (shake.slh.slh_sign p m ctx sk addrnd).run = .ok (none, [.branch true]) := by
  have hc' : Slice.len ctx > 255#usize := len_gt.mpr hc
  unfold shake.slh.slh_sign
  rw [Leak.cond_eq_ok]
  exact ⟨[], by simp [hc'], by rw [ite_eq_left_of_eq_true _ _ (eq_true hc')]; rfl⟩

theorem api_sign {N : Usize} (p : slhdsa.params.Params) (hp : slhdsa.PN p N)
    (m ctx sk : Slice U8) (hsk : sk.length = 4 * N.val) (addrnd : Std.Array U8 N) (pk : Slice U8)
    (hpk : pk.val = sk.val.drop (2 * N.val))
    (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (shake.api.sign p m ctx sk addrnd).run = .ok (some sig, t)) :
    (ShakeSim.sign N p pk m ctx sig.deref).run = .ok ((), t) := by
  unfold shake.api.sign at h
  exact slh_sign p hp m ctx sk hsk addrnd pk hpk sig t h

theorem api_sign_deterministic {N : Usize} (p : slhdsa.params.Params) (hp : slhdsa.PN p N)
    (m ctx sk : Slice U8) (hsk : sk.length = 4 * N.val) (pk : Slice U8)
    (hpk : pk.val = sk.val.drop (2 * N.val))
    (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (shake.api.sign_deterministic N p m ctx sk).run = .ok (some sig, t)) :
    (ShakeSim.signDeterministic N p pk m ctx sig.deref).run = .ok ((), t) := by
  unfold shake.api.sign_deterministic at h
  inv h => ps hps
  have hN16 := hp.nok.ge16
  obtain ⟨k2, hk2, -⟩ := sk_block_sim (N := N) sk pk (skOf_len hsk hpk) 2#usize
    (by simp [hsk]; try omega) hps
  have := slh_sign p hp m ctx sk hsk ps pk hpk sig _ h
  unfold ShakeSim.signDeterministic
  simp only [Leak.run_bind, hk2, this, bind_ok]

/-- The early exit of the two `api` signers: the trace is the simulator's (whatever signature
it is given), which depends on nothing but the context length. -/
theorem api_long_ctx {N : Usize} (p : slhdsa.params.Params) (hp : slhdsa.PN p N)
    (m ctx sk : Slice U8) (hsk : sk.length = 4 * N.val) (addrnd : Std.Array U8 N) (pk : Slice U8)
    (hlen : (skOf pk).length = sk.length) (s : Slice U8) (hc : 255 < ctx.length) :
    (∀ t, (shake.api.sign p m ctx sk addrnd).run = .ok (none, t) ↔ t = [.branch true]) ∧
    (∃ t, (shake.api.sign_deterministic N p m ctx sk).run = .ok (none, t) ∧
      (ShakeSim.signDeterministic N p pk m ctx s).run = .ok ((), t)) := by
  have h1 := slh_sign_long_ctx p m ctx sk addrnd hc
  have hc' : Slice.len ctx > 255#usize := len_gt.mpr hc
  have hN16 := hp.nok.ge16
  obtain ⟨b2, t2, hb2, -⟩ := SignFacts.block_run_ok N sk 2#usize (by simp [hsk]; try omega)
  obtain ⟨k2, hk2, -⟩ := sk_block_sim (N := N) sk pk hlen 2#usize
    (by simp [hsk]; try omega) hb2
  have hs1 : (ShakeSim.sign N p pk m ctx s).run = .ok ((), [.branch true]) := by
    unfold ShakeSim.sign; rw [Leak.cond_eq_ok]
    exact ⟨[], by simp [hc'], by rw [ite_eq_left_of_eq_true _ _ (eq_true hc')]; rfl⟩
  have e1 := slh_sign_long_ctx p m ctx sk b2 hc
  refine ⟨?_, ⟨t2 ++ [.branch true], ?_, ?_⟩⟩
  · intro t; unfold shake.api.sign; rw [h1]; simp [eq_comm]
  · unfold shake.api.sign_deterministic
    simp only [Leak.run_bind, hb2, e1, bind_ok]
  · unfold ShakeSim.signDeterministic
    simp only [Leak.run_bind, hk2, hs1, bind_ok]

end Ct.ShakeSigning
