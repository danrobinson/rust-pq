import Ct.SignFacts

/-!
# Signing leaks only what the signature shows

(The single-set tree's `lean/Ct/Sign.lean`, generalised to the hash length `N` and the parameter set
`p`: the simulators take `N`, `p`, the public key as a byte string of `2N` bytes, the message
(and context) and the signature.)

The simulators (`slhdsa_leak.Sim.*`) take the parameter set, the public key, the message (and
context) and the signature, and no secret. They run the instrumented functions in the order the
signer does, with

* every secret input replaced by zeros (the private key by `skOf pk = 0^(2N) ‖ pk`, the
  randomness by `zeroN N`), and
* every value the signer derives from secrets replaced by what a verifier recomputes from the
  signature: `R` is the first block of the signature, the digest is `H_msg(R, PK.seed, PK.root,
  M)`, the FORS public key is `fors_pk_from_sig` of the FORS part, and the message signed by
  each hypertree layer is the root `xmss_pk_from_sig` recomputes from the layer below.

The signature is cut into its parts at the lengths of the simulator's own outputs (which equal
the signer's: the layer lemmas say so).

Theorems: if a signer returns a signature `sig` with trace `t`, the simulator on
`(p, pk, m, ctx, sig)` returns with the same trace `t`.
-/

open Aeneas Aeneas.Std Ct

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace slhdsa_leak.Sim

open Aeneas.Std.ControlFlow
open slhdsa

/-- Zero bytes, in place of a secret seed. -/
def zeroN (N : Usize) : Std.Array Std.U8 N := Std.Array.repeat N 0#u8

/-- The private key the simulator uses: zero seeds, then the public key (`0^|pk| ‖ pk`). -/
def skOf (pk : Slice Std.U8) : Slice Std.U8 :=
  if h : pk.length + pk.length ≤ Usize.max then
    Slice.from (List.replicate pk.length 0#u8 ++ pk.val) (by simp; omega)
  else pk

/-- `s[off .. off + len]` (clamped): cutting the signature into its parts. -/
def chunk (s : Slice Std.U8) (off len : Nat) : Slice Std.U8 :=
  Slice.from ((s.val.drop off).take len) (by
    have := s.property; simp only [List.length_take, List.length_drop]; omega)

/-- `s[off ..]`. -/
def dropS (s : Slice Std.U8) (off : Nat) : Slice Std.U8 :=
  Slice.from (s.val.drop off) (by have := s.property; simp only [List.length_drop]; omega)

/-- One layer of `ht_sign`, simulated: `node` is the message of this layer (recomputed),
`acc` the simulator's own XMSS signatures so far (for the lengths). -/
def htBody {N : Std.Usize} (p : params.Params) (sigHt : Slice Std.U8) (seed : hash.Seed N)
    (acc : alloc.vec.Vec Std.U8) (node : Std.Array Std.U8 N) (tree : Std.U64) (leaf : Std.U32)
    (j : Std.U32) :
    Result (ControlFlow ((alloc.vec.Vec Std.U8) × (Std.Array Std.U8 N) × Std.U64 ×
      Std.U32 × Std.U32) (alloc.vec.Vec Std.U8)) := do
  if j < p.d
  then
    let a ← address.Adrs.new
    let a1 ← address.Adrs.with_layer a j
    let adrs ← address.Adrs.with_tree a1 tree
    let s ← xmss.xmss_sign p node (zeroN N) leaf seed adrs
    let s1 := chunk sigHt acc.length s.length
    let root1 ← ht.next_message p j leaf s1 node seed adrs
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
def htSign {N : Std.Usize} (p : params.Params) (sigHt : Slice Std.U8) (seed : hash.Seed N)
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
  let _ ← hash.prf_msg sk_prf (zeroN N) m
  let r ← slhdsa.util.block N sig 0#usize
  let digest ← hash.h_msg p r pk_seed pk_root m
  let s := alloc.vec.Vec.deref digest
  let idx_tree ← slh.digest_tree p s
  let s1 := alloc.vec.Vec.deref digest
  let idx_leaf ← slh.digest_leaf p s1
  let a ← address.Adrs.new
  let a1 ← address.Adrs.with_tree a idx_tree
  let a2 ← address.Adrs.with_type a1 address.FORS_TREE
  let adrs ← address.Adrs.with_keypair a2 idx_leaf
  let seed ← hash.seed_ctx pk_seed
  let i ← params.Params.md_bytes p
  let md ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
      digest { start := 0#usize, «end» := i }
  let sig_fors ← fors.fors_sign p md sk_seed seed adrs
  let s2 := chunk sig N.val sig_fors.length
  let pk_fors ← fors.fors_pk_from_sig p s2 md seed adrs
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
    let mp ← slh.with_context m ctx
    let s := alloc.vec.Vec.deref mp
    signInternal N p pk s sig

/-- `api.sign_deterministic`, simulated (`PK.seed` as the randomness: read from the key). -/
def signDeterministic (N : Std.Usize) (p : params.Params) (pk : Slice Std.U8)
    (m ctx sig : Slice Std.U8) : Result Unit := do
  let _ ← util.block N (skOf pk) 2#usize
  sign N p pk m ctx sig

end slhdsa_leak.Sim

namespace Ct.Sign

open slhdsa_leak slhdsa_leak.Sim

/-- Invert one `bind` of a returning run. -/
macro "inv " h:ident " => " x:ident hx:ident : tactic =>
  `(tactic| (rw [Leak.bind_eq_ok] at $h:ident; obtain ⟨$x:ident, _, _, $hx:ident, $h:ident, ht⟩ := $h:ident; subst ht))

theorem ht_sign_loop_post {N : Usize} (p : slhdsa.params.Params) (sk : Std.Array U8 N)
    (seed : slhdsa.hash.Seed N) (sig : alloc.vec.Vec U8) (root : Std.Array U8 N) (tree : U64)
    (leaf j : U32) (b : alloc.vec.Vec U8) (t : Trace)
    (h : (ht.ht_sign_loop p sk seed sig root tree leaf j).run = .ok (b, t)) :
    ∃ rest, b.val = sig.val ++ rest := by
  unfold ht.ht_sign_loop at h
  refine loop_post (P := fun (x : alloc.vec.Vec U8 × Std.Array U8 N × U64 × U32 × U32)
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

theorem hp_le {N : Usize} {p : slhdsa.params.Params} (hp : slhdsa.PN p N) : p.hp.val ≤ 9 :=
  slhdsa.valid_hp_le p hp.valid

/-- The simulated hypertree signer: if `ht_sign_loop` returns `final` with trace `t`, the
simulated loop (on `final` as the hypertree signature, with the same message) returns with the
same trace. -/
theorem ht_sign_loop_sim {N : Usize} (p : slhdsa.params.Params) (hp : slhdsa.PN p N)
    (sk : Std.Array U8 N) (seed : slhdsa.hash.Seed N)
    (hseed : slhdsa.SeedOk seed) (final : alloc.vec.Vec U8) :
    ∀ sig root tree leaf j t,
      (ht.ht_sign_loop p sk seed sig root tree leaf j).run = .ok (final, t) →
      ∀ acc, acc.length = sig.length → leaf.val < 2 ^ p.hp.val →
      ∃ b', (Leak.loop (fun (q : alloc.vec.Vec U8 × Std.Array U8 N × U64 × U32 × U32) =>
          match q with
          | (acc, node, tree, leaf, j) => htBody p final.deref seed acc node tree leaf j)
          (acc, root, tree, leaf, j)).run = .ok (b', t) ∧ b'.length = final.length := by
  intro sig root tree leaf j t h acc hacc hl
  unfold ht.ht_sign_loop at h
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
    obtain ⟨rest, hfinal⟩ := ht_sign_loop_post p sk seed _ _ _ _ _ _ _
      (by unfold ht.ht_sign_loop; exact hrest)
    have hsig1v := (SignFacts.extend_run hsig1).1
    obtain ⟨s', hs', hss', -⟩ := SignFacts.sim_of_spec
      (Ct.Xmss.xmss_sign p root sk (zeroN N) leaf seed seed _) hs
      (slhdsa_leak.xmss.xmss_sign.erase_eq _ _ _ _ _ _)
      (slhdsa.xmss_sign_spec p hp root (zeroN N) leaf seed hseed _ hl)
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


theorem skOf_val {pk : Slice U8} (h : pk.length + pk.length ≤ Usize.max) :
    (skOf pk).val = List.replicate pk.length 0#u8 ++ pk.val := by
  unfold skOf; rw [dif_pos h]; simp

theorem skOf_length {pk : Slice U8} (h : pk.length + pk.length ≤ Usize.max) :
    (skOf pk).length = pk.length + pk.length := by
  simp [Slice.length, skOf_val h]

theorem pk_len {N : Usize} {sk pk : Slice U8} (hsk : sk.length = 4 * N.val)
    (hpk : pk.val = sk.val.drop (2 * N.val)) : pk.length = 2 * N.val := by
  have : pk.length = (sk.val.drop (2 * N.val)).length := by simp [Slice.length, hpk]
  rw [this, List.length_drop]; simp only [Slice.length] at hsk; omega

theorem skOf_len {N : Usize} {sk pk : Slice U8} (hsk : sk.length = 4 * N.val)
    (hpk : pk.val = sk.val.drop (2 * N.val)) : (skOf pk).length = sk.length := by
  have hl := pk_len hsk hpk
  have hm : sk.length ≤ Usize.max := sk.property
  rw [skOf_length (by omega)]; omega

theorem seed_ok {N : Usize} (hN : slhdsa.NOk N) {pk : Std.Array U8 N} {seed : slhdsa.hash.Seed N}
    {t : Trace} (h : (hash.seed_ctx pk).run = .ok (seed, t)) : slhdsa.SeedOk seed :=
  (SignFacts.spec_of_run (slhdsa_leak.hash.seed_ctx.erase_eq pk) (slhdsa.seed_ctx_spec hN pk) h).2

theorem sk_block_sim {N : Usize} (sk pk : Slice U8) (hlen : (skOf pk).length = sk.length)
    (i : Usize) (hi : (i.val + 1) * N.val ≤ sk.length) {r : Std.Array U8 N} {t : Trace}
    (h : (util.block N sk i).run = .ok (r, t)) :
    ∃ r', (util.block N (skOf pk) i).run = .ok (r', t) ∧
      r'.val = ((skOf pk).val.drop (i.val * N.val)).take N.val := by
  obtain ⟨r', t', h', hv⟩ := SignFacts.block_run_ok N (skOf pk) i (by rw [hlen]; exact hi)
  obtain ⟨rfl, -⟩ := (Ct.Wots.block N sk (skOf pk) i hlen.symm) r t r' t' h h'
  exact ⟨r', h', hv⟩

theorem digest_facts {N : Usize} (p : slhdsa.params.Params) (hp : slhdsa.PN p N)
    {r ps pr : Std.Array U8 N} {m : Slice U8} (hm : slhdsa.Room m.length (slhdsa.msgSlack N.val))
    {d : alloc.vec.Vec U8} {t : Trace} (h : (hash.h_msg p r ps pr m).run = .ok (d, t)) :
    d.length = p.m.val :=
  (SignFacts.spec_of_run (slhdsa_leak.hash.h_msg.erase_eq _ _ _ _ _)
    (slhdsa.h_msg_spec p hp.valid hp.n_eq r ps pr m hm) h).2

theorem leaf_lt (p : slhdsa.params.Params) (hv : (slhdsa.paramsS p).Valid) {d : Slice U8}
    {l : U32} {t : Trace} (hd : d.length = p.m.val)
    (h : (slh.digest_leaf p d).run = .ok (l, t)) : l.val < 2 ^ p.hp.val :=
  (SignFacts.spec_of_run (slhdsa_leak.slh.digest_leaf.erase_eq p d)
    (slhdsa.digest_leaf_spec p d hv hd) h).2

theorem md_len (p : slhdsa.params.Params) (hv : (slhdsa.paramsS p).Valid) {i : Usize}
    {t : Trace} (hi : (params.Params.md_bytes p).run = .ok (i, t)) {d : alloc.vec.Vec U8}
    {md : Slice U8} {t' : Trace}
    (h : (slhdsa_leak.alloc.vec.Vec.index (slhdsa_leak.core.slice.index.SliceIndexRangeUsizeSlice U8)
      d { start := 0#usize, «end» := i }).run = .ok (md, t')) :
    md.length = (p.k.val * p.a.val + 7) / 8 := by
  have hiv := (SignFacts.spec_of_run (slhdsa_leak.params.Params.md_bytes.erase_eq p)
    (slhdsa.md_bytes_spec p hv) hi).1
  have := (SignFacts.vec_range_len (Leak.prim_eq_ok.mp h).1).1
  rw [this]; simp [hiv]

/-- **Signing, `slh_sign_internal`.** -/
theorem sign_internal {N : Usize} (p : slhdsa.params.Params) (hp : slhdsa.PN p N)
    (m sk : Slice U8) (hsk : sk.length = 4 * N.val) (addrnd : Std.Array U8 N) (pk : Slice U8)
    (hpk : pk.val = sk.val.drop (2 * N.val)) (hm : slhdsa.Room m.length (slhdsa.msgSlack N.val))
    (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (slh.slh_sign_internal p m sk addrnd).run = .ok (sig, t)) :
    (signInternal N p pk m sig.deref).run = .ok ((), t) := by
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
  have hseed := seed_ok hN h9
  have hmd := md_len p hp.valid hi h10
  have hdl := digest_facts p hp hm h6
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
    (Ct.Hash.prf_msg sk_prf k1 addrnd (zeroN N) m m rfl)
    h5 (slhdsa_leak.hash.prf_msg.erase_eq _ _ _)
    (slhdsa.prf_msg_spec (slhdsa.paramsS p) hp.n hN k1 (zeroN N) m hm)
  -- `R` from the signature
  obtain ⟨rr, hrr, hrrv⟩ := SignFacts.block_ok N sig.deref 0#usize
    (by simp [alloc.vec.Vec.deref, hsigv, Slice.length])
  have err : rr = r := by
    apply Std.Array.ext
    rw [hrrv]; simp [alloc.vec.Vec.deref, hsigv]
  subst err
  -- FORS on zeros
  obtain ⟨sf, hsf, hsfl, -⟩ := SignFacts.sim_of_spec
    (Ct.Fors.fors_sign p md sk_seed k0 seed seed _) h11
    (slhdsa_leak.fors.fors_sign.erase_eq _ _ _ _ _) (slhdsa.fors_sign_spec p hp md k0 seed hseed _ hmd)
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
  obtain ⟨sh, hsh, hshl⟩ := ht_sign_loop_sim p hp sk_seed seed hseed sig_ht _ _ _ _ _ _ h13
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


theorem room_ctx {N : Usize} {m ctx : Slice U8}
    (hm : slhdsa.Room m.length (slhdsa.msgSlack N.val + 257)) (hc : ctx.length ≤ 255)
    {mp : alloc.vec.Vec U8} {t : Trace} (h : (slh.with_context m ctx).run = .ok (mp, t)) :
    slhdsa.Room mp.deref.length (slhdsa.msgSlack N.val) := by
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
theorem slh_sign {N : Usize} (p : slhdsa.params.Params) (hp : slhdsa.PN p N)
    (m ctx sk : Slice U8) (hsk : sk.length = 4 * N.val) (addrnd : Std.Array U8 N) (pk : Slice U8)
    (hpk : pk.val = sk.val.drop (2 * N.val))
    (hm : slhdsa.Room m.length (slhdsa.msgSlack N.val + 257)) (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (slh.slh_sign p m ctx sk addrnd).run = .ok (some sig, t)) :
    (Sim.sign N p pk m ctx sig.deref).run = .ok ((), t) := by
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
  have := sign_internal p hp _ sk hsk addrnd pk hpk (room_ctx hm hc' hmp) _ _ hv
  unfold Sim.sign
  rw [Leak.cond_eq_ok]
  refine ⟨_, rfl, ?_⟩
  rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
  simp only [Leak.run_bind, hmp, this, bind_ok]
  simp

/-- The early exit: a context string longer than 255 bytes. -/
theorem slh_sign_long_ctx {N : Usize} (p : slhdsa.params.Params) (m ctx sk : Slice U8)
    (addrnd : Std.Array U8 N) (hc : 255 < ctx.length) :
    (slh.slh_sign p m ctx sk addrnd).run = .ok (none, [.branch true]) := by
  have hc' : Slice.len ctx > 255#usize := len_gt.mpr hc
  unfold slh.slh_sign
  rw [Leak.cond_eq_ok]
  exact ⟨[], by simp [hc'], by rw [ite_eq_left_of_eq_true _ _ (eq_true hc')]; rfl⟩

theorem api_sign {N : Usize} (p : slhdsa.params.Params) (hp : slhdsa.PN p N)
    (m ctx sk : Slice U8) (hsk : sk.length = 4 * N.val) (addrnd : Std.Array U8 N) (pk : Slice U8)
    (hpk : pk.val = sk.val.drop (2 * N.val))
    (hm : slhdsa.Room m.length (slhdsa.msgSlack N.val + 257)) (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (api.sign p m ctx sk addrnd).run = .ok (some sig, t)) :
    (Sim.sign N p pk m ctx sig.deref).run = .ok ((), t) := by
  unfold api.sign at h
  exact slh_sign p hp m ctx sk hsk addrnd pk hpk hm sig t h

theorem api_sign_deterministic {N : Usize} (p : slhdsa.params.Params) (hp : slhdsa.PN p N)
    (m ctx sk : Slice U8) (hsk : sk.length = 4 * N.val) (pk : Slice U8)
    (hpk : pk.val = sk.val.drop (2 * N.val))
    (hm : slhdsa.Room m.length (slhdsa.msgSlack N.val + 257)) (sig : alloc.vec.Vec U8) (t : Trace)
    (h : (api.sign_deterministic N p m ctx sk).run = .ok (some sig, t)) :
    (Sim.signDeterministic N p pk m ctx sig.deref).run = .ok ((), t) := by
  unfold api.sign_deterministic at h
  inv h => ps hps
  have hN16 := hp.nok.ge16
  obtain ⟨k2, hk2, -⟩ := sk_block_sim (N := N) sk pk (skOf_len hsk hpk) 2#usize
    (by simp [hsk]; try omega) hps
  have := slh_sign p hp m ctx sk hsk ps pk hpk hm sig _ h
  unfold Sim.signDeterministic
  simp only [Leak.run_bind, hk2, this, bind_ok]

/-- The early exit of the two `api` signers: the trace is the simulator's (whatever signature
it is given), which depends on nothing but the context length. -/
theorem api_long_ctx {N : Usize} (p : slhdsa.params.Params) (hp : slhdsa.PN p N)
    (m ctx sk : Slice U8) (hsk : sk.length = 4 * N.val) (addrnd : Std.Array U8 N) (pk : Slice U8)
    (hlen : (skOf pk).length = sk.length) (s : Slice U8) (hc : 255 < ctx.length) :
    (∀ t, (api.sign p m ctx sk addrnd).run = .ok (none, t) ↔ t = [.branch true]) ∧
    (∃ t, (api.sign_deterministic N p m ctx sk).run = .ok (none, t) ∧
      (Sim.signDeterministic N p pk m ctx s).run = .ok ((), t)) := by
  have h1 := slh_sign_long_ctx p m ctx sk addrnd hc
  have hc' : Slice.len ctx > 255#usize := len_gt.mpr hc
  have hN16 := hp.nok.ge16
  obtain ⟨b2, t2, hb2, -⟩ := SignFacts.block_run_ok N sk 2#usize (by simp [hsk]; try omega)
  obtain ⟨k2, hk2, -⟩ := sk_block_sim (N := N) sk pk hlen 2#usize
    (by simp [hsk]; try omega) hb2
  have hs1 : (Sim.sign N p pk m ctx s).run = .ok ((), [.branch true]) := by
    unfold Sim.sign; rw [Leak.cond_eq_ok]
    exact ⟨[], by simp [hc'], by rw [ite_eq_left_of_eq_true _ _ (eq_true hc')]; rfl⟩
  have e1 := slh_sign_long_ctx p m ctx sk b2 hc
  refine ⟨?_, ⟨t2 ++ [.branch true], ?_, ?_⟩⟩
  · intro t; unfold api.sign; rw [h1]; simp [eq_comm]
  · unfold api.sign_deterministic
    simp only [Leak.run_bind, hb2, e1, bind_ok]
  · unfold Sim.signDeterministic
    simp only [Leak.run_bind, hk2, hs1, bind_ok]

end Ct.Sign
