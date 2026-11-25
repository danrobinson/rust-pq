import Armwide.XmssNode
import Armwide.Dispatch
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Armwide.XmssLeaves.Signer
open Keygen Public.Dispatcher
noncomputable section
section
variable [Cpu] [Features]

abbrev xmss.xmss_node {N : Usize} := @Node.xmss.xmss_node _ _ N
abbrev wots.wots_sign [cpu : Cpu] {N : Usize} := @Public.Dispatcher.wots.wots_sign cpu N

@[rust_loop_body]
def xmss.xmss_sign_loop.body
  {N : Std.Usize} (p : params.Params) (sk_seed : Array Std.U8 N)
  (idx : Std.U32) (seed : hash.Seed N) (adrs : address.Adrs)
  (sig : alloc.vec.Vec Std.U8) (j : Std.U32) :
  Result (ControlFlow ((alloc.vec.Vec Std.U8) × Std.U32) (alloc.vec.Vec
    Std.U8))
  := do
  if j < p.hp
  then
    let i ← idx >>> j
    let k ← lift (i ^^^ 1#u32)
    let node ← xmss.xmss_node sk_seed k j seed adrs
    let s ← lift (Array.to_slice node)
    let sig1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sig s
    let j1 ← j + 1#u32
    ok (cont (sig1, j1))
  else ok (done sig)

@[rust_loop]
def xmss.xmss_sign_loop
  {N : Std.Usize} (p : params.Params) (sk_seed : Array Std.U8 N)
  (idx : Std.U32) (seed : hash.Seed N) (adrs : address.Adrs)
  (sig : alloc.vec.Vec Std.U8) (j : Std.U32) :
  Result (alloc.vec.Vec Std.U8)
  := do
  loop
    (fun (sig1, j1) => xmss.xmss_sign_loop.body p sk_seed idx seed adrs sig1
      j1)
    (sig, j)

def xmss.xmss_sign
  {N : Std.Usize} (p : params.Params) (m : Array Std.U8 N)
  (sk_seed : Array Std.U8 N) (idx : Std.U32) (seed : hash.Seed N)
  (adrs : address.Adrs) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let a ← address.Adrs.with_type adrs address.WOTS_HASH
  let a1 ← address.Adrs.with_keypair a idx
  let sig ← wots.wots_sign m sk_seed seed a1
  xmss.xmss_sign_loop p sk_seed idx seed adrs sig 0#u32

end

private theorem treeNode [Cpu] [Features] {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N) (i z : U32)
    (s : hash.Seed N) (hs : SeedOk s) (a : address.Adrs) (within : (i.val+1)*2^z.val≤2^p.hp.val) :
    xmss.xmss_node sk i z s a ⦃ out => slhdsa.bytes out.val=Spec.xmssNode (paramsS p) (slhdsa.bytes sk.val)
      i.val z.val (slhdsa.bytes s.pk_seed.val) (slhdsa.adrsS a) ⦄ := by
  have cap : 2^p.hp.val≤512 := Nat.pow_le_pow_right (by decide) hp.valid.hp_le
  exact Node.node_fips p hp sk s hs a _ i z rfl (by omega)

private theorem xmss_sign_loop_spec [Cpu] [Features] {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (idx : U32) (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (sig : alloc.vec.Vec U8)
    (j : U32) (wsig : Spec.Bytes)
    (hidx : idx.val < 2 ^ p.hp.val) (hj : j.val ≤ p.hp.val)
    (hlen : sig.length = N.val * (2 * N.val + 3) + N.val * j.val)
    (hinv : slhdsa.bytes sig.val = wsig ++ (List.range j.val).flatMap fun j =>
      Spec.xmssNode (paramsS p) (slhdsa.bytes sk.val) ((idx.val / 2 ^ j) ^^^ 1) j (slhdsa.bytes seed.pk_seed.val)
        (slhdsa.adrsS a)) :
    xmss.xmss_sign_loop p sk idx seed a sig j ⦃ r =>
      slhdsa.bytes r.val = wsig ++ (List.range p.hp.val).flatMap (fun j =>
        Spec.xmssNode (paramsS p) (slhdsa.bytes sk.val) ((idx.val / 2 ^ j) ^^^ 1) j (slhdsa.bytes seed.pk_seed.val)
          (slhdsa.adrsS a)) ∧
      r.length = (2 * N.val + 3 + p.hp.val) * N.val ⦄ := by
  have hn32 := hp.le32
  have hhp := valid_hp_le p hp.valid
  unfold xmss.xmss_sign_loop
  apply loop.spec_decr_nat (measure := fun (q : alloc.vec.Vec U8 × U32) => p.hp.val - q.2.val)
    (inv := fun q => q.2.val ≤ p.hp.val ∧
      q.1.length = N.val * (2 * N.val + 3) + N.val * q.2.val ∧
      slhdsa.bytes q.1.val = wsig ++ (List.range q.2.val).flatMap fun j =>
        Spec.xmssNode (paramsS p) (slhdsa.bytes sk.val) ((idx.val / 2 ^ j) ^^^ 1) j
          (slhdsa.bytes seed.pk_seed.val) (slhdsa.adrsS a))
  · clear hj hlen hinv sig j
    rintro ⟨sig, j⟩ ⟨hj, hlen, hinv⟩
    simp only [xmss.xmss_sign_loop.body]
    simp only at hj hlen hinv
    simp only [step_simps]
    spec_split
    · rename_i hlt
      have hjlt : j.val < p.hp.val := by scalar_tac
      let* ⟨ i, i_post, i_post1 ⟩ ← U32.ShiftRight_spec
      let* ⟨ k, k_post, k_post1 ⟩ ← UScalar.xor_spec
      have hk : k.val = (idx.val / 2 ^ j.val) ^^^ 1 := by
        rw [k_post]; simp [i_post, Nat.shiftRight_eq_div_pow]
      have splitHeight : 2 ^ p.hp.val = 2 ^ (p.hp.val - j.val) * 2 ^ j.val := by
        rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
      have siblings := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos j.val)).2 (splitHeight ▸ hidx)
      have flipBit : 1 < 2 ^ (p.hp.val - j.val) :=
        lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide) (by omega))
      have siblingBound : k.val < 2 ^ (p.hp.val - j.val) := hk ▸ Nat.xor_lt_two_pow siblings flipBit
      let* ⟨ node, node_post ⟩ ← treeNode p hp
      · rw [splitHeight]
        exact Nat.mul_le_mul_right _ (by omega)
      have hb1 : N.val * (2 * N.val + 3) ≤ 32 * 67 :=
        Nat.mul_le_mul hn32 (by omega)
      have hb2 : N.val * j.val ≤ 32 * 9 := Nat.mul_le_mul hn32 (by omega)
      let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
      let* ⟨ sig1, sig1_post, sig1_len ⟩ ← xmss_extend_u8_spec
      let* ⟨ j1, j1_post ⟩ ← U32.add_spec
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [sig1_len, hlen, s_post, j1_post]; simp; ring
      · simp [sig1_post, s_post, hinv, j1_post, List.range_succ, node_post, hk]
    · rename_i hge
      have hjeq : j.val = p.hp.val := by scalar_tac
      simp only [step_simps]
      refine ⟨?_, ?_⟩
      · rw [hinv, hjeq]
      · rw [hlen, hjeq]; ring
  · exact ⟨hj, hlen, hinv⟩

@[step]
theorem xmss_sign_spec [Cpu] [Features] {N : Usize} (p : params.Params) (hp : PN p N) (m sk : Array U8 N) (idx : U32)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (h : idx.val < 2 ^ p.hp.val) :
    xmss.xmss_sign p m sk idx seed a ⦃ r =>
      slhdsa.bytes r.val = Spec.xmssSign (paramsS p) (slhdsa.bytes m.val) (slhdsa.bytes sk.val) idx.val
        (slhdsa.bytes seed.pk_seed.val) (slhdsa.adrsS a) ∧
      r.length = (2 * N.val + 3 + p.hp.val) * N.val ⦄ := by
  unfold xmss.xmss_sign
  let* ⟨ a1, a1_post, a1_post1 ⟩ ← slhdsa.with_type_spec
  let* ⟨ a2, a2_post ⟩ ← slhdsa.with_keypair_spec
  have reachable : Public.hashAddress (slhdsa.adrsS a2)=slhdsa.adrsS a2 := by
    rw [a2_post,a1_post1]
    with_unfolding_all rfl
  rw [show wots.wots_sign m sk seed a2 = slhdsa.wots.wots_sign m sk seed a2 from wots_dispatch_eq p hp m sk seed hs a2 reachable]
  let* ⟨ sig, sig_post, sig_len ⟩ ← wots_sign_spec p hp
  apply WP.spec_mono
  · exact xmss_sign_loop_spec p hp sk idx seed hs a sig 0#u32 (slhdsa.bytes sig.val) h
      (by scalar_tac) (by simp [sig_len]) (by simp)
  · rintro r ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h1, sig_post]
    simp [Spec.xmssSign, a2_post, a1_post1, slhdsa.adrsS, Spec.Adrs.setTypeAndClear,
      Spec.WOTS_HASH, address.WOTS_HASH]

theorem sign_eq_scalar [Cpu] [Features] {N} (p : params.Params) (hp : PN p N) (m sk : Array U8 N)
    (idx : U32) (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (index : idx.val<2^p.hp.val) :
    xmss.xmss_sign p m sk idx seed a = slhdsa.xmss.xmss_sign p m sk idx seed a := by
  obtain ⟨x,hx,xs,_⟩ := spec_imp_exists (xmss_sign_spec p hp m sk idx seed hs a index)
  obtain ⟨y,hy,ys,_⟩ := spec_imp_exists (slhdsa.xmss_sign_spec p hp m sk idx seed hs a index)
  rw [hx,hy,ok.injEq]
  exact alloc.vec.Vec.ext _ _ ((bytes_inj _ _).mp (xs.trans ys.symm))

end
end slhdsa.Armwide.XmssLeaves.Signer
