import Cachepath.NativeVerify.ForsSignScatter
open Aeneas Aeneas.Std Result
namespace slhdsa.NativeVerify.ForsSign
open ShakeBatch
variable [machine : Machine]
abbrev Short := {N : Usize} → Array U8 N → Array address.Adrs machine.width →
  Rows N → Usize → Result (Rows N)

/-- The live secret phase preserves all authentication bytes and fills exactly one
    secret per tree, including a final partial vector. The hash only owes the active lanes. -/
theorem secret_phase (short : Short) {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (choices : Slice U32) (sk seed : Array U8 N) (prf : address.Adrs) (buf : Buffer)
    (k stride : Usize) (count : k.val=choices.length) (trees : choices.length ≤ 35)
    (index : ∀ t < choices.length, choices.val[t]!.val < 2^p.a.val)
    (width : 0 < machine.width.val) (within : N.val ≤ stride.val)
    (fit : choices.length*stride.val ≤ buf.length) (value : Nat → Nat → U8)
    (hash : ∀ (addrs : Array address.Adrs machine.width) (active : Usize),
      0 < active.val → active.val ≤ machine.width.val →
      (∀ j < machine.width.val, addrs.val[j]! = {prf with word3 := addrs.val[j]!.word3}) →
      short seed addrs (Array.repeat machine.width sk) active ⦃ out =>
        ∀ j < active.val, ∀ b < N.val, out.val[j]!.val[b]! = value addrs.val[j]!.word3.val b ⦄) :
    sign_loop0 short choices sk seed k p.a stride buf prf 0#usize ⦃ out =>
      out.length=buf.length ∧ ∀ t q, q < stride.val → t*stride.val+q < buf.length →
        out.val[t*stride.val+q]! = if t < choices.length ∧ q < N.val then
          value (t*2^p.a.val+choices.val[t]!.val) q else buf.val[t*stride.val+q]! ⦄ := by
  unfold sign_loop0
  apply loop.spec_decr_nat (measure := fun v : Buffer × Usize => k.val-v.2.val)
    (inv := fun v => v.2.val ≤ k.val ∧ v.1.length=buf.length ∧
      ∀ t q, q < stride.val → t*stride.val+q < buf.length →
        v.1.val[t*stride.val+q]! = if t < v.2.val ∧ q < N.val then
          value (t*2^p.a.val+choices.val[t]!.val) q else buf.val[t*stride.val+q]!)
  · rintro ⟨cur,first⟩ ⟨le,size,prior⟩
    simp only at le size prior
    unfold sign_loop0.body
    by_cases more : first < k
    · simp only [if_pos more]
      have lt : first.val < k.val := more
      step as ⟨rem,remaining⟩
      simp only [lift,bind_ok]
      let active := core.cmp.impls.OrdUsize.min rem machine.width
      have av : active.val = min (k.val-first.val) machine.width.val := by
        simp [active,core.cmp.impls.OrdUsize.min_val,remaining]
      have pos : 0 < active.val := by omega
      have bound : active.val ≤ machine.width.val := by omega
      have endBound : first.val+active.val ≤ choices.length := by omega
      step with addresses p hp prf choices first active pos endBound trees index as ⟨addrs,addr⟩
      step with hash addrs active pos bound (fun j hj => (addr j hj).1) as ⟨rows,fields⟩
      have room : (first.val+active.val)*stride.val ≤ cur.length :=
        size ▸ (Nat.mul_le_mul_right _ endBound).trans fit
      step with store_secrets rows first stride active cur room bound (by have := hp.nok.ge16; omega)
        (by simpa using within) as ⟨out,wrote⟩
      step as ⟨nxt,advance⟩
      all_goals try scalar_tac
      rw [← show active = core.cmp.impls.OrdUsize.min rem machine.width from rfl] at advance addr fields wrote
      refine ⟨by omega,wrote.1.trans size,?_,by omega⟩
      intro t q hq hidx
      rw [wrote.2 _ _ hq (size.symm ▸ hidx),prior _ _ hq hidx,advance]
      simp only [Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero] 
      by_cases current : first.val ≤ t ∧ t < first.val+active.val ∧ q < N.val
      · have lane : t-first.val < active.val := by omega
        have tr : treeAt first.val active.val (t-first.val) = t := by
          unfold treeAt; rw [min_eq_left (by omega)]; omega
        have ids := (addr (t-first.val) (by omega)).2
        change addrs.val[t-first.val]!.word3.val = _ at ids
        rw [tr] at ids
        rw [if_pos ⟨current.1,current.2.1,current.2.2⟩,if_pos current.2,fields _ lane _ current.2.2,ids]
      · split_ifs <;> first | rfl | omega
    · simp only [if_neg more,step_simps]
      have eq : first.val=choices.length := by have : ¬ first.val < k.val := more; omega
      exact ⟨size,eq ▸ prior⟩
  · simp
end slhdsa.NativeVerify.ForsSign
