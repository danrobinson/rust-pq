import Chainwrite.Mask
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Chain
abbrev Rows := Slice (Array U8 64#usize)
abbrev MaskBody := Rows → U16 → Result (ControlFlow (Rows × U16) Rows)

def Covers (mask : U16) (n : Nat) := ∀ j, mask.bv.getLsbD j = true → j < n

theorem walk (body : MaskBody) (applyRow : Nat → Spec.Bytes → Spec.Bytes) (before : Rows) (mask : U16)
    (finish : ∀ b : Rows, body b 0#u16 = ok (done b))
    (advance : ∀ (b : Rows) (m : U16), b.length = before.length → m.bv ≠ 0 →
      (∀ k, m.bv.getLsbD k = true → mask.bv.getLsbD k = true) →
      body b m ⦃ flow => ∃ next rest, flow = cont (next,rest) ∧ next.length = b.length ∧
        rest.bv = m.bv &&& (m.bv-1) ∧
        ∀ k < b.length, bytes next.val[k]!.val =
          if k = m.bv.ctz.toNat then applyRow k (bytes b.val[k]!.val) else bytes b.val[k]!.val ⦄) :
    loop (fun q : Rows × U16 => body q.1 q.2) (before,mask) ⦃ out =>
      out.length = before.length ∧ ∀ k < before.length, bytes out.val[k]!.val =
        if mask.bv.getLsbD k then applyRow k (bytes before.val[k]!.val) else bytes before.val[k]!.val ⦄ := by
  apply loop.spec_decr_nat (measure := fun q : Rows × U16 => q.2.val)
    (inv := fun q => q.1.length = before.length ∧
      (∀ k, q.2.bv.getLsbD k = true → mask.bv.getLsbD k = true) ∧
      ∀ k < before.length, bytes q.1.val[k]!.val =
        if mask.bv.getLsbD k && !q.2.bv.getLsbD k then applyRow k (bytes before.val[k]!.val) else bytes before.val[k]!.val)
  · rintro ⟨b,m⟩ ⟨len,sub,rows⟩
    simp only at len sub rows
    by_cases zero : m.bv = 0
    · have eq : m = 0#u16 := by apply U16.bv_eq_imp_eq; exact zero
      subst m
      rw [finish]
      simp only [step_simps]
      exact ⟨len,by simpa using rows⟩
    · apply WP.spec_mono (advance b m len zero sub)
      rintro flow ⟨next,rest,rfl,ln,hr,changed⟩
      have set := BitVec.getLsbD_true_ctz_of_ne_zero zero
      have original := sub _ set
      have dec : rest.val < m.val := by
        change rest.bv.toNat < m.bv.toNat
        rw [hr,BitVec.toNat_and,BitVec.toNat_sub_of_le (by change (1:Nat) ≤ m.val; by_contra! h; apply zero; apply BitVec.eq_of_toNat_eq; change m.val = 0; omega)]
        have h : m.val &&& (m.val-1) ≤ m.val-1 := Nat.and_le_right
        have nonzero : m.val ≠ 0 := by intro e; apply zero; apply BitVec.eq_of_toNat_eq; exact e
        change m.val &&& (m.val-1) < m.val
        omega
      refine ⟨⟨ln.trans len,fun k hk => ?_,fun k hk => ?_⟩,dec⟩
      · rw [hr,pop_bit m zero] at hk; exact sub k (Bool.and_eq_true_iff.mp hk).1
      · rw [changed k (by omega),rows k hk,hr,pop_bit m zero]
        by_cases eq : k=m.bv.ctz.toNat
        · subst k; simp [set,original]
        · cases m.bv.getLsbD k <;> simp [eq]
  · simp

end slhdsa.X86.Chain
