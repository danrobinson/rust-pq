import Integration.SlhDsaShakePermutationClassicalReport

namespace Reduction.ShakePermutation.Classic
open Classical OracleComp OracleSpec
noncomputable section

def demand (T : ℕ) (H : Row T → Words) : Row T → Port
  | .inr x => x
  | .inl a =>
    let p := List.ofFn a.2
    let z := bankState T H p.dropLast
    (false,join (rateXor (p.getLastD 0) (rateOf z)) (capOf z))

def wire (T : ℕ) (H : Row T → Words) (j : Row T) : Words × Words :=
  edge (demand T H j).1 (demand T H j).2 (H j)

theorem snoc_demand (T : ℕ) (H : Row T → Words) (p : List Rate) (r : Rate) (h : (p++[r]).length ≤ T) :
    demand T H (rowId T (p++[r])) = (false,join (rateXor r (rateOf (bankState T H p))) (capOf (bankState T H p))) := by
  simp only [rowId,dite_eq_left h,demand,BList.ofFn_ofList]
  simp

theorem snoc_state (T : ℕ) (H : Row T → Words) (p : List Rate) (r : Rate) :
    bankState T H (p++[r]) = H (rowId T (p++[r])) := by simp [bankState]

structure Wires (T : ℕ) (H : Row T → Words) (t : EdgeTrace Words) (seen : Finset (Row T)) : Prop extends History T t seen where
  state_ok : ∀ ⦃p s⦄, Trail t p s → bankState T H p = s
  recorded : ∀ j ∈ seen, wire T H j ∈ t
  distinct : ∀ j ∈ seen, ∀ l ∈ seen, wire T H j = wire T H l → j = l
  outside : ∀ u : Port, Sum.inr u ∈ seen → ∀ ⦃p s⦄, Trail t p s → capOf (wire T H (.inr u)).1 ≠ capOf s

theorem emptyWires (T : ℕ) (H : Row T → Words) : Wires T H [] ∅ where
  toHistory := emptyHistory T
  state_ok := by intro p s h; cases h with | root => rfl | step _ e _ => simp at e
  recorded := by simp
  distinct := by simp
  outside := by simp

theorem row_demand {T : ℕ} {H : Row T → Words} {t seen} (h : Wires T H t seen) (short : t.length < T)
    (d : Bool) (x : Words) : demand T H (publicRow T t d x) = (d,x) := by
  cases d with
  | true => rfl
  | false =>
    simp only [publicRow,Bool.false_eq_true,ite_false]
    split
    · rename_i ht
      let p := ht.choose
      let s := ht.choose_spec.choose
      have hz : Trail t p s := ht.choose_spec.choose_spec.1
      have len : (p++[nextBlock s x]).length ≤ T := by have := h.short hz; simp; omega
      rw [snoc_demand _ _ _ _ len,h.state_ok hz]
      rw [nextBlock,rateXor_cancel,ht.choose_spec.choose_spec.2,join_split]
    · rfl

theorem wire_step {T : ℕ} {H : Row T → Words} {t seen} (w : Wires T H t seen) (short : t.length < T)
    (d : Bool) (x : Words) (fresh : ¬old t d x) (iso : isolated t x (H (publicRow T t d x))) :
    Wires T H (edge d x (H (publicRow T t d x))::t) (insert (publicRow T t d x) seen) := by
  let j := publicRow T t d x
  let y := H j
  let e := edge d x y
  have aligned : wire T H j = e := by simp only [wire,j,row_demand w short,e,y]
  have newEdge : e ∉ t := by
    intro he
    apply fresh
    cases d with
    | false => exact ⟨_,he⟩
    | true => exact ⟨_,List.mem_map.mpr ⟨e,he,rfl⟩⟩
  constructor
  · exact history_step w.toHistory d x y fresh iso
  · intro p s ht
    cases d with
    | true => exact w.state_ok (inverse_paths iso ht)
    | false =>
      rcases forward_paths iso ht with oldp|⟨rfl,q,z,prev,hc,rfl⟩
      · exact w.state_ok oldp
      · have hit : rootAt t (capOf x) := ⟨q,z,prev,hc⟩
        have both := w.unique prev hit.choose_spec.choose_spec.1 (hc.trans hit.choose_spec.choose_spec.2.symm)
        rw [snoc_state]
        simp only [publicRow,Bool.false_eq_true,ite_false,dite_eq_left hit,both.1,both.2]
  · intro u hu
    rcases Finset.mem_insert.mp hu with rfl|oldmem
    · exact aligned ▸ List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (w.recorded _ oldmem)
  · intro u hu v hv eq
    rcases Finset.mem_insert.mp hu with rfl|hu
    · rcases Finset.mem_insert.mp hv with rfl|hv
      · rfl
      · exact False.elim (newEdge (aligned ▸ eq.symm ▸ w.recorded _ hv))
    · rcases Finset.mem_insert.mp hv with rfl|hv
      · exact False.elim (newEdge (aligned ▸ eq ▸ w.recorded _ hu))
      · exact w.distinct _ hu _ hv eq
  · intro u mem p s ht
    rcases Finset.mem_insert.mp mem with added|oldmem
    · have eq : wire T H (.inr u) = e := (congrArg (wire T H) added).trans aligned
      rw [eq]
      cases d with
      | true => exact (inverse_paths iso ht).separate iso
      | false =>
        have miss : ¬rootAt t (capOf x) := by
          intro root
          simp only [publicRow,Bool.false_eq_true,ite_false,dite_eq_left root,rowId] at added
          contradiction
        rcases forward_paths iso ht with oldp|⟨_,q,z,prev,hc,_⟩
        · exact fun hc => miss ⟨_,_,oldp,hc.symm⟩
        · exact False.elim (miss ⟨q,z,prev,hc⟩)
    · cases d with
      | true => exact w.outside u oldmem (inverse_paths iso ht)
      | false =>
        rcases forward_paths iso ht with oldp|⟨rfl,_⟩
        · exact w.outside u oldmem oldp
        · exact (((isolate_parts iso).2.2 _ _ (w.recorded _ oldmem)).1).symm

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.wire_step
