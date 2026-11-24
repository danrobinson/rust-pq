import Integration.SlhDsaShakePermutationClassicalPaths
import Integration.SlhDsaShakePermutationSkFormat

/-! Two-sided extension sparsity for a multi-block SHAKE challenge forest.
A desired output may depend on the complete padded block sequence. Each
new forward edge has at most one relevant digest outside capacity clashes,
independently of the number of challenge digests. -/
namespace Reduction.ShakePermutation.Long
open Classical Classic
noncomputable section
set_option maxRecDepth 8192
variable {Y Z : Type} (out : Words ≃ Y × Z) (goal : List Rate → Option Y)

def bad (t : EdgeTrace Words) := ¬UniquePaths t ∨ ∃ p w, Trail t p w ∧ goal p = some (out w).1

theorem bad_mono {t u : EdgeTrace Words} (sub : ∀ e ∈ t, e ∈ u) (b : bad out goal t) : bad out goal u := by
  rcases b with amb|⟨p,w,trail,reached⟩
  · apply Or.inl; intro uq; apply amb
    intro p q s z h k c
    exact uq (h.weaken sub) (k.weaken sub) c
  · exact Or.inr ⟨p,w,trail.weaken sub,reached⟩

def aim (t : EdgeTrace Words) (x : Words) : Option Y :=
  if reached : ∃ p s, Trail t p s ∧ capOf s = capOf x then
    goal (reached.choose ++ [nextBlock reached.choose_spec.choose x])
  else none

theorem fresh_forward {t : EdgeTrace Words} {x y : Words} (good : ¬ bad out goal t) (iso : isolated t x y)
    (b : bad out goal ((x,y)::t)) : aim goal t x = some (out y).1 := by
  have unique : UniquePaths t := not_not.mp (fun amb => good (Or.inl amb))
  rcases b with lost|⟨p,w,trail,yes⟩
  · exact (lost (unique_forward unique iso)).elim
  rcases forward_paths iso trail with old|⟨rfl,q,z,old,cap,rfl⟩
  · exact (good (Or.inr ⟨p,w,old,yes⟩)).elim
  have seen : ∃ p s, Trail t p s ∧ capOf s = capOf x := ⟨q,z,old,cap⟩
  rw [aim,dite_eq_left seen]
  obtain ⟨hq,hz⟩ := unique seen.choose_spec.choose_spec.1 old
    (seen.choose_spec.choose_spec.2.trans cap.symm)
  exact (congrArg₂ (fun p z => goal (p ++ [nextBlock z x])) hq hz).trans yes

theorem fresh_inverse {t : EdgeTrace Words} {x y : Words} (good : ¬ bad out goal t) (iso : isolated t x y) :
    ¬bad out goal ((y,x)::t) := by
  intro hb
  have uq : UniquePaths t := not_not.mp (fun amb => good (Or.inl amb))
  rcases hb with lost|⟨p,w,path,yes⟩
  · exact lost (unique_inverse uq iso)
  · exact good (Or.inr ⟨p,w,inverse_paths iso path,yes⟩)

/-- A fresh answer adding a successful multi-block witness must create
a capacity clash or match the unique path-derived head for this input. -/
theorem extension {t : EdgeTrace Words} (good : ¬bad out goal t) (back : Bool) (x y : Words)
    (win : bad out goal (edge back x y::t)) :
    ¬isolated t x y ∨ aim goal t x = some (out y).1 := by
  by_cases iso : isolated t x y
  · cases back with
    | false => exact Or.inr (fresh_forward out goal good iso win)
    | true => exact False.elim ((fresh_inverse out goal good iso) win)
  · exact Or.inl iso

private theorem head_count [Fintype Z] (v : Option Y) :
    Fintype.card {y : Words // v = some (out y).1} ≤ Fintype.card Z := by
  apply Fintype.card_le_of_injective (fun y => (out y.val).2)
  intro y z eq
  apply Subtype.ext; apply out.injective
  exact Prod.ext (Option.some.inj (y.property.symm.trans z.property)) eq

private theorem cap_count (t : EdgeTrace Words) (x : Words) :
    Fintype.card {y : Words // ¬isolated t x y} ≤ (2*t.length+2)*Fintype.card Rate := by
  let D := forbidden wordSplit 0 t x
  let tag (y : {y : Words // ¬isolated t x y}) : D := ⟨capOf y.val,not_not.mp y.property⟩
  let f (y : {y : Words // ¬isolated t x y}) := (tag y,rateOf y.val)
  have inj : Function.Injective f := by
    intro y z he
    have hc := congrArg (fun p : D × Rate => p.1.val) he
    have hr := congrArg Prod.snd he
    apply Subtype.ext; apply wordSplit.injective
    exact Prod.ext hr hc
  have h := Fintype.card_le_of_injective f inj
  rw [Fintype.card_prod,Fintype.card_coe] at h
  exact h.trans (Nat.mul_le_mul_right _ (forbidden_card _ _ _ _))

theorem two_sided [Fintype Z] (t : EdgeTrace Words) (good : ¬bad out goal t) (back : Bool) (x : Words) :
    Fintype.card {y : Words // bad out goal (edge back x y::t)} ≤ (2*t.length+2)*Fintype.card Rate + Fintype.card Z := by
  let C := {y : Words // ¬isolated t x y}
  let H := {y : Words // aim goal t x = some (out y).1}
  let f (y : {y : Words // bad out goal (edge back x y::t)}) : C ⊕ H :=
    if h : ¬isolated t x y.val then .inl ⟨y.val,h⟩
    else .inr ⟨y.val,(extension out goal good back x y.val y.property).resolve_left h⟩
  let get : C ⊕ H → Words := Sum.elim Subtype.val Subtype.val
  have spec (y) : get (f y) = y.val := by unfold f; split <;> rfl
  have inj : Function.Injective f := fun y z h => Subtype.ext ((spec y).symm.trans ((congrArg get h).trans (spec z)))
  have h := Fintype.card_le_of_injective f inj
  rw [Fintype.card_sum] at h
  exact h.trans (Nat.add_le_add (cap_count t x) (head_count out (aim goal t x)))

end
end Reduction.ShakePermutation.Long
#print axioms Reduction.ShakePermutation.Long.two_sided
