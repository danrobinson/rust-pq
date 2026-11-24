import Integration.SlhDsaCompressionLongGrowth
import Integration.SlhDsaCompressionLeftPrefix
namespace Reduction.Compression.LongClass
open MLink Ideal Ideal.MP2 Recording.Database Recording.Compile Recording.Compile.LeftPort TweakableHash OracleComp OracleSpec ENNReal Classical
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 8192
set_option linter.unusedSectionVars false

def tag {S B : Type} [DecidableEq S] (cv : S) (x : S × B) : Cell S B := if x.1 = cv then .inr x.2 else .inl x
def physical {S B : Type} (cv : S) : Cell S B → S × B
  | .inl x => x
  | .inr b => (cv,b)

def fallback {S B : Type} [DecidableEq S] (cv : S) (raw : S × B → Option S) : Partial S B
  | .inl x => if x.1 = cv then none else raw x
  | .inr b => raw (cv,b)

section Abstract
variable {S B J Y : Type} [DecidableEq S] [DecidableEq B] [DecidableEq J]
variable [Fintype S] [Fintype B] [Fintype J] [Fintype Y] [Nonempty S] [Nonempty Y]
local notation "X" => (S × B) ⊕ J
variable (output : Y → S)

def view (cv : S) (d : DB X Y) : Partial S B :=
  fallback cv (fun x => (d (.inl x)).map output)

private theorem mem_phys (cv : S) (d : DB X Y) (z : Cell S B) (h : z ∈ occupied (view output cv d)) :
    (.inl (physical cv z) : X) ∈ occupied d ∧ tag cv (physical cv z) = z := by
  simp only [occupied,Finset.mem_filter,Finset.mem_univ,true_and] at h ⊢
  cases z with
  | inl x =>
    by_cases e : x.1 = cv
    · simp [view,fallback,e] at h
    · simpa [view,fallback,e,physical,tag] using h
  | inr b => simpa [view,fallback,physical,tag] using h

private theorem occupied_view (cv : S) (d : DB X Y) : (occupied (view output cv d)).card ≤ (occupied d).card := by
  apply Finset.card_le_card_of_injOn (fun z => (.inl (physical cv z) : X))
  · exact fun z hz => (mem_phys output cv d z hz).1
  · intro x hx y hy h
    exact (mem_phys output cv d x hx).2.symm.trans ((congrArg (tag cv) (Sum.inl.inj h)).trans (mem_phys output cv d y hy).2)

private theorem entry (cv : S) (d : DB X Y) (x : S × B) : view output cv d (tag cv x) = (d (.inl x)).map output := by
  rcases x with ⟨s,b⟩
  by_cases e : s = cv <;> simp [view,fallback,tag,e]

private theorem change_far (cv : S) (x : X) (r : Rest x Y) (u : Option Y) (z : Cell S B)
    (far : ∀ a : S × B, x = .inl a → z ≠ tag cv a) :
    view output cv (assemble x r u) z = view output cv (assemble x r none) z := by
  cases z with
  | inl a =>
    by_cases h : a.1 = cv
    · simp [view,fallback,h]
    · have e : (.inl a : X) ≠ x := by
        intro eq
        apply far a eq.symm
        simp [tag,h]
      simp [view,fallback,h,assemble_other _ _ _ e]
  | inr b =>
    have e : (.inl (cv,b) : X) ≠ x := by
      intro eq
      apply far _ eq.symm
      simp [tag]
    simp [view,fallback,assemble_other _ _ _ e]

private theorem clear (cv : S) (a : S × B) (r : Rest (.inl a : X) Y) (u : Option Y) :
    view output cv (assemble (.inl a) r u) = assemble (tag cv a)
      (fun z => view output cv (assemble (.inl a) r none) z.val) (u.map output) := by
  funext z
  by_cases e : z = tag cv a
  · subst z
    simp [entry]
  · rw [assemble_other _ _ _ e]
    exact change_far output cv _ r u z (fun b eq => by simpa only [Sum.inl.inj eq] using e)

private theorem right_ignored (cv : S) (x : J) (r : Rest (.inr x : X) Y) (u : Option Y) :
    view output cv (assemble (.inr x) r u) = view output cv (assemble (.inr x) r none) :=
  funext fun z => change_far output cv _ r u z (fun _ eq => by cases eq)

end Abstract

noncomputable abbrev records (cv : St) (d : Cells) : Partial St Blk := view (fun y => (halves y).1) cv d
private theorem balanced (P : St → Prop) :
    ((Finset.univ.filter fun y => P (halves y).1).card:ℝ)/Fintype.card Chain512 =
      ((Finset.univ.filter P).card:ℝ)/Fintype.card St := by
  let B := Finset.univ.filter P
  have eq : (Finset.univ.filter fun y => P (halves y).1).card = (B ×ˢ (Finset.univ : Finset St)).card := by
    apply Finset.card_equiv halves
    simp [B]
  rw [eq,Finset.card_product,Finset.card_univ,Fintype.card_congr halves,Fintype.card_prod,Nat.cast_mul,Nat.cast_mul]
  exact mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

theorem growth_records (cv : St) (P : Partial St Blk → Prop) (t : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (g : Growth P (t+1) δ) : Growth (fun d : Cells => P (records cv d)) t δ := by
  classical
  constructor
  · intro x r u bad
    cases x with
    | inl a =>
      exact (congrArg P (clear _ cv a r u)).mpr
        (g.mono _ _ _ ((congrArg P (clear _ cv a r none)).mp bad))
    | inr j => exact (congrArg P (right_ignored _ cv j r u)).mpr bad
  · intro x r sz clean
    cases x with
    | inl a =>
      let rest : Rest (tag cv a) St := fun z => records cv (assemble (.inl a) r none) z.val
      have erased := clear (fun y => (halves y).1) cv a r none
      have bound : (occupied rest).card ≤ t+1 :=
        (occupied_rest_le _ rest none).trans ((le_of_eq (congrArg (fun z => (occupied z).card) erased.symm)).trans
          ((occupied_view (fun y => (halves y).1) cv _).trans ((occupied_assemble_le ..).trans (Nat.succ_le_succ sz))))
      have ok : ¬P (assemble (tag cv a) rest none) := fun hh => clean ((congrArg P erased).mpr hh)
      have step := g.fresh _ rest bound ok
      have eq := balanced (fun y => P (assemble (tag cv a) rest (some y)))
      have repl (y : Chain512) : records cv (assemble (Sum.inl a) r (some y)) =
          assemble (tag cv a) rest (some (halves y).1) := clear (fun y => (halves y).1) cv a r (some y)
      simpa only [repl] using eq.le.trans step
    | inr j =>
      have no (y : Chain512) : ¬P (records cv (assemble (.inr j) r (some y))) := fun hit => clean ((congrArg P (right_ignored _ cv j r (some y))).mp hit)
      simpa only [no,not_false_eq_true,Finset.filter_false,Finset.card_empty,Nat.cast_zero,zero_div] using hδ

theorem recorded_at (cv : St) (d : Cells) (x : Left) :
    records cv d (tag cv x) = (d (.inl x)).map (fun y => (halves y).1) :=
  entry _ _ _ _

theorem records_empty (cv : St) : records cv (fun _ => none) = fun _ => none := by
  funext x
  cases x with
  | inl a => by_cases h : a.1 = cv <;> simp [records,view,fallback,h]
  | inr b => rfl

end Reduction.Compression.LongClass
#print axioms Reduction.Compression.LongClass.growth_records
