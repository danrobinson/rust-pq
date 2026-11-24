import Integration.SlhDsaShakePermutationTails
import Integration.SlhDsaShakePermutationShear
import Integration.SlhDsaRawSearch

/-! A coherent relabeling of the h and F recording databases in the
three-mask sponge simulator. Each chosen reachable capacity is paired with
one input path. A swap also xors the pre-shear rate into the recorded value. -/
namespace Reduction.ShakePermutation.Relabel
open Tails Classical
variable (π : Permutation) (k k' : Db)

def run : List Rate → Option (Rate × Capacity)
  | [] => some (fun _ => 0,fun _ => 0)
  | r :: rs => -- process in reverse chronological order
    do
      let (_,z) ← run rs
      let u ← k r
      let m := (layout π).middle r z u
      let v ← k' m.1
      return (m.1,(layout π).finish m.2 v)

theorem run_tail {rs : List Rate} {z : Capacity} :
    (∃ h, run π k k' rs.reverse = some (h,z)) ↔ Graph.Tail (layout π) k k' rs z := by
  constructor
  · intro e
    induction rs using List.reverseRecOn generalizing z with
    | nil => obtain ⟨h,e⟩ := e; have ez : (layout π).zero = z := congrArg Prod.snd (Option.some.inj e); rw [← ez]; exact .root
    | append_singleton ls r ih =>
      obtain ⟨h,e⟩ := e
      simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append] at e
      unfold run at e
      cases hv : run π k k' ls.reverse with
      | none => simp [hv] at e
      | some m =>
        cases hu : k r with
        | none => simp [hv,hu] at e
        | some u =>
          cases hw : k' ((layout π).middle r m.2 u).1 with
          | none => simp [hv,hu,hw] at e
          | some w =>
            simp [hv,hu,hw] at e
            rw [← e.2]
            exact .step (ih ⟨_,hv⟩) hu hw
  · intro tail
    induction tail with
    | root => exact ⟨_,rfl⟩
    | @step _ z r u v prev hu hw ih =>
      obtain ⟨head,eq⟩ := ih
      exact ⟨((layout π).middle r z u).1,by simp [run,eq,hu,hw]⟩

abbrev Path (L : ℕ) := BList Rate L
def visit {L : ℕ} (x : Path L) := run π k k' (List.ofFn x.2).reverse

/-- Choose one path also on graphs with cycles or ambiguous tails. -/
noncomputable def chosen (L : ℕ) (z : Capacity) : Option (Path L × Rate) :=
  if h : ∃ b : Path L × Rate, visit π k k' b.1 = some (b.2,z) then some h.choose else none

theorem chosen_sound {L : ℕ} {z : Capacity} {x : Path L} {h : Rate}
    (e : chosen π k k' L z = some (x,h)) : visit π k k' x = some (h,z) := by
  unfold chosen at e
  split at e
  · rename_i ok; simpa only [Option.some.inj e] using ok.choose_spec
  · contradiction

noncomputable def mate {L : ℕ} (x : Path L) : Option (Capacity × Rate) := by
  classical
  exact match visit π k k' x with
    | none => none
    | some (h,z) => if chosen π k k' L z = some (x,h) then some (z,h) else none

theorem mates {L : ℕ} {x : Path L} {z : Capacity} {h : Rate} :
    chosen π k k' L z = some (x,h) ↔ mate π k k' x = some (z,h) := by
  classical
  constructor
  · intro e; simp [mate,chosen_sound π k k' e,e]
  · intro e
    unfold mate at e
    cases eq : visit π k k' x with
    | none => simp [eq] at e
    | some a =>
      rcases a with ⟨hh,zz⟩
      rw [eq] at e
      dsimp only at e
      split at e
      · rename_i ok; cases Option.some.inj e; exact ok
      · contradiction

abbrev Cells (L : ℕ) := Sum Capacity (Path L) → Option Rate

def twist (h : Rate) := Option.map (fun v : Rate => rateXor v h)
@[simp] theorem twist_twice (h : Rate) (v : Option Rate) : twist h (twist h v) = v := by
  cases v <;> simp [twist]

noncomputable def swap (L : ℕ) (d : Cells L) : Cells L
  | .inl z => match chosen π k k' L z with
    | none => d (.inl z)
    | some (x,h) => twist h (d (.inr x))
  | .inr x => match mate π k k' x with
    | none => d (.inr x)
    | some (z,h) => twist h (d (.inl z))

theorem swap_twice (L : ℕ) : Function.Involutive (swap π k k' L) := by
  intro d; funext i; cases i with
  | inl z =>
    cases e : chosen π k k' L z with
    | none => simp [swap,e]
    | some a => rcases a with ⟨x,h⟩; simp [swap,e,(mates π k k').mp e]
  | inr x =>
    cases e : mate π k k' x with
    | none => simp [swap,e]
    | some a => rcases a with ⟨z,h⟩; simp [swap,e,(mates π k k').mpr e]

abbrev Registers (L : ℕ) := (Db × Db) × Cells L
noncomputable local instance (L : ℕ) : Fintype (Registers L)  := by
  classical
  letI : Fintype Rate := inferInstance
  letI : Fintype Capacity := inferInstance
  letI : Fintype (Path L) := inferInstance
  letI : Fintype (Capacity ⊕ Path L) := inferInstance
  letI : Fintype (Cells L) := inferInstance
  letI : Fintype Db := inferInstance
  unfold Registers; infer_instance
noncomputable def basisMap (L : ℕ) : Equiv.Perm (Registers L) :=
  Function.Involutive.toPerm (fun d => (d.1,swap π d.1.1 d.1.2 L d.2))
    (fun d => Prod.ext rfl (swap_twice π d.1.1 d.1.2 L d.2))

noncomputable def isometry (L : ℕ) :
    EuclideanSpace ℂ (Registers L) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Registers L) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (basisMap π L)

theorem isometry_basis (L : ℕ) (d : Registers L) (a : ℂ) :
    isometry π L (PiLp.single 2 d a) = PiLp.single 2 (basisMap π L d) a :=
  LinearIsometryEquiv.piLpCongrLeft_single ..

end Reduction.ShakePermutation.Relabel
#print axioms Reduction.ShakePermutation.Relabel.run_tail
#print axioms Reduction.ShakePermutation.Relabel.isometry_basis
