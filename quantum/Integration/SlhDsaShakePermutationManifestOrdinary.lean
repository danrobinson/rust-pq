import Integration.SlhDsaShakePermutationManifestRisk

/-! Conditioning a random two-way permutation on an entire XOR-absorption
prefix tree. Every successful permutation determines a unique tuple of
nonzero capacities, rate responses and a compatible permutation extension. -/
namespace Reduction.ShakePermutation.Manifest.Ordinary
open Classical Fix
noncomputable section

variable {I : Type}
def prev (r : I → Rate) : Option I → Rate
  | none => 0
  | some i => r i

def inputs (t : Tree I) (c : Caps I) (r : I → Rate) : I ↪ Words where
  toFun i := join (rateXor (t.block i) (prev r (t.parent i))) (branch c (t.parent i))
  inj' i j e := by
    have hp := branch_injective c (by simpa only [cap_join] using congrArg capOf e)
    have hr : rateXor (t.block i) (prev r (t.parent j)) = rateXor (t.block j) (prev r (t.parent j)) := by
      simpa only [rate_join,hp] using congrArg rateOf e
    apply t.siblings
    apply Prod.ext hp
    funext w
    have h := congrArg (fun a => a ^^^ prev r (t.parent j) w) (congrFun hr w)
    simpa only [rateXor,UInt64.xor_assoc,UInt64.xor_self,UInt64.xor_zero] using h

def Good (t : Tree I) (π : Permutation) :=
  Function.Injective (fun i => capOf (ordinary π (t.paths i))) ∧
  ∀ i, capOf (ordinary π (t.paths i)) ≠ 0

abbrev Assignment (I : Type) := (I → Rate) × Caps I
abbrev Extension (t : Tree I) (w : Assignment I) :=
  {π : Permutation // imageTuple (inputs t w.2 w.1) π = outputs w.2 w.1}

private theorem step (t : Tree I) (π : Permutation) (i : I) :
    ordinary π (t.paths i) = π (join (rateXor (t.block i)
      (rateOf (ordinary π ((t.parent i).elim [] t.paths))))
      (capOf (ordinary π ((t.parent i).elim [] t.paths)))) := by
  rw [t.step i]
  simp only [ordinary,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem states (t : Tree I) (w : Assignment I) (e : Extension t w) (i : I) :
    ordinary e.val (t.paths i) = outputs w.2 w.1 i := by
  have induction_step (n : ℕ) (i : I) (hn : (t.paths i).length = n) :
      ordinary e.val (t.paths i) = outputs w.2 w.1 i := by
    induction n using Nat.strong_induction_on generalizing i with
    | ind n ih =>
      have h := DFunLike.congr_fun e.property i
      change e.val (join (rateXor (t.block i) (prev w.1 (t.parent i))) (branch w.2 (t.parent i))) = _ at h
      rw [step]
      cases hp : t.parent i with
      | none => rw [hp] at h; exact h
      | some j =>
        rw [t.step i,hp] at hn
        simp only [Option.elim_some,List.length_append,List.length_singleton] at hn
        rw [Option.elim_some,ih (t.paths j).length (by omega) j rfl]
        change e.val (join (rateXor (t.block i) (rateOf (join (w.1 j) (w.2 j).val)))
          (capOf (join (w.1 j) (w.2 j).val))) = _
        rw [rate_join,cap_join]
        rw [hp] at h
        exact h
  exact induction_step _ i rfl

def observed (t : Tree I) (π : Permutation) (ok : Good t π) : Assignment I :=
  (fun i => rateOf (ordinary π (t.paths i)),⟨fun i => ⟨_,ok.2 i⟩,
    fun _ _ e => ok.1 (congrArg Subtype.val e)⟩)

theorem compatible (t : Tree I) (π : Permutation) (ok : Good t π) :
    imageTuple (inputs t (observed t π ok).2 (observed t π ok).1) π =
      outputs (observed t π ok).2 (observed t π ok).1 := by
  apply DFunLike.ext; intro i
  change π (join (rateXor (t.block i) (prev _ (t.parent i))) (branch _ (t.parent i))) =
    join (rateOf (ordinary π (t.paths i))) (capOf (ordinary π (t.paths i)))
  rw [join_split,step]
  cases t.parent i <;> rfl

theorem good_of (t : Tree I) (w : Assignment I) (e : Extension t w) : Good t e.val := by
  have c (i) : capOf (ordinary e.val (t.paths i)) = (w.2 i).val := by
    rw [states t w e i]; apply cap_join
  constructor
  · intro i j h; exact w.2.injective (Subtype.ext ((c i).symm.trans (h.trans (c j))))
  · intro i; rw [c]; exact (w.2 i).property

def enumeration (t : Tree I) : (Σ w : Assignment I, Extension t w) ≃ {π : Permutation // Good t π} where
  toFun z := ⟨z.2.val,good_of t z.1 z.2⟩
  invFun π := ⟨observed t π.val π.property,π.val,compatible t π.val π.property⟩
  right_inv _ := rfl
  left_inv := by
    rintro ⟨w,e⟩
    have hw : observed t e.val (good_of t w e) = w := by
      apply Prod.ext
      · funext i
        change rateOf (ordinary e.val (t.paths i)) = _
        rw [states]; apply rate_join
      · apply DFunLike.ext; intro i; apply Subtype.ext
        change capOf (ordinary e.val (t.paths i)) = _
        rw [states]; apply cap_join
    apply Sigma.ext hw
    exact (Subtype.heq_iff_coe_eq (by dsimp only; rw [hw]; intro; rfl)).mpr rfl

end
end Reduction.ShakePermutation.Manifest.Ordinary
#print axioms Reduction.ShakePermutation.Manifest.Ordinary.enumeration
