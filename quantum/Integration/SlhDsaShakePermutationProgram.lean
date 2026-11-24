import Integration.SlhDsaShakePermutationHiddenSets
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-! Program the full outputs of a family of disjoint one-block permutation
inputs. Swapping the old and new outputs keeps the public inverse consistent. -/
namespace Reduction.ShakePermutation.Program
open Classical
variable {I J : Type}
def flip : Equiv.Perm (Bool × J) where
  toFun a := (!a.1,a.2)
  invFun a := (!a.1,a.2)
  left_inv a := by simp
  right_inv a := by simp

def column (f : (I × Bool × J) ↪ Words) (i : I) : (Bool × J) ↪ Words where
  toFun t := f (i,t)
  inj' _ _ eq := congrArg Prod.snd (f.injective eq)

noncomputable def exchange (f : (Bool × J) ↪ Words) : Permutation := flip.viaEmbedding f

theorem exchange_hit (f : (Bool × J) ↪ Words) (b : Bool) (j : J) :
    exchange f (f (b,j)) = f (!b,j) := Equiv.Perm.viaEmbedding_apply _ _ _

theorem exchange_miss (f : (Bool × J) ↪ Words) (w : Words) (h : w ∉ Set.range f) :
    exchange f w = w := Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ h

theorem exchange_self (f : (Bool × J) ↪ Words) (w : Words) : exchange f (exchange f w) = w := by
  by_cases mem : w ∈ Set.range f
  · obtain ⟨⟨b,j⟩,rfl⟩ := mem
    simp only [exchange_hit,Bool.not_not]
  · simp only [exchange_miss f w mem]

noncomputable def changed (π : Permutation) (f : (I × Bool × J) ↪ Words) (i : I) : Permutation :=
  π.trans (exchange (column f i))

theorem changed_hit (π : Permutation) (f : (I × Bool × J) ↪ Words) (i : I) (j : J) (x : Words)
    (old : π x = f (i,false,j)) : changed π f i x = f (i,true,j) := by
  change exchange (column f i) (π x) = _
  rw [old]
  exact exchange_hit (column f i) false j

noncomputable def owner (f : (I × Bool × J) ↪ Words) (w : Words) : Option I :=
  if h : ∃ t, f t = w then some h.choose.1 else none

private theorem owner_hit (f : (I × Bool × J) ↪ Words) (i : I) (b : Bool) (j : J) :
    owner f (f (i,b,j)) = some i := by
  have ex : ∃ t, f t = f (i,b,j) := ⟨_,rfl⟩
  simp only [owner,dite_eq_left ex,f.injective ex.choose_spec]

theorem agree (π : Permutation) (f : (I × Bool × J) ↪ Words) (i : I) (p : Port)
    (miss : owner f (if p.1 then p.2 else π p.2) ≠ some i) :
    oracle (changed π f i) p = oracle π p := by
  have clean : (if p.1 then p.2 else π p.2) ∉ Set.range (column f i) := by
    rintro ⟨⟨b,j⟩,eq⟩
    apply miss
    exact eq ▸ owner_hit f i b j
  rcases p with ⟨d,w⟩
  cases d with
  | false => exact exchange_miss _ _ clean
  | true =>
    change π.symm ((exchange (column f i)).symm w) = π.symm w
    apply congrArg π.symm
    exact (exchange (column f i)).symm_apply_eq.mpr (exchange_miss _ _ clean).symm

/-- In either coherent direction each basis input belongs to at most one
reprogrammed column. The sum of squared distances grows quadratically in
the number of quantum calls, independently of the size of a column. -/
theorem column_queries [Fintype I] [DecidableEq I] {E : Type} [Fintype E]
    (π : Permutation) (f : (I × Bool × J) ↪ Words)
    (op : ℕ → Hidden.Vec E ≃ₗᵢ[ℂ] Hidden.Vec E) (x : Hidden.Vec E) (q : ℕ) :
    ∑ i, ‖Hidden.interact (changed π f i) op x q - Hidden.interact π op x q‖^2 ≤
      4*(q:ℝ)^2*‖x‖^2 := by
  classical
  let a (p : Port) := owner f (if p.1 then p.2 else π p.2)
  have sharp := Hidden.changed_call_sum (E:=E) π (changed π f) a (fun i => {some i}) 1
    (fun i p h => agree π f i p (fun e => h (Finset.mem_singleton.mpr e)))
    (by intro z; cases z with
        | none => simp
        | some j => simpa only [Finset.mem_singleton,Option.some.injEq] using
            (show (Finset.univ.filter (fun i : I => j = i)).card ≤ 1 by
              apply Finset.card_le_one.mpr
              intro a ha b hb
              exact (Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2))
  apply Hidden.query_hybrid π (changed π f) 4 _ op x q
  simpa only [Nat.cast_one,mul_one] using sharp

end Reduction.ShakePermutation.Program
#print axioms Reduction.ShakePermutation.Program.changed_hit
#print axioms Reduction.ShakePermutation.Program.column_queries
