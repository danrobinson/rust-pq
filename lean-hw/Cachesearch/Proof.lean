import Cachesearch.Funs

open Aeneas Aeneas.Std Result
namespace slhdsa.cache

/-- At a hit, every earlier entry differs. At a miss, every entry differs. -/
def FirstMatch {N : Usize} (entries : Slice (LayerD2Entry N)) (target : U64)
    (answer : Option Usize) : Prop :=
  (∀ i (hi : i < entries.length), i < (answer.map UScalar.val).getD entries.length →
    entries.val[i].tree_index ≠ target) ∧
  ∀ p, answer = some p → ∃ hp : p.val < entries.length, entries.val[p.val].tree_index = target

theorem search {N : Usize} (entries : Slice (LayerD2Entry N)) (target : U64) :
    find_cached_index entries target ⦃ r => FirstMatch entries target r ⦄ := by
  unfold find_cached_index find_cached_index_loop
  apply loop.spec_decr_nat (measure := fun p : Usize => entries.length - p.val)
    (inv := fun p => p.val ≤ entries.length ∧
      ∀ i (hi : i < entries.length), i < p.val → entries.val[i].tree_index ≠ target)
  · rintro p ⟨bound, skipped⟩
    unfold find_cached_index_loop.body
    dsimp only
    split
    · rename_i more
      have inside : p.val < entries.length := more
      step as ⟨entry, hentry⟩
      split
      · rename_i hit
        rw [WP.spec_ok]
        constructor
        · exact skipped
        · intro q eq
          cases Option.some.inj eq
          exact ⟨inside, by simpa [hentry] using hit⟩
      · rename_i miss
        step as ⟨next, inc⟩
        refine ⟨by omega, ?_, by omega⟩
        intro i hi less
        by_cases eq : i = p.val
        · subst i
          simpa [hentry] using miss
        · exact skipped i hi (by omega)
    · rename_i stop
      have endpos : p.val = entries.length := by
        have : ¬ p.val < entries.length := stop
        omega
      rw [WP.spec_ok]
      exact ⟨by simpa [endpos] using skipped, by simp⟩
  · exact ⟨by simp, by simp⟩

/-- A direct hit can choose a later duplicate. Every returned index still
identifies the requested tree, and a miss rules out every matching entry. -/
def Matches {N : Usize} (entries : Slice (LayerD2Entry N)) (target : U64) :
    Option Usize → Prop
  | some p => ∃ hp : p.val < entries.length, entries.val[p.val].tree_index = target
  | none => ∀ i (hi : i < entries.length), entries.val[i].tree_index ≠ target

private theorem matches_of_first {N : Usize} {entries : Slice (LayerD2Entry N)}
    {target : U64} {r : Option Usize} (h : FirstMatch entries target r) : Matches entries target r := by
  cases r with
  | none => exact fun i hi => h.1 i hi hi
  | some p => exact h.2 p rfl

theorem lookup {N : Usize} (entries : Slice (LayerD2Entry N)) (target : U64) :
    lookup_cached_index entries target ⦃ r => Matches entries target r ⦄ := by
  unfold lookup_cached_index
  step as ⟨empty, hempty⟩
  split
  · rename_i yes
    rw [WP.spec_ok]
    intro i hi
    have zero : entries.length = 0 := hempty ▸ yes
    omega
  · simp only [lift, bind_ok]
    split
    · step as ⟨entry, hentry⟩
      split
      · rename_i hit
        rw [WP.spec_ok]
        exact ⟨by assumption, by simpa [hentry] using hit⟩
      · step with search entries target as ⟨r, hr⟩
        exact matches_of_first hr
    · step with search entries target as ⟨r, hr⟩
      exact matches_of_first hr

end slhdsa.cache
