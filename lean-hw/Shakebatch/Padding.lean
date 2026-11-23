import Shakebatch.Addr
open Aeneas Aeneas.Std Result
namespace slhdsa.ShakeBatch
abbrev WordIter := core.slice.iter.IterMut U64

def lastBit (w : U64) := w ||| 0x8000000000000000#u64

private def Invariant (s : Slice U64) (it : WordIter) (back : WordIter → WordIter) :=
  it.slice = s ∧ it.i ≤ s.length ∧ ∀ other : WordIter, other.slice.length=s.length →
    (back other).slice.length=s.length ∧
    (∀ j < it.i, (back other).slice.val[j]! = lastBit s.val[j]!) ∧
    (∀ j, it.i ≤ j → j < s.length → (back other).slice.val[j]! = other.slice.val[j]!)

/-- The terminating FIPS 202 padding bit is set in every lane, even when the domain byte shares its word. -/
theorem high_bit (s : Slice U64) :
    shake.batch.header_loop2 ⟨s,0⟩ id ⦃ it back =>
      (back it).slice.length=s.length ∧ ∀ j < s.length, (back it).slice.val[j]! = lastBit s.val[j]! ⦄ := by
  unfold shake.batch.header_loop2
  apply loop.spec_decr_nat (measure := fun q : WordIter × (WordIter → WordIter) => s.length-q.1.i)
    (inv := fun q => Invariant s q.1 q.2)
  · rintro ⟨it,back⟩ ⟨hs,hi,hb⟩
    simp only at hs hi hb
    unfold shake.batch.header_loop2.body
    apply WP.spec_bind (core.slice.iter.IteratorIterMut.next.spec it)
    rintro ⟨opt,it1,next_back⟩ ⟨hsl,hnone,ho⟩
    simp only [uncurry]
    cases opt with
    | none =>
      obtain ⟨h1,h2,-⟩ := hb it1 (by rw [hsl,hs])
      simp only [step_simps,hnone]
      exact ⟨h1,fun j hj => h2 j (by rw [hs] at ho; omega)⟩
    | some w =>
      obtain ⟨hlt,rfl,hnext,hback⟩ := ho
      have valid : it.i < s.length := hs ▸ hlt
      have shift : (1#u64 <<< 63#i32) = ok 0x8000000000000000#u64 := by rfl
      simp only [shift,bind_ok,lift,step_simps]
      refine ⟨⟨hsl.trans hs,by omega,fun other len => ?_⟩,by omega⟩
      simp only [hback]
      let value := lastBit it.slice.val[it.i]!
      obtain ⟨h1,h2,h3⟩ := hb {slice:=other.slice.setAtNat it.i value,i:=other.i} (by simp [len])
      simp only [value,lastBit] at h2 h3
      have wrote := fun j => Slice.getElem!_Nat_setAtNat other.slice it.i j value (by simpa [len] using valid)
      simp only [value,lastBit] at wrote
      refine ⟨h1, fun j hj => ?_, fun j hj hj' => ?_⟩
      · by_cases same : j=it.i
        · subst j
          rw [h3 _ (by omega) valid,wrote]
          simp only [ite_true,lastBit,hs]
        · exact h2 j (by omega)
      · rw [h3 j (by omega) hj',wrote]
        simp [show j ≠ it.i by omega]
  · simp [Invariant]
end slhdsa.ShakeBatch
