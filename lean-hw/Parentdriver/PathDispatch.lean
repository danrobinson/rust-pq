import Parentdriver.PathReduce
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformParent.Driver

theorem path_active {G N : Usize} (K : Kernel G) (p : Spec.Params) (pk : Spec.Bytes)
    (a : address.Adrs) (s : Array U64 8#usize) (v : Nodes N) (idx : Slice U32) (sig : Slice U8) (h off : Usize)
    (shape : N.val = 24 ∨ N.val = 32) (good : Correct (N := N) K p pk s) (hg : 0 < G.val)
    (hi : v.length ≤ idx.length) (hh : h.val+1 ≤ Usize.max) (bounds : SigBounds N.val h.val off.val v.length sig) :
    pathActive K s a v idx sig h off ⦃ n r ix => n.val = v.length/G.val*G.val ∧
      Paths p pk a v idx sig h.val off.val n.val r ix ⦄ := by
  unfold pathActive
  step as ⟨q,hq⟩
  have limit : q.val*G.val ≤ v.length := hq ▸ Nat.div_mul_le_self _ _
  step as ⟨last,hl⟩
  step as ⟨it,hit,hs⟩
  have he : it = ⟨⟨0#usize,last⟩,G⟩ := by cases it; simp_all
  rw [he]
  step with path_batches_spec K p pk a s v idx sig h off last shape good hg
    (by simp [hl]) (by omega) hi hh bounds as ⟨r,ix,hr⟩
  exact ⟨by rw [hl,hq]; rfl,hr⟩

theorem path_parents {G N : Usize} (K : Kernel G) (enabled : Bool) (p : Spec.Params) (pk : Spec.Bytes)
    (a : address.Adrs) (s : Array U64 8#usize) (v : Nodes N) (idx : Slice U32) (sig : Slice U8) (h off : Usize)
    (shape : N.val = 24 ∨ N.val = 32) (available : K.available = ok enabled)
    (good : enabled = true → Correct (N := N) K p pk s) (hg : 0 < G.val)
    (hi : v.length ≤ idx.length) (hh : h.val+1 ≤ Usize.max) (bounds : SigBounds N.val h.val off.val v.length sig) :
    pathParents K s a v idx sig h off ⦃ n r ix => n.val = processed enabled v.length G.val ∧
      Paths p pk a v idx sig h.val off.val n.val r ix ⦄ := by
  unfold pathParents
  apply WP.spec_bind (Pₘ := fun b => b = true)
  · rcases shape with h | h <;> rw [h] <;> exact (WP.spec_ok _).2 rfl
  rintro _ rfl
  simp only [↓reduceIte]
  by_cases small : v.len < G
  · have div : v.length/G.val = 0 := Nat.div_eq_of_lt small
    simp [small,processed,div,Paths,IndexRange]
  · simp only [small,↓reduceIte,available,bind_ok]
    cases enabled with
    | false => simp [processed,Paths,IndexRange]
    | true => simpa only [processed,↓reduceIte] using path_active K p pk a s v idx sig h off shape (good rfl) hg hi hh bounds

end slhdsa.PlatformParent.Driver
