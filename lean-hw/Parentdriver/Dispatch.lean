import Parentdriver.Reduce
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformParent.Driver

theorem tree_active {G N : Usize} (K : Kernel G) (p : Spec.Params) (pk : Spec.Bytes)
    (a : address.Adrs) (s : Array U64 8#usize) (first : U32) (v : Nodes N) (count : Usize)
    (shape : N.val = 24 ∨ N.val = 32) (good : Correct (N := N) K p pk s) (hg : 0 < G.val)
    (hv : 2*count.val ≤ v.length) (hi : first.val + count.val ≤ 2^32) :
    treeActive K s a first v count ⦃ n r =>
      n.val = count.val/G.val*G.val ∧ Reduced p pk a first v r n.val ⦄ := by
  unfold treeActive
  step as ⟨q,hq⟩
  have limit : q.val*G.val ≤ count.val := hq ▸ Nat.div_mul_le_self _ _
  step as ⟨last,hl⟩
  step as ⟨it,hit,hs⟩
  have he : it = ⟨⟨0#usize,last⟩,G⟩ := by cases it; simp_all
  rw [he]
  step with tree_batches_spec K p pk a s first v last shape good hg
    (by simp [hl]) (by omega) (by omega) as ⟨r,hr⟩
  exact ⟨by rw [hl,hq],hr⟩

def processed (enabled : Bool) (count lanes : Nat) := if enabled then count/lanes*lanes else 0

theorem tree_parents {G N : Usize} (K : Kernel G) (enabled : Bool) (p : Spec.Params) (pk : Spec.Bytes)
    (a : address.Adrs) (s : Array U64 8#usize) (first : U32) (v : Nodes N) (count : Usize)
    (shape : N.val = 24 ∨ N.val = 32) (available : K.available = ok enabled)
    (good : enabled = true → Correct (N := N) K p pk s) (hg : 0 < G.val)
    (hv : 2*count.val ≤ v.length) (hi : first.val+count.val ≤ 2^32) :
    treeParents K s a first v count ⦃ n r =>
      n.val = processed enabled count.val G.val ∧ Reduced p pk a first v r n.val ⦄ := by
  unfold treeParents
  apply WP.spec_bind (Pₘ := fun b => b = true)
  · rcases shape with h | h <;> rw [h] <;> exact (WP.spec_ok _).2 rfl
  rintro _ rfl
  simp only [↓reduceIte]
  by_cases small : count < G
  · have div : count.val/G.val = 0 := Nat.div_eq_of_lt small
    simp [small,processed,div,Reduced]
  · simp only [small,↓reduceIte,available,bind_ok]
    cases enabled with
    | false => simp [processed,Reduced]
    | true => simpa only [processed,↓reduceIte] using tree_active K p pk a s first v count shape (good rfl) hg hv hi

end slhdsa.PlatformParent.Driver
