import Cachepath.NativeVerify.ForsProgram

open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Fors

private abbrev Iterator (α : Type) := core.slice.iter.IterMut α

private def rewriteBody {α : Type} (f : α → α) (iter : Iterator α) (back : Iterator α → Iterator α) :
    Result (ControlFlow (Iterator α × (Iterator α → Iterator α)) (Iterator α × (Iterator α → Iterator α))) := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => ok (done (iter1, fun im => back (next_back im none)))
  | some x => ok (cont (iter1, fun im => back (next_back im (some (f x)))))

private def rewriteAll {α : Type} (f : α → α) (s : Slice α) := loop
  (fun (it,back) => rewriteBody f it back)
  ((⟨s,0⟩ : Iterator α),id)

private def Invariant {α : Type} [Inhabited α] (f : α → α) (s : Slice α) (it : Iterator α) (back : Iterator α → Iterator α) :=
  it.slice = s ∧ it.i ≤ s.length ∧ ∀ other : Iterator α, other.slice.length=s.length →
    (back other).slice.length=s.length ∧
    (∀ j < it.i, (back other).slice.val[j]! = f s.val[j]!) ∧
    (∀ j, it.i ≤ j → j < s.length → (back other).slice.val[j]! = other.slice.val[j]!)

private theorem rewrite_all {α : Type} [Inhabited α] (f : α → α) (s : Slice α) :
    rewriteAll f s ⦃ it back => (back it).slice.length=s.length ∧ ∀ j<s.length,
      (back it).slice.val[j]! = f s.val[j]! ⦄ := by
  unfold rewriteAll
  apply loop.spec_decr_nat (measure := fun q : Iterator α × (Iterator α → Iterator α) => s.length-q.1.i)
    (inv := fun q => Invariant f s q.1 q.2)
  · rintro ⟨it,back⟩ ⟨hs,hi,hb⟩
    simp only at hs hi hb
    unfold rewriteBody
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
      simp only [step_simps]
      refine ⟨⟨hsl.trans hs,by omega,fun other len => ?_⟩,by omega⟩
      simp only [hback]
      let value := f it.slice.val[it.i]!
      obtain ⟨h1,h2,h3⟩ := hb {slice:=other.slice.setAtNat it.i value,i:=other.i} (by simp [len])
      simp only [value] at h2 h3
      have wrote := fun j => Slice.getElem!_Nat_setAtNat other.slice it.i j value (by simpa [len] using valid)
      simp only [value] at wrote
      refine ⟨h1, fun j hj => ?_, fun j hj hj' => ?_⟩
      · by_cases same : j=it.i
        · subst j
          rw [h3 _ (by omega) valid,wrote]
          simp only [ite_true,hs]
        · exact h2 j (by omega)
      · rw [h3 j (by omega) hj',wrote]
        simp [show j ≠ it.i by omega]
  · simp [Invariant]

open ShakeBatch
variable [machine : Machine]

theorem zero_leaf_tail (s : Slice (Array U64 machine.width)) :
    recover_loop0_loop3 ⟨s,0⟩ id ⦃ it back => (back it).slice.length=s.length ∧
      ∀ j<s.length, (back it).slice.val[j]! = Array.repeat machine.width 0#u64 ⦄ := by
  suffices eq : recover_loop0_loop3 ⟨s,0⟩ id = rewriteAll (fun _ => Array.repeat machine.width 0#u64) s by
    rw [eq]; exact rewrite_all _ s
  unfold recover_loop0_loop3 rewriteAll
  congr 1
  funext ⟨it,back⟩
  dsimp only
  unfold recover_loop0_loop3.body rewriteBody
  congr 1
  funext ⟨o,next,restore⟩
  cases o <;> rfl

theorem zero_pair_tail (s : Slice (Array U64 machine.width)) :
    recover_loop0_loop4_loop2 ⟨s,0⟩ id ⦃ it back => (back it).slice.length=s.length ∧
      ∀ j<s.length, (back it).slice.val[j]! = Array.repeat machine.width 0#u64 ⦄ := by
  exact zero_leaf_tail s

theorem pad_pair_word (marker : U64) (s : Slice U64) :
    recover_loop0_loop4_loop3 marker ⟨s,0⟩ id ⦃ it back => (back it).slice.length=s.length ∧
      ∀ j<s.length, (back it).slice.val[j]! = (s.val[j]! ||| marker) ⦄ := by
  apply (show recover_loop0_loop4_loop3 marker ⟨s,0⟩ id = rewriteAll (fun x => x ||| marker) s from ?_) ▸
    rewrite_all (fun x => x ||| marker) s
  unfold recover_loop0_loop4_loop3 rewriteAll
  congr 1
  funext ⟨it,back⟩
  dsimp only
  unfold recover_loop0_loop4_loop3.body rewriteBody
  congr 1
  funext ⟨o,next,restore⟩
  cases o <;> simp only [lift,bind_ok] <;> rfl

end slhdsa.NativeVerify.Fors
