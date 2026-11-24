import Shakebatch.Scatter
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ShakeBatch

theorem range_fold {S : Type} (body : Range → S → Result (ControlFlow (Range × S) S))
    (endAt : Usize) (init : S) (p : Nat → S → Prop) (start : p 0 init)
    (advance : ∀ (it : Range) (s : S), it.end=endAt → it.start.val < endAt.val → p it.start.val s →
      body it s ⦃ r => ∃ next out, r=cont (next,out) ∧ next.end=endAt ∧
        next.start.val=it.start.val+1 ∧ p next.start.val out ⦄)
    (finish : ∀ (it : Range) (s : S), it.start.val=endAt.val → it.end=endAt →
      body it s=ok (done s)) :
    loop (fun q : Range × S => body q.1 q.2) (⟨0#usize,endAt⟩,init) ⦃ out => p endAt.val out ⦄ := by
  apply loop.spec_decr_nat (measure := fun q : Range × S => endAt.val-q.1.start.val)
    (inv := fun q => q.1.end=endAt ∧ q.1.start.val ≤ endAt.val ∧ p q.1.start.val q.2)
  · rintro ⟨it,s⟩ ⟨he,hi,prior⟩
    simp only at he hi prior ⊢
    by_cases more : it.start.val < endAt.val
    · apply WP.spec_mono (advance it s he more prior)
      rintro _ ⟨next,out,rfl,hend,idx,post⟩
      simp only [step_simps]
      exact ⟨hend,by omega,post,by omega⟩
    · have eq : it.start.val=endAt.val := by omega
      rw [finish it s eq he]
      simpa [eq] using prior
  · simpa using start
end slhdsa.ShakeBatch
