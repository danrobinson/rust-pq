import Chainni.Group
import Slhdsa.Proofs.InPlace
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Intel.Chain
open ChainNiRust.sha256.x86

def expected (N : Usize) (state : Array U32 8#usize) (blocks : Rows) (starts ends : Slice U32) (i : Nat) :=
  runBlock N.val (wv state.val) (bytes blocks.val[i]!.val) starts.val[i]!.val ends.val[i]!.val

private theorem bind_if {α β : Type} (p : Prop) [Decidable p] (a b : Result α) (f : α → Result β) :
    Std.bind (if p then a else b) f = if p then Std.bind a f else Std.bind b f := by split <;> rfl

theorem groups_spec (N : Usize) (state : Array U32 8#usize) (iv : Array Reg 2#usize)
    (blocks : Rows) (starts ends : Slice U32) (pairs : Usize) (hn : N.val ≤ 32)
    (init : stateWords (packedState iv) = wv state.val) (fits : 2*pairs.val ≤ blocks.length)
    (hs : blocks.length ≤ starts.length) (he : blocks.length ≤ ends.length) :
    chains_loop0 N ⟨0#usize,pairs⟩ state blocks starts ends iv ⦃ out =>
      InPlace.Processed (expected N state blocks starts ends) blocks out (2*pairs.val) ⦄ := by
  unfold chains_loop0
  apply loop.spec_decr_nat (measure := fun p : core.ops.range.Range Usize × Rows => pairs.val-p.1.start.val)
    (inv := fun p => p.1.end = pairs ∧ p.1.start.val ≤ pairs.val ∧
      InPlace.Processed (expected N state blocks starts ends) blocks p.2 (2*p.1.start.val))
  · rintro ⟨it,buf⟩ ⟨hend,hle,processed⟩
    simp only at hend hle processed
    have len := processed.1
    unfold chains_loop0.body
    by_cases lt : it.start.val < it.end.val
    · have small : it.start.val < pairs.val := hend ▸ lt
      step with core.iter.range.IteratorRange.next_Usize_some_spec it lt as ⟨o,next,ho,hnxt,hend'⟩
      simp only [ho,lift,bind_ok]
      step as ⟨off,hoff⟩
      step as ⟨stop,hstop⟩
      step as ⟨pair,back,hpair,lp,hback⟩
      step as ⟨ss,hss,ls⟩
      step as ⟨es,hes,le⟩
      conv => lhs; equals (group N iv state pair ss es >>= fun r => ok (cont (next,back r))) =>
        unfold group
        simp only [bind_tc_eq,Std.bind_assoc,bind_ok,bind_if,lift]
      step with group_spec N iv state pair ss es hn init (by omega) (by omega) (by omega) as ⟨r,h⟩
      have lr := h.1
      refine ⟨hend'.trans hend,by omega,?_,by omega⟩
      rw [show 2*next.start.val = 2*it.start.val + r.length by omega]
      apply InPlace.advance _ _ _ _ _ _ processed (by omega)
      · simp only [hback,Slice.setSlice!_val,hoff]
      · intro k hk
        have actual := h.2 k (by omega)
        have old := processed.2 (off.val+k) (by omega)
        rw [if_neg (by omega)] at old
        have bounds (l : Nat) (hl : stop.val ≤ l) : stop.val ≤ l ∧ off.val+k < stop.val := by omega
        simp only [hpair,hss,hes,List.getElem!_slice _ _ _ buf.val (bounds _ (by change stop.val ≤ buf.length; omega)),
          List.getElem!_slice _ _ _ starts.val (bounds _ (by change stop.val ≤ starts.length; omega)),
          List.getElem!_slice _ _ _ ends.val (bounds _ (by change stop.val ≤ ends.length; omega))] at actual
        rw [old] at actual
        simpa only [expected,hoff] using actual
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val = pairs.val := by rw [hend] at lt; omega
      exact eq ▸ processed
  · simp [InPlace.Processed]

end slhdsa.Intel.Chain
