import Chainni.Shared
open Aeneas Aeneas.Std Result
namespace slhdsa.Intel.Chain

theorem run_split (n : Nat) (st : List Word) (b : Spec.Bytes) (s x e : Nat) (hx : x ≤ e-s) :
    runBlock n st (runBlock n st b s (s+x)) (s+x) e = runBlock n st b s e := by
  by_cases rev : e < s
  · have zero : x = 0 := by omega
    simp [zero,runBlock_le]
  have stop : e = s+x+(e-(s+x)) := by omega
  generalize e-(s+x) = left at stop
  subst e
  induction left with
  | zero => simp [runBlock_le]
  | succ k ih =>
    rw [runBlock_succ,show s+x+(k+1)=s+((x+k)+1) by omega,runBlock_succ]
    have h := ih (by omega) (by omega)
    rw [show s+(x+k)=s+x+k by omega,h]

def Ended (N : Usize) (state : Array U32 8#usize) (before after : Rows) (start stop : Slice U32) :=
  after.length = before.length ∧ ∀ i < before.length, bytes after.val[i]!.val =
    runBlock N.val (wv state.val) (bytes before.val[i]!.val) start.val[i]!.val stop.val[i]!.val

theorem residual (N : Usize) (state : Array U32 8#usize) (iv : Array Reg 2#usize)
    (starts ends next : Slice U32) (before tmp : Rows) (k : Nat)
    (hn : N.val ≤ 32) (init : stateWords (packedState iv) = wv state.val)
    (count : before.length = 2) (es : ends.length = 2) (ns : next.length = 2)
    (shared : Shared N iv starts before tmp k)
    (steps : ∀ i < 2, k ≤ ends.val[i]!.val-starts.val[i]!.val)
    (nextStep : ∀ i < 2, next.val[i]!.val = starts.val[i]!.val+k) :
    ChainNiRust.hash.chain_blocks_portable N state tmp next ends ⦃ out => Ended N state before out starts ends ⦄ := by
  obtain ⟨len,h⟩ := shared
  apply WP.spec_mono (chain_blocks_portable_spec N hn state tmp next ends (by omega) (by omega))
  rintro r ⟨lr,hr⟩
  refine ⟨by omega,fun i hi => ?_⟩
  rw [hr i (by omega),h i (by omega),init,nextStep i (by omega),run_split _ _ _ _ _ _ (steps i (by omega))]

theorem already_done (N : Usize) (state : Array U32 8#usize) (iv : Array Reg 2#usize)
    (starts ends : Slice U32) (before tmp : Rows) (k : Nat) (init : stateWords (packedState iv) = wv state.val)
    (count : before.length = 2) (shared : Shared N iv starts before tmp k)
    (steps : ∀ i < 2, k ≤ ends.val[i]!.val-starts.val[i]!.val)
    (done : ∀ i < 2, ends.val[i]!.val ≤ starts.val[i]!.val+k) :
    Ended N state before tmp starts ends := by
  refine ⟨shared.1.trans count.symm,fun i hi => ?_⟩
  have he := done i (by omega)
  have h := shared.2 i (by omega)
  rw [init] at h
  rw [← run_split _ _ _ _ _ _ (steps i (by omega)),runBlock_le _ _ _ _ _ he]
  exact h

end slhdsa.Intel.Chain
