import Chainwide.Output
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Chain

def SavedWords (N : Usize) (orig finished : U16) (old hash result : Hash) :=
  ∀ k, k < N.val/4 → ∀ j : Fin 16, orig.bv.getLsbD j.val →
    result.val[k]! j = if finished.bv.getLsbD j.val then hash.val[k]! j else old.val[k]! j

def NextWords (N : Usize) (w : Array Reg 16#usize) (hash : Hash) (out : Array Reg 16#usize) :=
  ∀ k, k < 16 → ∀ j : Fin 16, out.val[k]! j =
    valueWord (fun i => w.val[i]! j) (fun i => hash.val[i]! j) N.val k

def Retired (N : Usize) (ends : Slice U32) (off : Usize) (batch : Rows)
    (start stop : Reg) (t : Nat) (orig finished : U16) (saved hash : Hash) (w : Array Reg 16#usize)
    (flow : ControlFlow (Reg × U16 × Hash × Array Reg 16#usize) Rows) :=
  match flow with
  | done out => (∀ j, ¬ Live start stop (t+1) j) ∧ ∃ finalHash,
      SavedWords N orig finished saved hash finalHash ∧ Rendered N ends off orig finalHash batch out
  | cont (next,active,kept,out) => active ≠ 0#u16 ∧ Schedule start stop next active (t+1) ∧
      SavedWords N orig finished saved hash kept ∧ NextWords N w hash out

theorem retire_spec (N : Usize) (ends : Slice U32) (off : Usize) (batch : Rows)
    (start stop next : Reg) (t : Nat) (orig active finished : U16)
    (saved hash : Hash) (words : Array Reg 16#usize) (hn : N.val=16 ∨ N.val=24 ∨ N.val=32)
    (he : off.val+batch.length ≤ ends.length) (hb : Covers orig batch.length)
    (positive : ∀ k, orig.bv.getLsbD k → 0 < ends.val[off.val+k]!.val)
    (nonempty : active ≠ 0#u16)
    (origMask : ∀ j : Fin 16, orig.bv.getLsbD j.val = decide (Live start stop 0 j))
    (last : ∀ j : Fin 16, finished.bv.getLsbD j.val =
      decide (Live start stop t j ∧ (start j).toNat+t+1 = (stop j).toNat))
    (schedule : Schedule start stop next (active &&& ~~~finished) (t+1)) :
    retire N ends off batch orig (fun _ => 0xffff) next active finished saved words hash
      ⦃ flow => Retired N ends off batch start stop t orig finished saved hash words flow ⦄ := by
  unfold retire
  by_cases f : finished = 0#u16
  · subst finished
    simp only [bne_self_eq_false,Bool.false_eq_true,ite_false]
    step with value_spec N words hash hn as ⟨out,hout⟩
    refine ⟨nonempty,?_,?_,hout⟩
    · have nochange : (active &&& ~~~(0#u16)) = active := by
        apply U16.bv_eq_imp_eq; change active.bv &&& ~~~(0 : BitVec 16) = _; simp
      rwa [nochange] at schedule
    · intro k hk j hj; simp
  · simp only [bne_iff_ne,ite_cond_eq_true]
    rw [if_pos f]
    by_cases all : finished = orig
    · rw [if_pos all,all]
      step with flush_spec N ends off batch orig hash (by omega) he hb positive as ⟨flow,out,eq,rows⟩
      subst flow
      refine ⟨all_finished _ _ _ _ _ origMask last all,hash,?_,rows⟩
      intro k hk j hj
      simp [hj]
    · rw [if_neg all]
      step with saved_spec N saved hash finished (by omega) as ⟨kept,hk⟩
      have savedOk : SavedWords N orig finished saved hash kept := by
        intro k h j _
        simpa [h] using hk k (by omega) j
      simp only [lift,bind_ok]
      split <;> rename_i empty
      · step with flush_spec N ends off batch orig kept (by omega) he hb positive as ⟨flow,out,eq,rows⟩
        subst flow
        refine ⟨?_,kept,savedOk,rows⟩
        intro j live
        have set := schedule.1 j
        rw [empty,decide_eq_true live] at set
        simpa using set
      · step with value_spec N words hash hn as ⟨out,hw⟩
        exact ⟨empty,schedule,savedOk,hw⟩

/-- A production iteration compresses the addressed blocks, removes exactly the lanes
whose intervals end here, and either writes their final digests or advances the surviving words. -/
theorem iteration_spec (N : Usize) (ends : Slice U32) (iv : Hash) (off : Usize) (batch : Rows)
    (start stop : Reg) (orig : U16) (fixed : Reg) (pre : Hash) (current : Reg)
    (active : U16) (saved : Hash) (words : Array Reg 16#usize) (t : Nat)
    (blocks : Fin 16 → Spec.Bytes) (hn : N.val=16 ∨ N.val=24 ∨ N.val=32)
    (he : off.val+batch.length ≤ ends.length) (hb : Covers orig batch.length)
    (positive : ∀ k, orig.bv.getLsbD k → 0 < ends.val[off.val+k]!.val)
    (work : active ≠ 0#u16) (sched : Schedule start stop current active t)
    (initial : ∀ j : Fin 16, orig.bv.getLsbD j.val = decide (Live start stop 0 j))
    (trace : Trace pre (fun j => Spec.SHA256.schedule (blocks j)) (laneState iv) 4)
    (message : ∀ k, k < 16 → ∀ j, addressWord (fun i => words.val[i]! j) (fixed j) (current j) k =
      Spec.SHA256.word (blocks j) (4*k)) :
    ChainWideRust.sha256.x86.avx512.chains_loop0_loop1.body N ends iv off batch stop orig fixed
      (fun _ => 0xffff) pre current active saved words ⦃ flow =>
        ∃ w hash finished,
          (∀ k, k < 16 → ∀ j, w.val[k]! j = Spec.SHA256.word (blocks j) (4*k)) ∧
          (∀ j, stateWords (laneState hash j) = Spec.SHA256.compress (stateWords (laneState iv j)) (blocks j)) ∧
          (∀ j : Fin 16, finished.bv.getLsbD j.val =
            decide (Live start stop t j ∧ (start j).toNat+t+1 = (stop j).toNat)) ∧
          Retired N ends off batch start stop t orig finished saved hash w flow ⦄ := by
  apply compression_step_spec _ _ _ _ _ _ _ _ _ _ _ _ _ blocks _ trace message
  intro w hash hw hh
  unfold finishStep
  step with advance_spec start stop current active t sched as ⟨next,finished,last,hs⟩
  apply WP.spec_mono (retire_spec N ends off batch start stop next t orig active finished saved hash w
    hn he hb positive work initial last hs)
  intro flow h
  exact ⟨w,hash,finished,hw,hh,last,h⟩

end slhdsa.X86.Chain
