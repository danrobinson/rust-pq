import Streamstep.Proof
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Stream
set_option maxHeartbeats 2000000

def slots256 (w : Array U32 16#usize) (i : Nat) := w.val[i]!.bv

theorem step256 (I : Usize) (v : Array U32 8#usize) (w : Array U32 16#usize) (block : Spec.Bytes)
    (bound : I.val < 64) (old : window (slots256 w) (Spec.SHA256.schedule block) I.val) :
    StreamStepRust.sha256.stream.scalar_step I v w ⦃ out next =>
      state256 out = Spec.SHA256.round (Spec.SHA256.schedule block) (state256 v) I.val ∧
      window (slots256 next) (Spec.SHA256.schedule block) (I.val+1) ⦄ := by
  have key : StreamStepRust.sha256.K.val[I.val]!.bv = Spec.SHA256.K[I.val]! := by
    have same : StreamStepRust.sha256.K = slhdsa.sha256.K := by unfold StreamStepRust.sha256.K slhdsa.sha256.K; rfl
    rw [same,← slhdsa.K_eq,slhdsa.wv_getElem! _ _ (by simpa using bound),getElem!_pos _ _ (by simpa using bound)]
  unfold StreamStepRust.sha256.stream.scalar_step
  by_cases late : 16#usize ≤ I
  · simp only [late,ite_true]
    step*
    have expanded : x.bv = (Spec.SHA256.schedule block)[I.val]! := by
      rw [← expansion256 _ _ _ old (by scalar_tac) bound]
      simp (disch := scalar_tac) [slots256,Spec.SHA256.ssig0,Spec.SHA256.ssig1,getElem!_pos, *]
    obtain ⟨next,word⟩ := updated_window (next := slots256 w1) old (by scalar_tac) (by
      intro k hk
      obtain ⟨idx,hidx,write⟩ : ∃ idx : Usize, idx.val = I.val%16 ∧ w1 = w.set idx x :=
        ⟨_,by assumption,w1_post⟩
      by_cases same : I.val%16=k <;>
        simp (disch := scalar_tac) [slots256,write,List.getElem_set,getElem!_pos,hidx,same,expanded])
    have wk : i3.bv = Spec.SHA256.K[I.val]! + (Spec.SHA256.schedule block)[I.val]! := by
      rw [← word,← key,BitVec.add_comm]
      simp (disch := scalar_tac) [slots256,i3_post,i1_post,i2_post,i_post,getElem!_pos]
    step with round256_spec v i3 _ _ wk
    exact ⟨by assumption,next⟩
  · simp only [late,ite_false,bind_ok]
    step*
    obtain ⟨next,word⟩ := unchanged_window old (by scalar_tac)
    have wk : i3.bv = Spec.SHA256.K[I.val]! + (Spec.SHA256.schedule block)[I.val]! := by
      rw [← word,← key,BitVec.add_comm]
      simp (disch := scalar_tac) [slots256,i3_post,i1_post,i2_post,i_post,getElem!_pos]
    step with round256_spec v i3 _ _ wk
    exact ⟨by assumption,next⟩

def slots512 (w : Array U64 16#usize) (i : Nat) := w.val[i]!.bv

theorem step512 (I : Usize) (v : Array U64 8#usize) (w : Array U64 16#usize) (block : Spec.Bytes)
    (bound : I.val < 80) (old : window (slots512 w) (Spec.SHA512.schedule block) I.val) :
    StreamStepRust.sha512.stream.scalar_step I v w ⦃ out next =>
      state512 out = Spec.SHA512.round (Spec.SHA512.schedule block) (state512 v) I.val ∧
      window (slots512 next) (Spec.SHA512.schedule block) (I.val+1) ⦄ := by
  have key : StreamStepRust.sha512.K.val[I.val]!.bv = Spec.SHA512.K[I.val]! := by
    have same : StreamStepRust.sha512.K = slhdsa.sha512.K := by unfold StreamStepRust.sha512.K slhdsa.sha512.K; rfl
    rw [same,← slhdsa.S512.K_eq,slhdsa.S512.wv_getElem! _ _ (by simpa using bound),getElem!_pos _ _ (by simpa using bound)]
  unfold StreamStepRust.sha512.stream.scalar_step
  by_cases late : 16#usize ≤ I
  · simp only [late,ite_true]
    step*
    have expanded : x.bv = (Spec.SHA512.schedule block)[I.val]! := by
      rw [← expansion512 _ _ _ old (by scalar_tac) bound]
      simp (disch := scalar_tac) [slots512,Spec.SHA512.ssig0,Spec.SHA512.ssig1,getElem!_pos, *]
    obtain ⟨next,word⟩ := updated_window (next := slots512 w1) old (by scalar_tac) (by
      intro k hk
      obtain ⟨idx,hidx,write⟩ : ∃ idx : Usize, idx.val = I.val%16 ∧ w1 = w.set idx x :=
        ⟨_,by assumption,w1_post⟩
      by_cases same : I.val%16=k <;>
        simp (disch := scalar_tac) [slots512,write,List.getElem_set,getElem!_pos,hidx,same,expanded])
    have wk : i3.bv = Spec.SHA512.K[I.val]! + (Spec.SHA512.schedule block)[I.val]! := by
      rw [← word,← key,BitVec.add_comm]
      simp (disch := scalar_tac) [slots512,i3_post,i1_post,i2_post,i_post,getElem!_pos]
    step with round512_spec v i3 _ _ wk
    exact ⟨by assumption,next⟩
  · simp only [late,ite_false,bind_ok]
    step*
    obtain ⟨next,word⟩ := unchanged_window old (by scalar_tac)
    have wk : i3.bv = Spec.SHA512.K[I.val]! + (Spec.SHA512.schedule block)[I.val]! := by
      rw [← word,← key,BitVec.add_comm]
      simp (disch := scalar_tac) [slots512,i3_post,i1_post,i2_post,i_post,getElem!_pos]
    step with round512_spec v i3 _ _ wk
    exact ⟨by assumption,next⟩

end slhdsa.X86.Stream
