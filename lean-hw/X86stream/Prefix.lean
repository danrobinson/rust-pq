import X86stream.Funs
import X86remainder.Proof
import Streamvector.Groups
open Aeneas Aeneas.Std Result
open ChainAvx2Rust (fullChunks remainder)
namespace slhdsa.X86.Stream

def usesVector256 (b : Slice (Array U8 64#usize)) : Prop :=
  8 ≤ b.length ∧ X86StreamRust.vectorAvailable = true ∧ RcDispatchRust.sha = false

def groupSpec256 (st : Array U32 8#usize) (b : Slice (Array U8 64#usize)) : Prop :=
  X86StreamRust.sha256.stream.prescheduled st (fullChunks 8#usize b) ⦃ out =>
    slhdsa.wv out.val = (fullChunks 8#usize b).val.foldl (fun s g => fold256 s g.val) (slhdsa.wv st.val) ⦄

theorem prefix256 (st : Array U32 8#usize) (b : Slice (Array U8 64#usize))
    (groups : usesVector256 b → groupSpec256 st b) :
    X86StreamRust.sha256.stream.prefix st b ⦃ tail out =>
      fold256 (slhdsa.wv out.val) tail.val = fold256 (slhdsa.wv st.val) b.val ⦄ := by
  unfold X86StreamRust.sha256.stream.prefix
  simp only [X86StreamRust.sha256.stream.FORCE_SOFT,Bool.false_eq_true,ite_false]
  by_cases short : b.len < 8#usize
  · simp [short,step_simps]
  simp only [short,ite_false,X86StreamRust.sha256.stream.available.get,X86StreamRust.sha256.stream.available.get,bind_ok]
  cases avail : X86StreamRust.vectorAvailable with
  | false => simp [step_simps]
  | true =>
    simp only [ite_true]
    simp only [X86StreamRust.sha256.stream.dedicated.get,X86RemainderRust.sha256.stream.dedicated.get,bind_ok]
    cases sha : RcDispatchRust.sha with
    | true => simp [step_simps]
    | false =>
      have selected : usesVector256 b := ⟨by change 8 ≤ b.len.val; scalar_tac,avail,sha⟩
      simp only [Bool.false_eq_true,ite_false,X86StreamRust.core.slice.Slice.as_chunks,ArmStreamRust.core.slice.Slice.as_chunks,
        show (8#usize).val ≠ 0 by decide,bind_tc_eq,bind_ok]
      apply WP.spec_bind (groups selected)
      intro out computed
      apply (WP.spec_ok _).mpr
      change fold256 _ _ = fold256 _ _
      rw [computed]
      unfold fold256
      rw [fold_groups,← List.foldl_append,ChainAvx2Rust.chunk_parts]

def usesVector512 (b : Slice (Array U8 128#usize)) : Prop :=
  8 ≤ b.length ∧ X86StreamRust.vectorAvailable = true

def groupSpec512 (st : Array U64 8#usize) (b : Slice (Array U8 128#usize)) : Prop :=
  X86StreamRust.sha512.stream.prescheduled st (fullChunks 8#usize b) ⦃ out =>
    slhdsa.S512.wv out.val = (fullChunks 8#usize b).val.foldl (fun s g => fold512 s g.val) (slhdsa.S512.wv st.val) ⦄

theorem prefix512 (st : Array U64 8#usize) (b : Slice (Array U8 128#usize))
    (groups : usesVector512 b → groupSpec512 st b) :
    X86StreamRust.sha512.stream.prefix st b ⦃ tail out =>
      fold512 (slhdsa.S512.wv out.val) tail.val = fold512 (slhdsa.S512.wv st.val) b.val ⦄ := by
  unfold X86StreamRust.sha512.stream.prefix
  simp only [X86StreamRust.sha512.stream.FORCE_SOFT,Bool.false_eq_true,ite_false]
  by_cases short : b.len < 8#usize
  · simp [short,step_simps]
  simp only [short,ite_false,X86StreamRust.sha512.stream.available.get,X86StreamRust.sha256.stream.available.get,bind_ok]
  cases avail : X86StreamRust.vectorAvailable with
  | false => simp [step_simps]
  | true =>
    simp only [ite_true]
    have selected : usesVector512 b := ⟨by change 8 ≤ b.len.val; scalar_tac,avail⟩
    simp only [Bool.false_eq_true,ite_false,X86StreamRust.core.slice.Slice.as_chunks,ArmStreamRust.core.slice.Slice.as_chunks,
        show (8#usize).val ≠ 0 by decide,bind_tc_eq,bind_ok]
    apply WP.spec_bind (groups selected)
    intro out computed
    apply (WP.spec_ok _).mpr
    change fold512 _ _ = fold512 _ _
    rw [computed]
    exact prefix_groups512 _ _

end slhdsa.X86.Stream
