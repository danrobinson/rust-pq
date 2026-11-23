import Leaf256.Funs
import Digest256.Block
import Slhdsa.Proofs.Hash
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Leaf
open LeafRust.sha256.x86.avx512

def addressOf (a : LeafRust.address.Adrs) : address.Adrs := ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩

theorem short_block (a : LeafRust.address.Adrs) (s : Slice U8) (h : s.length ≤ 33) :
    LeafRust.hash.short_block a s ⦃ b => bytes b.val = padFrom 64 ((adrsS (addressOf a)).compress ++ bytes s.val) ⦄ :=
  short_block_spec (addressOf a) s h

private theorem signed_word (a : Array U8 4#usize) :
    (core.num.I32.from_be_bytes a).bv = a.val[0]!.bv ++ a.val[1]!.bv ++ a.val[2]!.bv ++ a.val[3]!.bv := by
  let words := [a.val[0]!,a.val[1]!,a.val[2]!,a.val[3]!]
  have eq : a = Array.make 4#usize words (by rfl) := by
    apply Aeneas.Std.Array.ext
    apply List.ext_getElem
    · simp [words]
    · intro i hi _
      have h : i < 4 := by simpa using hi
      interval_cases i <;> simp [words,getElem!_pos]
  calc
    _ = (core.num.I32.from_be_bytes (Array.make 4#usize words (by rfl))).bv := congrArg (fun x => (core.num.I32.from_be_bytes x).bv) eq
    _ = _ := Avx2.be_four _ _ _ _

theorem read_word (N : Usize) (b : Array U8 64#usize) (i : Usize) (hi : i.val < 16) :
    fors_leaves.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i.call_mut (N := N) b i ⦃ v b' =>
      (∀ j : Fin 16, v j = Spec.SHA256.word (bytes b.val) (4*i.val)) ∧ b' = b ⦄ := by
  unfold fors_leaves.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i.call_mut
  simp only [core.core_arch.x86.avx512f._mm512_set1_epi32, lift, bind_ok]
  step*
  all_goals try scalar_tac
  · cases r <;> simp_all
  · rename_i converted
    intro j
    subst r
    simp only at converted
    rw [signed_word]
    simp only [Spec.SHA256.word]
    repeat rw [bytes_getElem! _ _ (by scalar_tac)]
    simp only [converted.1,s_post,Array.val_to_slice,i_post,i1_post]
    simp (disch := scalar_tac) only [List.getElem!_slice,Nat.add_zero,← getElem!_pos]

theorem initial_spec (N : Usize) (st : Array U32 8#usize) :
    core.array.Array.map (fors_leaves.closure_1.Insts.CoreOpsFunctionFnMutTupleU32__m512i N) st ()
      ⦃ a => ∀ i, i < 8 → ∀ j : Fin 16, a.val[i]! j = st.val[i]!.bv ⦄ := by
  unfold core.array.Array.map
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 8#usize _ () (fun i v => ∀ j : Fin 16, v j = st.val[i]!.bv) ?_)
  · intro a h i hi j; simpa only [Array.getElem!_Nat_eq] using h i hi j
  intro i hi
  simp only [fors_leaves.closure_1.Insts.CoreOpsFunctionFnMutTupleU32__m512i,
    fors_leaves.closure_1.Insts.CoreOpsFunctionFnMutTupleU32__m512i.call_mut, lift, bind_ok,
    core.core_arch.x86.avx512f._mm512_set1_epi32]
  step*
  simp_all [step_simps, ← getElem!_pos]

theorem initial_words (a : Array Reg 8#usize) (st : Array U32 8#usize)
    (ha : ∀ i, i < 8 → ∀ j : Fin 16, a.val[i]! j = st.val[i]!.bv) (j : Fin 16) :
    stateWords (laneState a j) = st.val.map (·.bv) := by
  simp (disch := decide) only [laneState, stateWords, ha]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi8 : i < 8 := by simpa using hj
    rw [List.getElem_map]
    interval_cases i <;> simp [getElem!_pos]


theorem words_spec (N : Usize) (b : Array U8 64#usize) :
    core.array.from_fn 16#usize (fors_leaves.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i N) b
      ⦃ w => ∀ k, k < 16 → ∀ j : Fin 16, w.val[k]! j = Spec.SHA256.word (bytes b.val) (4*k) ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 16#usize (fors_leaves.closure.Insts.CoreOpsFunctionFnMutTupleUsize__m512i N) b
    (fun k v => ∀ j : Fin 16, v j = Spec.SHA256.word (bytes b.val) (4*k))
    (fun k hk => read_word N b k hk))
  intro a ha k hk j
  simpa only [Array.getElem!_Nat_eq] using ha k hk j

end slhdsa.X86.Leaf
