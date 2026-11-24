import Chainavx2.Funs
open Aeneas Aeneas.Std Result
namespace slhdsa.Avx2.Chain
open ChainAvx2Rust.sha256.x86.avx2

theorem broadcast_spec (N : Usize) (st : Array U32 8#usize) :
    core.array.Array.map (chains.closure.Insts.CoreOpsFunctionFnMutTupleU32__m256i N) st ()
      ⦃ a => ∀ i, i < 8 → ∀ lane : Fin 8, a.val[i]! lane = st.val[i]!.bv ⦄ := by
  unfold core.array.Array.map
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! 8#usize _ ()
    (fun i v => ∀ lane : Fin 8, v lane = st.val[i]!.bv) ?_)
  · intro a h i hi lane; simpa only [Array.getElem!_Nat_eq] using h i hi lane
  intro i hi
  simp only [chains.closure.Insts.CoreOpsFunctionFnMutTupleU32__m256i.call_mut,lift,bind_ok,
    core.core_arch.x86.avx._mm256_set1_epi32]
  step*
  simp_all [step_simps,← getElem!_pos]

abbrev EightRegs := Array core.core_arch.x86.__m256i 8#usize

abbrev EightWords := Array U32 8#usize
abbrev DigestWords := Array EightWords 8#usize

theorem digest_lanes_spec (regs : EightRegs) :
    core.intrinsics.transmute DigestWords regs ⦃ digest =>
      ∀ word lane : Fin 8, digest.val[word.val]!.val[lane.val]!.bv = regs.val[word.val]! lane ⦄ := by
  simp only [core.intrinsics.transmute,step_simps]
  intro word lane
  simp (disch := simp [word.isLt,lane.isLt]) only [LaneRepr.castBits,ChainAvx2Rust.nativeLanes,
    Array.from_val,getElem!_pos,List.getElem_ofFn]
end slhdsa.Avx2.Chain
