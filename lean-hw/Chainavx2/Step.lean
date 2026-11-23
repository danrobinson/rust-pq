import Chainavx2.Prefix
import Slhdsa.Proofs.Platform
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Avx2.Chain
open ChainAvx2Rust.sha256.x86.avx2

theorem digest_bytes (regs : EightRegs) (d : DigestWords)
    (cast : ∀ word lane : Fin 8, d.val[word.val]!.val[lane.val]!.bv = regs.val[word.val]! lane) (lane : Fin 8) :
    digestBytes d lane.val 8 = ser (X86.stateWords (laneState regs lane)) := by
  have eq (k : Nat) (hk : k < 8) : d.val[k]!.val[lane.val]!.val = (regs.val[k]! lane).toNat :=
    congrArg BitVec.toNat (cast ⟨k,hk⟩ lane)
  simp (disch := decide) only [digestBytes,eq,ser,X86.stateWords,laneState,List.flatMap_cons,List.flatMap_nil,
    List.nil_append,List.append_nil,List.append_assoc]

theorem step_spec (N off : Usize) (starts : Slice U32) (iv : EightRegs) (lengths : Array U32 8#usize)
    (it : core.ops.range.Range U32) (batch : Batch) (hn : N.val ≤ 32) (hstep : it.start.val < it.end.val)
    (hs : off.val+8 ≤ starts.length)
    (safe : ∀ j < 8, it.start.val < lengths.val[j]!.val → starts.val[off.val+j]!.val+it.start.val ≤ U32.max) :
    chains_loop0_loop1.body N starts iv off lengths it batch ⦃ flow =>
      ∃ next r, flow = cont (next,r) ∧ next.start.val = it.start.val+1 ∧ next.end = it.end ∧
        ∀ j : Fin 8, bytes r.val[j.val]!.val =
          if it.start.val < lengths.val[j.val]!.val then stepBlock N.val (X86.stateWords (laneState iv j))
            (bytes batch.val[j.val]!.val) (starts.val[off.val+j.val]!.val+it.start.val) else bytes batch.val[j.val]!.val ⦄ := by
  unfold chains_loop0_loop1.body
  step with core.iter.range.IteratorRange.next_U32_some_spec it hstep as ⟨o,next,ho,hnext,hend⟩
  simp only [ho]
  step with addresses_spec batch starts off lengths it.start hs safe as ⟨rows,addr⟩
  step with Avx2.compress_block_spec iv rows as ⟨regs,hash⟩
  step with digest_lanes_spec regs as ⟨d,cast⟩
  step with store_bytes_spec N rows lengths it.start d hn as ⟨r,written⟩
  refine ⟨next,r,rfl,hnext,hend,fun j => ?_⟩
  rw [written j.val j.isLt,digest_bytes regs d cast j,hash,addr j.val j.isLt]
  split <;> rfl

end slhdsa.Avx2.Chain
