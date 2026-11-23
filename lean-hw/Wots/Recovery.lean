import Wots.RecoveryKernel
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots
open WotsRust.sha256.x86.avx512
open Spec.SHA256

private theorem bypass_rows (P : Spec.Params) (N : Usize) (pk : Spec.Bytes) (a : Spec.Adrs)
    (sig : Slice U8) (digits : Slice U32) (original buf : Buffers)
    (init : initialized N digits sig original buf) (available : N.val*digits.length ≤ sig.length)
    (room : digits.length ≤ original.length) :
    rowsSafe N digits.length original buf ∧ ∀ r < digits.length, digits.val[r]!.val=15 →
      rowComplete N (fun i => chainAt P N pk a sig digits i 15) original buf r := by
  refine ⟨⟨init.1,?_⟩,?_⟩
  · intro r hr
    have atR := init.2 r hr
    split at atR
    next copied =>
      obtain ⟨inside,_⟩ := copied
      have fit := Nat.mul_le_mul_left N.val inside
      rw [Nat.mul_succ] at fit
      have len : (element N sig r).length=N.val := by
        change N.val*digits.length ≤ sig.val.length at available
        simp [element]; omega
      refine ⟨?_,fun extra => (Nat.not_le_of_lt inside extra).elim⟩
      unfold rowFrame
      rw [atR]
      exact splice_frame original.val[r]! (element N sig r) N.val len
    next => exact ⟨by simp [rowFrame,atR],fun _ => atR⟩
  · intro r hr digit
    have atR := init.2 r (by omega)
    rw [if_pos ⟨hr,digit⟩] at atR
    unfold rowComplete chainAt
    rw [atR]
    dsimp only
    rw [digit]
    simp only [Nat.sub_self,Spec.chain,List.range_zero,List.foldl_nil,bytes,List.map_append]

/-- Full functional correctness of the extracted Rust AVX-512 WOTS recovery
kernel. Every signature element is advanced from its digit through step 15.
Rows beyond the signature and all bytes outside each endpoint slot are preserved. -/
theorem recover_fips (P : Spec.Params) [Fact (P.family = .sha2)] (N : Usize)
    (pk : Spec.Bytes) (state : Array U32 8#usize) (a : WotsRust.address.Adrs)
    (sig : Slice U8) (digits : Slice U32) (out : Buffers)
    (width : N.val=P.n) (shape : P.n=16 ∨ P.n=24 ∨ P.n=32) (hpk : pk.length=P.n)
    (seed : state.val.map (·.bv) = seedState P.n pk)
    (small : digits.length ≤ 67) (valid : ∀ i < digits.length, digits.val[i]!.val < 16)
    (room : digits.length ≤ out.length) (available : N.val*digits.length ≤ sig.length) :
    recover N state a sig digits out ⦃ final => endpointsInRows N digits
      (fun i => chainAt P N pk (adrsS (WotsRust.addressOf a)) sig digits i 15) out final ⦄ := by
  rw [recover_eq]
  step with preparation_spec N sig digits out (by omega) small valid room available
    as ⟨order,work,buf,ordered,split,prepared⟩
  obtain ⟨safe,bypass⟩ := bypass_rows P N pk (adrsS (WotsRust.addressOf a)) sig digits out buf prepared available room
  apply run_recovery_entry N state a sig digits order work buf (by omega)
  intro base iv pre broadcast words trace
  exact loop_endpoints P N pk (adrsS (WotsRust.addressOf a)) sig digits order work base iv pre out buf width shape hpk
    (by change a.keypair.val < 2^32; scalar_tac) (fun j => (broadcast j).trans seed) words trace small room available
    ordered valid (split.trans (workload_eq digits valid).symm) safe bypass

end slhdsa.X86.Wots
