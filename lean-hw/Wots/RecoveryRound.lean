import Wots.RecoveryLanes
import Wots.Driver
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Wots
open Spec.SHA256

/-- Every survivor contains its next partial chain. Every lane retired this
round writes its own FIPS endpoint into its destination slot. -/
theorem cycle_chains (P : Spec.Params) [Fact (P.family=.sha2)] (N : Usize)
    (pk : Spec.Bytes) (a : Spec.Adrs) (sig : Slice U8) (digits : Slice U32)
    (iv pre h : Hash) (w : Words) (ix st : LaneArray) (idx c : Reg) (m : U16) (pos : Usize)
    (order : Order) (owner : Fin 16 → Option Nat) (out : Buffers)
    (width : N.val=P.n) (shape : P.n=16 ∨ P.n=24 ∨ P.n=32) (hpk : pk.length=P.n)
    (seed : ∀ j, stateWords (laneState iv j)=seedState P.n pk)
    (prefixOK : Trace pre (fun j => schedule (recoveryBlock N w h c j)) (laneState iv) 4)
    (owned : owns order ix m pos.val owner)
    (ordered : ∀ i < digits.length, order.val[rank digits.val i]!.val = i)
    (bound : pos.val ≤ digits.length) (small : digits.length ≤ 67) (rows : digits.length ≤ out.length)
    (before : laneStateOK P N pk a sig digits ix m c h w) :
    cycle N iv pre (fun _ => 0xffff) out ix st idx c m pos h w ⦃ flow =>
      ∃ packed digest after survivors buf, flow = cont (buf,packed,ix,st,idx,after,survivors,pos,digest) ∧
        (∀ j, after j = c j+1) ∧
        (∀ j, enabled survivors j = true ↔ enabled m j = true ∧ after j ≠ 15) ∧
        laneStateOK P N pk a sig digits ix survivors after digest packed ∧
        ∃ staged : Staged N, retired ix staged out buf (finishes m c) ∧
          ∀ j, finishes m c j → bytes (staged.val[j.val]!.val) = chainAt P N pk a sig digits (chainIndex ix j) 15 ⦄ := by
  unfold cycle
  have shapes : N.val=16 ∨ N.val=24 ∨ N.val=32 := width ▸ shape
  have both := WP.spec_and (compress_round_spec N iv pre h w c shapes prefixOK)
    (advance_chain P N pk a sig digits iv pre h w c width shape hpk seed prefixOK)
  apply WP.spec_bind both
  rintro ⟨packed,digest⟩ ⟨⟨words,_⟩,chain⟩
  step with finish_owned owned ordered bound small N c digest out shapes rows
    as ⟨after,survivors,buf,inc,bits,_,staged,writes,stagedBytes⟩
  have live (j) (on : enabled m j = true) :
      let i := chainIndex ix j
      i < digits.length ∧ digits.val[i]!.val ≤ (after j).toNat ∧ (after j).toNat ≤ 15 ∧
      laneValue digest j N.val = chainAt P N pk a sig digits i (after j).toNat := by
    obtain ⟨_,ready,active⟩ := before j
    obtain ⟨valid,lo,hi,old⟩ := active on
    have add : (after j).toNat = (c j).toNat+1 := by
      rw [inc,BitVec.toNat_add]; change (_+1)%(2^32) = _; apply Nat.mod_eq_of_lt; omega
    rw [add]
    exact ⟨valid,by omega,by omega,chain j _ lo hi old (by simpa only [addressReady,← width] using ready)⟩
  refine ⟨packed,digest,after,survivors,buf,rfl,inc,bits,?_,staged,writes,?_⟩
  · intro j
    have old := before j
    refine ⟨old.1,address_after_hash w packed h c j N.val a _ shapes old.2.1 (fun k hk => words k hk j),?_⟩
    intro on
    obtain ⟨prev,ne⟩ := (bits j).mp on
    obtain ⟨valid,lo,hi,correct⟩ := live j prev
    have not15 : (after j).toNat ≠ 15 := fun eq => ne (BitVec.eq_of_toNat_eq (by simpa using eq))
    change (after j).toNat ≤ 15 at hi
    exact ⟨valid,lo,by omega,correct⟩
  · intro j done
    obtain ⟨_,_,_,correct⟩ := live j done.1
    have eq : after j=15 := (inc j).trans done.2
    rw [eq] at correct
    change laneValue digest j N.val = chainAt P N pk a sig digits (chainIndex ix j) 15 at correct
    rw [← correct]
    apply List.ext_getElem
    · simp [laneValue,ser_length,stateWords,laneState]; omega
    · intro k hk hk'
      have lt : k < N.val := by simpa using hk
      rw [← getElem!_pos (bytes (staged.val[j.val]!.val)) k hk,← getElem!_pos (laneValue digest j N.val) k hk']
      unfold laneValue
      rw [← digest_byte_eq digest j k N.val lt (by omega)]
      simpa [bytes,getElem!_pos,lt] using stagedBytes j done k lt

end slhdsa.X86.Wots
