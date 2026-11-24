import Wots.Progress
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Wots
open WotsRust.sha256.x86.avx512
open Spec.SHA256

def samePrefix (base w : Words) := ∀ k < 4, ∀ j : Fin 16, w.val[k]! j = base.val[k]! j
def validCounters (m : U16) (c : Reg) := ∀ j, enabled m j = true → (c j).toNat < 15

theorem packed_prefix (w h : Nat → Word) (n : Nat) (t : Word) (k : Nat) (lt : k < 4) :
    packedWord w h n t k = w k := by
  simp (disch := omega) only [packedWord,Chain.valueWord,if_neg]

theorem recovery_prefix {base w : Words} (N : Usize) (h : Hash) (counter : Reg)
    (iv pre : Hash) (same : samePrefix base w)
    (initial : Trace pre (fun j => Spec.SHA256.schedule (Leaf.blockOf (chainWords base j))) (laneState iv) 4) :
    Trace pre (fun j => Spec.SHA256.schedule (recoveryBlock N w h counter j)) (laneState iv) 4 := by
  apply Leaf.transfer_prefix (by decide) _ initial
  intro j i hi
  rw [recoveryBlock,Leaf.word_blockOf _ _ (by omega),Leaf.word_blockOf _ _ (by omega),packed_prefix _ _ _ _ _ hi]
  exact (same i hi j).symm

private theorem old_live {digits order ix st active pos ix' st' mask next assigned}
    (fill : mapped digits order ix st active pos (ix',st',mask,next,assigned))
    (j : Fin 16) (off : enabled assigned j = false) : enabled mask j = enabled active j := by
  obtain ⟨job,_,_,lanes⟩ := fill
  have hj := lanes j
  cases e : job j with
  | none => rw [e] at hj; exact hj.2.1
  | some q => rw [e] at hj; have := hj.2.2.2.1; simp_all

def loopSafe (base : Words) (order : Order) (work : Usize) (rows : Nat) (s : RecoveryState) :=
  let (buf,w,ix,_,_,counter,active,pos,_) := s
  buf.length = rows ∧ samePrefix base w ∧ validCounters active counter ∧ pos.val ≤ work.val ∧
    ∃ owner, owns order ix active pos.val owner

def loopWork (work : Usize) (s : RecoveryState) :=
  let (_,_,_,_,_,counter,active,pos,_) := s
  remainingWork work pos active counter

set_option maxHeartbeats 1500000 in
/-- Total correctness for the scheduler's control flow and buffer length, starting
with its real empty lane mask. The loop measure covers partial and full refills. -/
theorem recovery_terminates (N : Usize) (zero : Reg) (sig : Slice U8) (digits : Slice U32)
    (order : Order) (work : Usize) (base : Words) (iv pre hash : Hash) (out : Buffers)
    (ix st : LaneArray) (idx counter : Reg)
    (shape : N.val=16 ∨ N.val=24 ∨ N.val=32) (small : digits.length ≤ 67)
    (available : N.val*digits.length ≤ sig.length) (rows : digits.length ≤ out.length)
    (ordered : ∀ i < digits.length, order.val[rank digits.val i]!.val = i)
    (valid : ∀ i < digits.length, digits.val[i]!.val < 16)
    (workload : work.val = digits.length-frequency digits.val 15)
    (initial : Trace pre (fun j => Spec.SHA256.schedule (Leaf.blockOf (chainWords base j))) (laneState iv) 4) :
    recover_loop5 N zero sig digits out order work base iv pre (fun _ => 0xffff) Store.control
      ix st idx counter 0#u16 0#usize hash ⦃ buf => buf.length = out.length ⦄ := by
  unfold recover_loop5
  apply loop.spec_decr_nat (measure := loopWork work) (inv := loopSafe base order work out.length)
  · rintro ⟨buf,w,indices,starts,id,c,m,p,h⟩ ⟨len,same,counts,cap,owner,owns0⟩
    change recover_loop5.body N zero sig digits order work iv pre _ _ buf w indices starts id c m p h ⦃ _ ⦄
    rw [cycle_body_eq]
    split
    next guard =>
      unfold iteration
      have queued (q) (lt : q < work.val) := (order_at digits order ordered q (by omega)).1
      step with refill_spec digits order work indices starts m p cap (by omega) queued
        as ⟨state,fill,le,stop⟩
      obtain ⟨ix',st',mask,next,assigned⟩ := state
      dsimp only at le stop
      obtain ⟨owner',owns1,_,_⟩ := refill_owns owns0 fill
      have round (loaded id' : Reg) (hash' : Hash) (w' : Words) (pres : samePrefix base w')
          (live : validCounters mask loaded) (keep : assigned=0#u16 → loaded=c) :
          cycle N iv pre (fun _ => 0xffff) buf ix' st' id' loaded mask next hash' w' ⦃ flow =>
            match flow with
            | done b => b.length = out.length
            | cont s => loopSafe base order work out.length s ∧ loopWork work s < remainingWork work p m c ⦄ := by
        unfold cycle
        step with compress_round_spec N iv pre hash' w' loaded shape (recovery_prefix N hash' loaded iv pre pres initial)
          as ⟨packed,digest,words,_⟩
        step with finish_owned owns1 ordered (by omega) small N loaded digest buf shape (by omega)
          as ⟨after,survive,b,inc,bits,ownership,staged,writes,_⟩
        refine ⟨⟨writes.1.trans len,?_,?_,le,_,ownership⟩,
          recovery_descent fill work le stop guard c loaded after survive keep counts inc bits⟩
        · intro k hk j
          rw [words k (by omega) j,packed_prefix _ _ _ _ _ hk,pres k hk j]
        · intro j on
          obtain ⟨on',ne⟩ := (bits j).mp on
          have lt := live j on'
          have add : (after j).toNat = (loaded j).toNat+1 := by
            rw [inc,BitVec.toNat_add]; change (_+1)%(2^32) = _
            apply Nat.mod_eq_of_lt; omega
          have not15 : (after j).toNat ≠ 15 := fun e =>
            ne (BitVec.eq_of_toNat_eq (by simpa using e))
          omega
      by_cases nz : assigned ≠ 0#u16
      · rw [if_pos (bne_iff_ne.mpr nz)]
        step with refill_load_spec fill (fun q lt => queued q (by omega)) nz small N c zero sig h w shape available
          as ⟨state,loads,patch⟩
        obtain ⟨id',loaded,hash',w'⟩ := state
        dsimp only at loads patch
        refine WP.spec_mono (round loaded id' hash' w' ?_ ?_ (fun e => (nz e).elim)) ?_
        · intro k hk j
          rw [patch k (by omega) j,if_neg (by omega),same k hk j]
        · intro j on
          have l := loads j
          cases e : enabled assigned j with
          | true =>
            simp only [e,ite_true] at l
            obtain ⟨q,_,hi,_,digit,_⟩ := l
            have part := order_partition digits order valid ordered q (by omega)
            have short := part.2.1.mp (by omega)
            rw [digit]; exact short
          | false =>
            simp only [e,Bool.false_eq_true,ite_false] at l
            rw [l.1]
            exact counts j ((old_live fill j e).symm.trans on)
        · intro flow post; cases flow <;> exact post
      · rw [if_neg (fun b => nz (bne_iff_ne.mp b))]
        refine WP.spec_mono (round c id h w same ?_ (fun _ => rfl)) ?_
        · intro j on
          have off : enabled assigned j = false := by simp [Classical.not_not.mp nz,enabled]
          exact counts j ((old_live fill j off).symm.trans on)
        · intro flow post; cases flow <;> exact post
    next => exact (show _ from by simpa only [step_simps] using len)
  · refine ⟨rfl,fun _ _ _ => rfl,?_,by simp,fun _ => none,?_,?_⟩
    · simp [validCounters,enabled]
    · simp
    · simp [enabled]

end slhdsa.X86.Wots
