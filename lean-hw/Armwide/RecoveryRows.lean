import Armwide.RecoveryProgram
import Armwide.RecoveryPre
namespace slhdsa.Armwide.Recovery
open WotsRefill Transitions Spec.SHA256

def ends (p : Spec.Params) (pk : Spec.Bytes) (a : Spec.Adrs) (sig : Nat → Spec.Bytes) (d : Nat → Nat) (i : Nat) :=
  Spec.chain p (sig i) (d i) (15-d i) pk {a with word2:=i}

theorem frame_congr (n count : Nat) (x y : Nat → Spec.Bytes) (agree : ∀ i<count, x i=y i) :
    frame n count x=frame n count y := by
  unfold frame encode
  congr 2
  apply List.map_congr_left
  intro i mem; exact agree i (List.mem_range.mp mem)

theorem complete_fips (p : Spec.Params) [Fact (p.family=.sha2)] (valid : p.Valid) (pk : Spec.Bytes)
    (pkLength : pk.length=p.n) (a : Spec.Adrs) (sig : Nat → Spec.Bytes) (d : Nat → Nat) (ord : List Nat)
    (count : Nat) (cap : count≤67) (sizes : ∀ c<count,(sig c).length=p.n) (digits : ∀ c<count,d c≤15)
    (unique : ord.Nodup) (members : ∀ c,c∈ord ↔ c<count ∧ d c<15) (buf : Spec.Bytes)
    (initial : buf=frame p.n count (fun c => if d c=15 then sig c else [])) :
    completeRows p.n (seedState p.n pk) a sig d ord buf =
      Keygen.filled p.n ((List.range count).flatMap (ends p pk a sig d)) := by
  rw [initial]
  unfold completeRows
  let ls := (ord.take 4).map (fresh sig d)
  let queue := ord.drop 4
  have active : ∀ l∈ls, Good p.n count l := by
    intro l mem
    obtain ⟨c,fromList,rfl⟩ := List.mem_map.mp (show l∈(ord.take 4).map (fresh sig d) from mem)
    have h := (members c).1 (List.mem_of_mem_take fromList)
    exact ⟨h.1,sizes c h.1,by dsimp [fresh];omega,by dsimp [fresh];omega⟩
  have waiting (c) (mem : c∈queue) := (members c).1 (List.mem_of_mem_drop mem)
  have result := run_sim (writeAt p.n) (frame p.n count) p valid pk pkLength a sig d count cap
    (write_frame p.n count) sizes ls queue (fun c => if d c=15 then sig c else []) (recoverMeasure ls queue+1) (by simp [ls]) active waiting
  rw [result]
  change frame p.n count (recoverFull p pk a sig d ord)=_
  rw [frame_congr p.n count _ (ends p pk a sig d) (recover_scheduler_eq_fips p pk a sig d count ord digits unique members)]
  unfold frame
  rw [encode_done p.n count (ends p pk a sig d) (fun c h => Spec.chain_length p valid _ (sizes c h) ..)]

end slhdsa.Armwide.Recovery
