import Armwide.RecoveryRoutesProgram
import Armwide.WotsRegisterHash
import Armwide.SignLoad
namespace slhdsa.Armwide.Recovery
open Transitions Spec.SHA256
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def route (active steps lane : Nat) : HashTrace :=
  routes[(if active=4 then 6+(steps-1)*4 else active*(active-1)/2)+lane]!

/-- All three tailStep-lane kernels use the common saved address head and each
physical lane's own starting register and counter. The four-lane kernel
increments that counter through its actual 1–15 rounds. -/
private def shape (steps j : Nat) : HashTrace :=
  ⟨j,(List.range steps).map fun t => ⟨4,j,j,t⟩⟩

private theorem checkBulk :
    (List.range 15).all (fun k => (List.range 4).all fun j => route 4 (k+1) j == shape (k+1) j) = true := by decide

private theorem checkTail :
    (List.range 4).all (fun a => (List.range a).all fun j => route a 1 j == shape 1 j) = true := by decide

def registers (n : Nat) (st : List Word) (r : WotsRegisters) (active steps lane : Nat) :=
  let trace := route active steps lane
  trace.calls.foldl (fun v op => hashRegisters n st (r.address op.head) (r.chain op.chain)
    (r.counter op.counter+op.increment) v.1 v.2) (r.digest trace.origin)

theorem registers_fips (p : Spec.Params) [Fact (p.family=.sha2)] (valid : p.Valid)
    (pk : Spec.Bytes) (pkLength : pk.length=p.n) (r : WotsRegisters) (active steps j : Nat)
    (width : active≤4) (live : j<active) (positive : 0<steps) (limit : steps≤15)
    (tailStep : active<4 → steps=1) (chain : r.chain j<65536) :
    content p.n (registers p.n (seedState p.n pk) r active steps j) =
      Spec.chain p (content p.n (r.digest j)) (r.counter j) steps pk {r.address 4 with word2 := r.chain j} := by
  let k : Fin 15 := ⟨steps-1,by omega⟩
  let lane : Fin (lanes (.shared k)) := ⟨j,by change j<4;omega⟩
  have kEq : k.val+1=steps := by dsimp [k];omega
  have physical : route active steps j = hashRoute (.shared k) lane := by
    rw [routed (.shared k) lane]
    change route active steps j = shape (k.val+1) j
    rw [kEq]
    by_cases four : active=4
    · rw [four,←kEq]
      have good := List.all_eq_true.mp (List.all_eq_true.mp checkBulk k.val (List.mem_range.mpr k.isLt)) j (List.mem_range.mpr lane.isLt)
      simpa using good
    · rw [tailStep (by omega)]
      have good := List.all_eq_true.mp (List.all_eq_true.mp checkTail active (List.mem_range.mpr (by omega))) j (List.mem_range.mpr live)
      simpa using good
  unfold registers
  rw [physical]
  trans content p.n (runRegisterHashes p.n (seedState p.n pk) r (.shared k) lane)
  · rfl'
  · simpa only [kEq] using (native_shared_chain p valid pk pkLength r k lane chain)

end slhdsa.Armwide.Recovery
