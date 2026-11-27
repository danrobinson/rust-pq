import Parallel.KeygenTickets
import Cachepath.WotsRows
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelKeygenPlan

namespace Arm
def slh.parallel.proof_keygen_plan
  (p : params.Params) (threads : Std.Usize) :
  Result (Option (Std.U32 × Std.Usize × Std.Usize))
  := do
  if threads < 2#usize
  then ok none
  else
    if p.hp < 3#u32
    then ok none
    else
      let sub_h ←
        if p.hp >= 9#u32
        then ok 3#u32
        else if p.hp >= 6#u32
             then ok 2#u32
             else ok 0#u32
      let split ← p.hp - sub_h
      let count ← 1#usize <<< split
      let i ← lift (core.cmp.impls.OrdUsize.min threads count)
      ok (some (sub_h, count, i))
end Arm
namespace X86
def slh.parallel.proof_keygen_plan
  (p : params.Params) (threads : Std.Usize) :
  Result (Option (Std.U32 × Std.Usize × Std.Usize))
  := do
  if threads < 2#usize
  then ok none
  else
    if p.hp < 3#u32
    then ok none
    else
      let sub_h ←
        if p.hp >= 8#u32
        then ok 3#u32
        else if p.hp >= 6#u32
             then ok 2#u32
             else ok 0#u32
      let split ← p.hp - sub_h
      let count ← 1#usize <<< split
      let i ← lift (core.cmp.impls.OrdUsize.min threads count)
      ok (some (sub_h, count, i))
end X86

private def policy (threshold : U32)
  (p : params.Params) (threads : Std.Usize) :
  Result (Option (Std.U32 × Std.Usize × Std.Usize))
  := do
  if threads < 2#usize
  then ok none
  else
    if p.hp < 3#u32
    then ok none
    else
      let sub_h ←
        if p.hp >= threshold
        then ok 3#u32
        else if p.hp >= 6#u32
             then ok 2#u32
             else ok 0#u32
      let split ← p.hp - sub_h
      let count ← 1#usize <<< split
      let i ← lift (core.cmp.impls.OrdUsize.min threads count)
      ok (some (sub_h, count, i))

def value (x86 : Bool) (p : params.Params) (threads : Usize) : Option (Nat × Nat × Nat) :=
  if threads.val<2 ∨ p.hp.val<3 then none else
  let count := ParallelKeygen.count x86 p.hp.val
  some (ParallelKeygen.subHeight x86 p.hp.val, count, min threads.val count)

def result := Option.map (fun (q : U32 × Usize × Usize) => (q.1.val,q.2.1.val,q.2.2.val))

private theorem threshold_value (x86 : Bool) (cut : U32) (arch : cut.val=(if x86 then 8 else 9))
    (p : params.Params) (threads : Usize) (height : p.hp.val≤9) :
    policy cut p threads ⦃ out => result out=value x86 p threads ⦄ := by
  unfold policy value
  by_cases serial : threads<2#usize
  · have b : threads.val<2 := serial
    simp [serial,b,result]
  simp only [serial,ite_false]
  by_cases tiny : p.hp<3#u32
  · have b : p.hp.val<3 := tiny
    simp [tiny,b,result]
  have nserial : ¬ threads.val<2 := serial
  have ntiny : ¬ p.hp.val<3 := tiny
  simp only [tiny,nserial,ntiny,ite_false,or_self]
  obtain ⟨sub,subret,subVal⟩ : ∃ sub : U32,
      (if cut≤p.hp then (ok 3#u32 : Result U32) else if 6#u32≤p.hp then ok 2#u32 else ok 0#u32)=ok sub ∧
      sub.val=ParallelKeygen.subHeight x86 p.hp.val := by
    unfold ParallelKeygen.subHeight
    by_cases high : cut≤p.hp
    · have raw : cut.val≤p.hp.val := high
      rw [arch] at raw
      exact ⟨3#u32,by simp [high],by simp [raw]⟩
    · have raw : ¬cut.val≤p.hp.val := high
      rw [arch] at raw
      by_cases mid : 6#u32≤p.hp
      · have m : 6≤p.hp.val := mid
        exact ⟨2#u32,by simp [high,mid],by simp [raw,m]⟩
      · have m : ¬6≤p.hp.val := mid
        exact ⟨0#u32,by simp [high,mid],by simp [raw,m]⟩
  have geom := ParallelKeygen.geometry x86 p.hp.val height
  have le : sub.val≤p.hp.val := subVal ▸ geom.1
  simp only [subret,bind_ok]
  step with U32.sub_spec (x:=p.hp) (y:=sub) le as ⟨diff,ds⟩
  step with Usize.ShiftLeft_spec 1#usize diff (by have bits := System.Platform.le_numBits; scalar_tac) as ⟨count,bits,_⟩
  have countEq : count.val=ParallelKeygen.count x86 p.hp.val := by
    rw [bits,Nat.one_shiftLeft,ds,subVal]
    change ParallelKeygen.count x86 p.hp.val % Usize.size=_
    rw [Nat.mod_eq_of_lt (by have := geom.2.1; scalar_tac)]
  simp [lift,bind_ok,result,cache.builder.nativeShake.Vector.min_val,subVal,countEq]

theorem arm (p : params.Params) (threads : Usize) (height : p.hp.val≤9) :
    Arm.slh.parallel.proof_keygen_plan p threads ⦃ out => result out=value false p threads ⦄ :=
  threshold_value false 9#u32 rfl p threads height

theorem x86 (p : params.Params) (threads : Usize) (height : p.hp.val≤9) :
    X86.slh.parallel.proof_keygen_plan p threads ⦃ out => result out=value true p threads ⦄ :=
  threshold_value true 8#u32 rfl p threads height
end slhdsa.ParallelKeygenPlan
