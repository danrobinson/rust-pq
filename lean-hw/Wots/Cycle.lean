import Wots.Finish
import Wots.RecoveryHash
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Wots
open WotsRust.sha256.x86.avx512
open WotsRust.core.core_arch.x86.avx512f

abbrev RecoveryState := Buffers × Words × LaneArray × LaneArray × Reg × Reg × U16 × Usize × Hash

def cycle (N : Usize) (iv pre : Hash) (half : Reg) (out : Buffers) (indices starts : LaneArray)
    (idx counter : Reg) (active : U16) (pos : Usize) (hash : Hash) (w : Words) :
    Result (ControlFlow RecoveryState Buffers) := do
  let (packed,digest) ← compressRound N iv pre hash w counter half
  let (next,mask,buf) ← finishRound (N := N) counter active digest out indices
  ok (cont (buf,packed,indices,starts,idx,next,mask,pos,digest))

def iteration (N : Usize) (zero : Reg) (sig : Slice U8) (digits : Slice U32) (order : Order)
    (work : Usize) (iv pre : Hash) (half swap : Reg) (out : Buffers) (w : Words)
    (indices starts : LaneArray) (idx counter : Reg) (active : U16) (pos : Usize) (hash : Hash) := do
  let (ix,st,mask,p,assigned) ← recover_loop5_loop0 digits order work indices starts active pos 0#u16
  if assigned != 0#u16 then
    let (idx',counter',h,w') ← loadAssigned N ix st counter zero assigned sig hash w swap
    cycle N iv pre half out ix st idx' counter' mask p h w'
  else cycle N iv pre half out ix st idx counter mask p hash w

private theorem sameBind {A B : Type} (x : Result A) {f g : A → Result B} (eq : ∀ a, f a=g a) :
    Std.bind x f = Std.bind x g := by rw [funext eq]

private theorem throughBind {A B C : Type} {x : Result A} {f : A → Result B} {g : B → Result C}
    {h : A → Result C} (eq : ∀ v, h v = Std.bind (f v) g) :
    Std.bind x h = Std.bind (Std.bind x f) g := by
  rw [Std.bind_assoc]
  exact sameBind _ eq

private theorem bindIte {A B : Type} (p : Prop) [Decidable p] (a b : Result A) (f : A → Result B) :
    Std.bind (if p then a else b) f = if p then Std.bind a f else Std.bind b f := by
  by_cases h : p <;> simp [h]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem cycle_body_eq (N : Usize) (zero : Reg) (sig : Slice U8) (digits : Slice U32) (order : Order)
    (work : Usize) (iv pre : Hash) (half swap : Reg) (out : Buffers) (w : Words)
    (indices starts : LaneArray) (idx counter : Reg) (active : U16) (pos : Usize) (hash : Hash) :
    recover_loop5.body N zero sig digits order work iv pre half swap out w indices starts idx counter active pos hash =
      if active ≠ 0#u16 ∨ pos < work then
        iteration N zero sig digits order work iv pre half swap out w indices starts idx counter active pos hash
      else ok (done out) := by
  obtain ⟨limit,divOK,_⟩ := UScalar.div_spec N (show (4#usize).val ≠ 0 by decide)
  have p2 : recover_loop5_loop2 = wots_endpoints_loop1_loop0_loop0 := rfl
  have p4 : recover_loop5_loop4 = wots_endpoints_loop1_loop0_loop0 := rfl
  have p8 : recover_loop5_loop8 = wots_endpoints_loop1_loop0_loop0 := rfl
  have p10 : recover_loop5_loop10 = wots_endpoints_loop1_loop0_loop0 := rfl
  obtain ⟨r5,r9,r11⟩ := retire_branch_eq (N := N)
  unfold recover_loop5.body
  simp only [bne_iff_ne,refill_empty_branch,gather_empty_branch,p2,p4,p8,p10,r5,r9,r11]
  by_cases alive : active ≠ 0#u16 <;> first
    | rw [if_pos alive,if_pos (Or.inl alive)]
    | (rw [if_neg alive]; by_cases pending : pos < work <;> first
        | rw [if_pos pending,if_pos (Or.inr pending)]
        | rw [if_neg pending,if_neg (not_or_intro alive pending)])
  all_goals
    unfold iteration
    apply sameBind
    rintro ⟨ix,st,mask,p,assigned⟩
    simp only [bne_iff_ne]
    change (if assigned ≠ 0#u16 then _ else _) = (if assigned ≠ 0#u16 then _ else _)
    by_cases fresh : assigned ≠ 0#u16 <;> first | simp only [if_pos fresh] | simp only [if_neg fresh]
    all_goals simp only [loadAssigned,loadLanes,cycle,compressRound,packHigh,PlatformRust.sha256.x86.avx512.compress,
      finishRound,stageAll,divOK,lift,bind_tc_eq,Std.bind_assoc,bind_ok,bindIte,bne_iff_ne]
    all_goals repeat' (first | (apply sameBind; first | rintro ⟨a,b⟩ | intro x) | (apply throughBind; first | rintro ⟨a,b⟩ | intro x))
    all_goals simp only [bind_ok,Array.to_slice_mut] <;> rfl

end slhdsa.X86.Wots
