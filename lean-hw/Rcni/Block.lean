import Rcni.Schedule
import Slhdsa.Proofs.Platform
open Aeneas Aeneas.Std Result
namespace slhdsa.Intel.RustCrypto
open RcNiRust RcNiRust.sha256.x86_sha
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

def blockStep {α : Type} (ret : Reg → Reg → α) (block : Array U8 64#usize) (abef cdgh : Reg) : Result α := do
  let w ← sha256.x86_sha.load_block block
  let mi ← Array.index_usize w 0#usize
  let (abef1, cdgh1) ← sha256.x86_sha.rounds4 0#usize abef cdgh mi
  let mi1 ← Array.index_usize w 1#usize
  let (abef2, cdgh2) ← sha256.x86_sha.rounds4 1#usize abef1 cdgh1 mi1
  let mi2 ← Array.index_usize w 2#usize
  let (abef3, cdgh3) ← sha256.x86_sha.rounds4 2#usize abef2 cdgh2 mi2
  let mi3 ← Array.index_usize w 3#usize
  let (abef4, cdgh4) ← sha256.x86_sha.rounds4 3#usize abef3 cdgh3 mi3
  let (abef5, cdgh5, w1) ←
    sha256.x86_sha.schedule_rounds16 4#usize abef4 cdgh4 w
  let (abef6, cdgh6, w2) ←
    sha256.x86_sha.schedule_rounds16 8#usize abef5 cdgh5 w1
  let (abef7, cdgh7, _) ←
    sha256.x86_sha.schedule_rounds16 12#usize abef6 cdgh6 w2
  let abef8 ← core.core_arch.x86.sse2._mm_add_epi32 abef7 abef
  let cdgh8 ← core.core_arch.x86.sse2._mm_add_epi32 cdgh7 cdgh
  ok (ret abef8 cdgh8)

private theorem load_ring (block : Array U8 64#usize) :
    load_block block ⦃ w => Ring w (Spec.SHA256.schedule (bytes block.val)) 4 ⦄ := by
  simp only [load_block,step_simps]
  intro g _ hi
  change g<4 at hi
  interval_cases g <;> simp (disch := decide) only [group,slhdsa.schedule_lt16] <;> rfl

theorem block_spec {α : Type} (ret : Reg → Reg → α) (block : Array U8 64#usize) (x y : Reg) :
    blockStep ret block x y ⦃ out => ∃ a b, out=ret a b ∧ stateWords (decode a b)=Spec.SHA256.compress (stateWords (decode x y)) (bytes block.val) ⦄ := by
  let W := Spec.SHA256.schedule (bytes block.val)
  let s := decode x y
  have hx : x=abef s := by cases x; cases y; rfl
  have hy : y=cdgh s := by cases x; cases y; rfl
  have recurrence : Rec W := fun i lo hi => slhdsa.schedule_rec _ i lo hi
  unfold blockStep
  step with load_ring block as ⟨w,ring⟩
  have read (i : Usize) (hi : i.val<4) (v : Reg) (val : v=w.val[i.val]'(by simp; omega)) :
      v=group W (4*i.val) := by
    rw [val,← getElem!_eq _ _ (by simp; omega),← Nat.mod_eq_of_lt hi]
    simpa [Nat.mod_eq_of_lt hi] using ring i.val (by omega) (by omega)
  step as ⟨w0,e0⟩
  rw [read 0#usize (by decide) w0 e0,hx,hy]
  have first := rounds (W := W) s 0#usize (by decide)
  rw [show after W s (4*(0#usize).val)=s by rfl] at first
  step with first as ⟨a0,b0,eA0,eB0⟩
  step as ⟨w1,e1⟩
  rw [read 1#usize (by decide) w1 e1,eA0,eB0]
  have next1 := rounds (W := W) s 1#usize (by decide)
  rw [show 4*(1#usize).val = 4*0+4 by decide] at next1
  rw [show 4*(1#usize).val = 4*0+4 by decide]
  step with next1 as ⟨a1,b1,eA1,eB1⟩
  step as ⟨w2,e2⟩
  rw [read 2#usize (by decide) w2 e2,eA1,eB1]
  have next2 := rounds (W := W) s 2#usize (by decide)
  rw [show 4*(2#usize).val = 4*1+4 by decide] at next2
  rw [show 4*(2#usize).val = 4*1+4 by decide]
  step with next2 as ⟨a2,b2,eA2,eB2⟩
  step as ⟨w3,e3⟩
  rw [read 3#usize (by decide) w3 e3,eA2,eB2]
  have next3 := rounds (W := W) s 3#usize (by decide)
  rw [show 4*(3#usize).val = 4*2+4 by decide] at next3
  rw [show 4*(3#usize).val = 4*2+4 by decide]
  step with next3 as ⟨a3,b3,eA3,eB3⟩
  step with scheduled W s 4#usize a3 b3 w (by decide) (by decide) (by decide) recurrence
    ⟨eA3,eB3⟩ ring as ⟨a4,b4,w4,regs4,ring4⟩
  step with scheduled W s 8#usize a4 b4 w4 (by decide) (by decide) (by decide) recurrence
    regs4 ring4 as ⟨a8,b8,w8,regs8,ring8⟩
  step with scheduled W s 12#usize a8 b8 w8 (by decide) (by decide) (by decide) recurrence
    regs8 ring8 as ⟨af,bf,wf,regs,_⟩
  obtain ⟨aEq,bEq⟩ := regs
  simp only [core.core_arch.x86.sse2._mm_add_epi32,bind_ok,step_simps,aEq,bEq]
  refine ⟨_,_,rfl,?_⟩
  have final := X86.finish s (bytes block.val)
  apply Eq.trans _ final
  change stateWords (decode _ _) = X86.stateWords (X86.feedForward s (after W s 64))
  generalize he : after W s 64 = last
  rcases s with ⟨a,b,c,d,e,f,g,h⟩
  rcases last with ⟨u,v,w,x,y,z,r,t⟩
  simp [stateWords,decode,abef,cdgh,X86.stateWords,X86.feedForward,BitVec.add_comm]
end slhdsa.Intel.RustCrypto
