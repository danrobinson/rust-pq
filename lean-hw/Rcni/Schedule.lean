import Rcni.Rounds
open Aeneas Aeneas.Std Result
namespace slhdsa.Intel.RustCrypto
open RcNiRust.sha256.x86_sha
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000

def registers (W : List Word) (init : State) (t : Nat) (x y : Reg) : Prop :=
  x = abef (after W init (4*t)) ∧ y = cdgh (after W init (4*t))

theorem scheduled (W : List Word) (init : State) (r : Usize) (x y : Reg) (w : Array Reg 4#usize)
    (base : 4≤r.val) (top : r.val+4≤16) (mod : r.val%4=0) (rec : Rec W)
    (regs : registers W init r.val x y) (ring : Ring w W r.val) :
    schedule_rounds16 r x y w ⦃ a b ws => registers W init (r.val+4) a b ∧ Ring ws W (r.val+4) ⦄ := by
  unfold schedule_rounds16 schedule_rounds16_loop
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × Reg × Reg × Array Reg 4#usize => 4-q.1.start.val)
    (inv := fun q => q.1.end=4#usize ∧ q.1.start.val≤4 ∧
      registers W init (r.val+q.1.start.val) q.2.1 q.2.2.1 ∧ Ring q.2.2.2 W (r.val+q.1.start.val))
  · rintro ⟨it,x,y,w⟩ ⟨stop,bound,hw,hr⟩
    simp only at stop bound hw hr
    unfold schedule_rounds16_loop.body
    by_cases more : it.start.val<4
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [stop]; exact more) as ⟨option,next,present,increment,last⟩
      simp only [present,bind_ok]
      step as ⟨w0,read0⟩
      step as ⟨n1,a1⟩
      step as ⟨j1,b1⟩
      step as ⟨w1,read1⟩
      step as ⟨n2,a2⟩
      step as ⟨j2,b2⟩
      step as ⟨w2,read2⟩
      step as ⟨n3,a3⟩
      step as ⟨j3,b3⟩
      step as ⟨w3,read3⟩
      let t := r.val+it.start.val
      have read (k : Nat) (j : Usize) (v : Reg) (hj : j.val=k%4) (lo : t-4≤k) (hi : k<t)
          (eq : v=w.val[j.val]!) : v=group W (4*k) := by rw [eq,hj]; exact hr k lo (by omega)
      have A := read (t-4) it.start w0 (by dsimp [t]; omega) (by omega) (by dsimp [t]; omega)
        (by simpa (disch := scalar_tac) only [getElem!_pos] using read0)
      have B := read (t-3) j1 w1 (by dsimp [t]; omega) (by omega) (by dsimp [t]; omega)
        (by simpa (disch := scalar_tac) only [getElem!_pos] using read1)
      have C := read (t-2) j2 w2 (by dsimp [t]; omega) (by omega) (by dsimp [t]; omega)
        (by simpa (disch := scalar_tac) only [getElem!_pos] using read2)
      have D := read (t-1) j3 w3 (by dsimp [t]; omega) (by omega) (by dsimp [t]; omega)
        (by simpa (disch := scalar_tac) only [getElem!_pos] using read3)
      have expansion := expand_spec W (4*(t-4)) (by dsimp [t]; omega) rec
      rw [show 4*(t-4)+4=4*(t-3) by dsimp [t]; omega,show 4*(t-4)+8=4*(t-2) by dsimp [t]; omega,
        show 4*(t-4)+12=4*(t-1) by dsimp [t]; omega,show 4*(t-4)+16=4*t by dsimp [t]; omega] at expansion
      rw [A,B,C,D]
      simp only [expand,align4,core.core_arch.x86.sha._mm_sha256msg1_epu32,
        core.core_arch.x86.sha._mm_sha256msg2_epu32,core.core_arch.x86.sse2._mm_add_epi32,bind_ok,ok.injEq] at expansion ⊢
      rw [expansion]
      step as ⟨ws,updated⟩
      step as ⟨round,rv⟩
      step as ⟨msg,readWord⟩
      have value : msg=group W (4*round.val) := by simp (disch := scalar_tac) [readWord,updated,Array.set_val_eq,List.getElem_set,rv,t]
      have nextRing : Ring ws W (t+1) := by
        intro g lo hi
        rw [updated,Array.set_val_eq]
        by_cases current : g=t
        · subst g; rw [show t%4=it.start.val by dsimp [t]; omega,Avx2.setSame _ _ _ (by simp; omega)]
        · rw [Avx2.setOther _ _ _ _ (by dsimp [t] at *; omega)]
          exact hr _ (by dsimp [t] at *; omega) (by dsimp [t] at *; omega)
      obtain ⟨hx,hy⟩ := hw
      rw [value,hx,hy,← rv]
      step with rounds init round (by omega) as ⟨x',y',postX,postY⟩
      refine ⟨last.trans stop,by omega,?_,?_,by omega⟩
      · simpa only [registers,increment,rv,show 4*(r.val+(it.start.val+1))=4*(r.val+it.start.val)+4 by omega] using And.intro postX postY
      · simpa only [increment,Nat.add_assoc,t] using nextRing
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop]; change 4 ≤ it.start.val; omega) as ⟨option,next,none,_⟩
      simp only [none,step_simps]
      simpa [show it.start.val=4 by omega] using And.intro hw hr
  · simpa using And.intro regs ring
end slhdsa.Intel.RustCrypto
