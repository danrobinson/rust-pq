import Buffered.Counts
namespace slhdsa.ForsHorizontal
open Buffered
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
theorem carry_next (b s h : Nat) (changed : waiting (carryCount b s) s=16)
    (hb : b<2048) (hs : s<14) :
    carryCount b (s+1) h = if h=s+1 then carryCount b s h+8 else carryCount b s h := by
  have bump : produced (b+1) (s+1)=produced b (s+1)+8 := by
    interval_cases s <;> simp [waiting,carryCount,produced] at changed ⊢ <;> omega
  by_cases eq : h=s+1
  · subst h; simp [carryCount,bump]
  · by_cases le : h≤s <;> simp [carryCount,eq,le,show (h≤s+1) ↔ h≤s by omega]

theorem carry_stop (b s h : Nat) (hb : b<2048) (hs : s≤14) (hh : h≤15)
    (stop : waiting (carryCount b s) s<16) : carryCount b s h = produced (b+1) h := by
  by_cases before : h≤s
  · simp [carryCount,before]
  have propagated : produced b h=produced (b+1) h := by
    have large : s<h := by omega
    interval_cases s <;> interval_cases h <;> first | omega | (simp [waiting,carryCount,produced] at stop ⊢ <;> omega)
  simp [carryCount,before,propagated]

theorem carry_stats (b s : Nat) (hb : b<2048) (hs : s≤14) :
    waiting (carryCount b s) s≤16 ∧ waiting (carryCount b s) (s+1)≤8 ∧
    2*(carryCount b s (s+1))≤carryCount b s s ∧
    2*(carryCount b s (s+2))≤carryCount b s (s+1) := by
  interval_cases s <;> simp [waiting,carryCount,produced] <;> omega

theorem block_stats (b : Nat) : waiting (produced b) 0≤8 ∧ 2*produced b 1≤produced b 0 := by
  simp [waiting,produced]
  omega

theorem flush_start (z h : Nat) (lo : 3≤z) (hi : z≤14) :
    flushCount z 0 h = produced (2^(z-3)) h := by
  by_cases zero : h=0
  · subst h;interval_cases z <;> decide
  · simp [flushCount,zero]

theorem flush_next (z s h : Nat) (lo : 3≤z) (hi : z≤14) (live : s<z) :
    flushCount z (s+1) h = if h=s+1 then flushCount z s h+waiting (flushCount z s) s/2 else flushCount z s h := by
  by_cases eq : h=s+1
  · subst h
    have table : ∀ z : Fin 15, ∀ s : Fin 15, 3≤z.val → s.val<z.val →
      flushCount z.val (s.val+1) (s.val+1)=flushCount z.val s.val (s.val+1)+waiting (flushCount z.val s.val) s.val/2 := by decide
    simpa using table ⟨z,by omega⟩ ⟨s,by omega⟩ lo live
  · by_cases le : h≤s <;> simp [flushCount,eq,le,show (h≤s+1) ↔ h≤s by omega]

theorem flush_stats (z s : Nat) (lo : 3≤z) (hi : z≤14) (live : s<z) :
    let c := flushCount z s
    waiting c s % 2=0 ∧ waiting c s≤16 ∧ waiting c (s+1)+waiting c s/2≤16 ∧
      2*c (s+1)≤c s ∧ 2*c (s+2)≤c (s+1) ∧ c (s+1)≤1048576 := by
  have table : ∀ z : Fin 15, ∀ s : Fin 15, 3≤z.val → s.val<z.val →
    let c := flushCount z.val s.val
    waiting c s.val % 2=0 ∧ waiting c s.val≤16 ∧ waiting c (s.val+1)+waiting c s.val/2≤16 ∧
      2*c (s.val+1)≤c s.val ∧ 2*c (s.val+2)≤c (s.val+1) ∧ c (s.val+1)≤1048576 := by decide
  exact table ⟨z,by omega⟩ ⟨s,by omega⟩ lo live

theorem finish_stats (z : Nat) (lo : 3≤z) (hi : z≤14) :
    waiting (flushCount z z) z=1 ∧ flushCount z z (z+1)=0 := by
  interval_cases z <;> decide

theorem carry_room (b s k : Nat) (hb : b<2048) (hs : s≤14) (hk : k≤14) : waiting (carryCount b s) k≤16 := by
  interval_cases s <;> interval_cases k <;> simp [waiting,carryCount,produced] <;> omega

theorem flush_room (z s k : Nat) (lo : 3≤z) (hi : z≤14) (hs : s≤z) (hk : k≤z) : waiting (flushCount z s) k≤16 := by
  have table : ∀ z : Fin 15, ∀ s : Fin 15, ∀ k : Fin 15, 3≤z.val → s.val≤z.val → k.val≤z.val →
    waiting (flushCount z.val s.val) k.val≤16 := by decide
  exact table ⟨z,by omega⟩ ⟨s,by omega⟩ ⟨k,by omega⟩ lo hs hk

theorem carry_end (z b k : Nat) (lo : 3≤z) (hi : z≤14) (inside : b<2^(z-3)) (hk : k≤z+1) :
    carryCount b z k=produced (b+1) k := by
  by_cases small : k≤z
  · simp [carryCount,small]
  · have eq : k=z+1 := by omega
    subst k
    simp only [carryCount,Nat.not_succ_le_self,ite_false,produced]
    have power : 2^(z-3) < 2^(z+1) := Nat.pow_lt_pow_right (by decide) (by omega)
    rw [Nat.div_eq_of_lt (by omega),Nat.div_eq_of_lt (by omega)]
end slhdsa.ForsHorizontal
