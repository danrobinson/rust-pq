import Mathlib.Tactic
namespace slhdsa.Buffered
/-- Cumulative rows delivered to each level after a complete leaf batch. -/
def produced (b h : Nat) := 8*(b/2^h)
/-- During the carry sweep, levels up to the current level have received the
new batch and the higher levels still have their previous totals. -/
def carryCount (b step h : Nat) := if h≤step then produced (b+1) h else produced b h

def waiting (made : Nat → Nat) (h : Nat) := made h-2*made (h+1)

def complete (z h : Nat) := if h≤z then 2^(z-h) else 0

def flushCount (z step h : Nat) := if h≤step then complete z h else produced (2^(z-3)) h

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem carry_bound (b step h : Nat) :
    carryCount b step h ≤ 8*(b+1) := by
  unfold carryCount produced
  split <;> apply Nat.mul_le_mul_left <;> first | exact Nat.div_le_self .. | exact (Nat.div_le_self ..).trans (by omega)

theorem start_leaf (b : Nat) (h : Nat) :
    carryCount b 0 h = if h=0 then produced b h+8 else produced b h := by
  cases h <;> simp [carryCount,produced,Nat.mul_add]

theorem carry_next (b s h : Nat) (changed : waiting (carryCount b s) s=16)
    (hb : b<64) (hs : s<9) :
    carryCount b (s+1) h = if h=s+1 then carryCount b s h+8 else carryCount b s h := by
  have bump : produced (b+1) (s+1)=produced b (s+1)+8 := by
    have table : ∀ x : Fin 64, ∀ y : Fin 9,
      waiting (carryCount x.val y.val) y.val=16 →
      produced (x.val+1) (y.val+1)=produced x.val (y.val+1)+8 := by decide
    exact table ⟨b,hb⟩ ⟨s,hs⟩ changed
  by_cases eq : h=s+1
  · subst h; simp [carryCount,bump]
  · by_cases le : h≤s <;> simp [carryCount,eq,le,show (h≤s+1) ↔ h≤s by omega]

theorem carry_stop (b s h : Nat) (hb : b<64) (hs : s≤9) (hh : h≤10)
    (stop : waiting (carryCount b s) s<16) : carryCount b s h = produced (b+1) h := by
  by_cases before : h≤s
  · simp [carryCount,before]
  have propagated : produced b h=produced (b+1) h := by
    have table : ∀ x : Fin 64, ∀ y : Fin 10, ∀ k : Fin 11, y.val<k.val →
      waiting (carryCount x.val y.val) y.val<16 → produced x.val k.val=produced (x.val+1) k.val := by decide
    exact table ⟨b,hb⟩ ⟨s,by omega⟩ ⟨h,by omega⟩ (show s<h by omega) stop
  simp [carryCount,before,propagated]

theorem carry_stats (b s : Nat) (hb : b<64) (hs : s≤9) :
    waiting (carryCount b s) s≤16 ∧ waiting (carryCount b s) (s+1)≤8 ∧
    2*(carryCount b s (s+1))≤carryCount b s s ∧
    2*(carryCount b s (s+2))≤carryCount b s (s+1) := by
  have table : ∀ x : Fin 64, ∀ y : Fin 10,
    let c := carryCount x.val y.val
    waiting c y.val≤16 ∧ waiting c (y.val+1)≤8 ∧ 2*c (y.val+1)≤c y.val ∧ 2*c (y.val+2)≤c (y.val+1) := by decide
  exact table ⟨b,hb⟩ ⟨s,by omega⟩

theorem block_stats (b : Nat) : waiting (produced b) 0≤8 ∧ 2*produced b 1≤produced b 0 := by
  simp [waiting,produced]
  omega

theorem flush_start (z h : Nat) (lo : 3≤z) (hi : z≤9) :
    flushCount z 0 h = produced (2^(z-3)) h := by
  by_cases zero : h=0
  · subst h;interval_cases z <;> decide
  · simp [flushCount,zero]

theorem flush_next (z s h : Nat) (lo : 3≤z) (hi : z≤9) (live : s<z) :
    flushCount z (s+1) h = if h=s+1 then flushCount z s h+waiting (flushCount z s) s/2 else flushCount z s h := by
  by_cases eq : h=s+1
  · subst h
    have table : ∀ z : Fin 10, ∀ s : Fin 10, 3≤z.val → s.val<z.val →
      flushCount z.val (s.val+1) (s.val+1)=flushCount z.val s.val (s.val+1)+waiting (flushCount z.val s.val) s.val/2 := by decide
    simpa using table ⟨z,by omega⟩ ⟨s,by omega⟩ lo live
  · by_cases le : h≤s <;> simp [flushCount,eq,le,show (h≤s+1) ↔ h≤s by omega]

theorem flush_stats (z s : Nat) (lo : 3≤z) (hi : z≤9) (live : s<z) :
    let c := flushCount z s
    waiting c s % 2=0 ∧ waiting c s≤16 ∧ waiting c (s+1)+waiting c s/2≤16 ∧
      2*c (s+1)≤c s ∧ 2*c (s+2)≤c (s+1) ∧ c (s+1)≤512 := by
  have table : ∀ z : Fin 10, ∀ s : Fin 10, 3≤z.val → s.val<z.val →
    let c := flushCount z.val s.val
    waiting c s.val % 2=0 ∧ waiting c s.val≤16 ∧ waiting c (s.val+1)+waiting c s.val/2≤16 ∧
      2*c (s.val+1)≤c s.val ∧ 2*c (s.val+2)≤c (s.val+1) ∧ c (s.val+1)≤512 := by decide
  exact table ⟨z,by omega⟩ ⟨s,by omega⟩ lo live

theorem finish_stats (z : Nat) (lo : 3≤z) (hi : z≤9) :
    waiting (flushCount z z) z=1 ∧ flushCount z z (z+1)=0 := by
  interval_cases z <;> decide

theorem carry_room (b s k : Nat) (hb : b<64) (hs : s≤9) (hk : k≤9) : waiting (carryCount b s) k≤16 := by
  have table : ∀ b : Fin 64, ∀ s : Fin 10, ∀ k : Fin 10, waiting (carryCount b.val s.val) k.val≤16 := by decide
  exact table ⟨b,hb⟩ ⟨s,by omega⟩ ⟨k,by omega⟩

theorem flush_room (z s k : Nat) (lo : 3≤z) (hi : z≤9) (hs : s≤z) (hk : k≤z) : waiting (flushCount z s) k≤16 := by
  have table : ∀ z : Fin 10, ∀ s : Fin 10, ∀ k : Fin 10, 3≤z.val → s.val≤z.val → k.val≤z.val →
    waiting (flushCount z.val s.val) k.val≤16 := by decide
  exact table ⟨z,by omega⟩ ⟨s,by omega⟩ ⟨k,by omega⟩ lo hs hk

theorem carry_end (z b k : Nat) (lo : 3≤z) (hi : z≤9) (inside : b<2^(z-3)) (hk : k≤z+1) :
    carryCount b z k=produced (b+1) k := by
  have table : ∀ z : Fin 10, ∀ b : Fin 64, ∀ k : Fin 11, 3≤z.val → b.val<2^(z.val-3) → k.val≤z.val+1 →
    carryCount b.val z.val k.val=produced (b.val+1) k.val := by decide
  have small : 2^(z-3)≤64 := by interval_cases z <;> decide
  exact table ⟨z,by omega⟩ ⟨b,by omega⟩ ⟨k,by omega⟩ lo inside hk

end slhdsa.Buffered
