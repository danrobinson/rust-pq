import Buffered.Leaves
import Buffered.Counts
open Aeneas Aeneas.Std Result
namespace slhdsa.Buffered

abbrev Buffer (N : Usize) := Array (Row16 N) 17#usize
abbrev Lengths := Array Usize 17#usize
abbrev Cursors := Array U32 17#usize
abbrev CellFn := Nat → Nat → Spec.Bytes

def levelBase (root z h : Nat) := root*2^(z-h)
def rowBase (root z : Nat) (made : Nat → Nat) (h : Nat) := levelBase root z h+2*made (h+1)
def nextBase (root z : Nat) (made : Nat → Nat) (h : Nat) := levelBase root z h + if h=0 then 0 else made h

def cellBytes {N depth : Usize} (buf : Array (Row16 N) depth) (h j : Nat) := bytes buf.val[h]!.val[j]!.val

structure Grid {N depth : Usize} (node : CellFn) (root z : Nat) (made : Nat → Nat)
    (buf : Array (Row16 N) depth) (len : Array Usize depth) (cursor : Array U32 depth) : Prop where
  count : ∀ h≤z, len.val[h]!.val=waiting made h
  index : ∀ h≤z, cursor.val[h]!.val=nextBase root z made h
  cell : ∀ h≤z, ∀ j<waiting made h, cellBytes buf h j=node h (rowBase root z made h+j)

theorem Grid.congr_made {N depth : Usize} {node root z c d} {buf : Array (Row16 N) depth} {len cur}
    (old : Grid node root z c buf len cur) (agree : ∀ h≤z+1,c h=d h) : Grid node root z d buf len cur := by
  have waitingEq (h : Nat) (le : h≤z) : waiting c h=waiting d h := by simp [waiting,agree h (by omega),agree (h+1) (by omega)]
  constructor
  · intro h le; rw [old.count h le,waitingEq h le]
  · intro h le; rw [old.index h le]; simp [nextBase,agree h (by omega)]
  · intro h le j inside
    rw [←waitingEq h le] at inside
    rw [old.cell h le j inside]
    simp [rowBase,agree (h+1) (by omega)]

theorem level_step (root z h : Nat) (live : h<z) : levelBase root z h=2*levelBase root z (h+1) := by
  have sub : z-h=z-(h+1)+1 := by omega
  simp [levelBase,sub,Nat.pow_succ,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]

/-- A transfer consumes all children at h and appends n freshly calculated parents
to the next row. Other rows and previously stored parents survive the copy. -/
theorem Grid.merge {N depth : Usize} {node root z c d} {buf out : Array (Row16 N) depth} {len newLen cur newCur}
    (old : Grid node root z c buf len cur) (h n : Nat) (live : h<z)
    (child : waiting c h=2*n) (balanced : 2*c (h+1)≤c h) (up : 2*c (h+2)≤c (h+1))
    (change : ∀ k, d k=if k=h+1 then c k+n else c k)
    (lengths : ∀ k≤z, newLen.val[k]!.val=if k=h then 0 else if k=h+1 then len.val[k]!.val+n else len.val[k]!.val)
    (cursor : ∀ k≤z, newCur.val[k]!.val=if k=h+1 then cur.val[k]!.val+n else cur.val[k]!.val)
    (cells : ∀ k≤z, ∀ j<16, cellBytes out k j =
      if k=h+1 ∧ waiting c (h+1)≤j ∧ j<waiting c (h+1)+n then
        node (h+1) (nextBase root z c (h+1)+(j-waiting c (h+1))) else cellBytes buf k j)
    (safe : ∀ k≤z, waiting d k≤16) : Grid node root z d out newLen newCur := by
  have ck : c h=2*c (h+1)+2*n := by dsimp [waiting] at child;omega
  have oldUpper := old.count (h+1) live
  have dst : c (h+1)=2*c (h+2)+waiting c (h+1) := by unfold waiting;change c (h+1)=2*c (h+2)+(c (h+1)-2*c (h+2));omega
  have counts (k : Nat) : waiting d k=if k=h then 0 else if k=h+1 then waiting c k+n else waiting c k := by
    unfold waiting
    rw [change k,change (k+1)]
    by_cases e : k=h
    · subst k;simp;omega
    · by_cases f : k=h+1
      · subst k;simp;change c (h+1)+n-2*c (h+2)=c (h+1)-2*c (h+2)+n;omega
      · simp [e,f]
  constructor
  · intro k kz; rw [lengths k kz,old.count k kz,counts k]
  · intro k kz; rw [cursor k kz,old.index k kz];unfold nextBase;rw [change k];split_ifs <;> omega
  · intro k kz j hj
    rw [cells k kz j (hj.trans_le (safe k kz))]
    by_cases low : k=h
    · subst k;rw [counts h,if_pos rfl] at hj;omega
    rw [counts k,if_neg low] at hj
    by_cases upper : k=h+1
    · subst k
      simp only [ite_true] at hj
      have origin : rowBase root z d (h+1)=rowBase root z c (h+1) := by simp [rowBase,change]
      rw [origin]
      by_cases fresh : waiting c (h+1)≤j
      · rw [if_pos ⟨rfl,fresh,hj⟩];congr 1
        simp [nextBase,rowBase]
        change levelBase root z (h+1)+c (h+1)+(j-waiting c (h+1))=levelBase root z (h+1)+2*c (h+2)+j
        omega
      · rw [if_neg (by omega),old.cell (h+1) live j (by omega)]
    · rw [if_neg upper] at hj
      rw [if_neg (by tauto),old.cell k kz j hj]
      simp [rowBase,change,low]

theorem Grid.appendLeaves {N depth : Usize} {node root z c d} {buf out : Array (Row16 N) depth} {len newLen cur}
    (old : Grid node root z c buf len cur) (balanced : 2*c 1≤c 0)
    (change : ∀ k, d k=if k=0 then c k+8 else c k)
    (lengths : ∀ k≤z, newLen.val[k]!.val=if k=0 then len.val[0]!.val+8 else len.val[k]!.val)
    (cells : ∀ k≤z, ∀ j<16, cellBytes out k j=
      if k=0 ∧ waiting c 0≤j ∧ j<waiting c 0+8 then node 0 (levelBase root z 0+c 0+(j-waiting c 0)) else cellBytes buf k j)
    (safe : ∀ k≤z, waiting d k≤16) : Grid node root z d out newLen cur := by
  have count (k : Nat) : waiting d k=if k=0 then waiting c k+8 else waiting c k := by
    unfold waiting;rw [change k,change (k+1)];simp;split_ifs <;> subst_vars <;> first | rfl | (change c 0+8-2*c 1=c 0-2*c 1+8;omega)
  constructor
  · intro k kz;rw [lengths k kz,count k];by_cases e:k=0
    · subst k;rw [if_pos rfl,if_pos rfl,old.count 0 kz]
    · rw [if_neg e,if_neg e,old.count k kz]
  · intro k kz;rw [old.index k kz];unfold nextBase;rw [change];split_ifs <;> rfl
  · intro k kz j hj
    rw [cells k kz j (hj.trans_le (safe k kz))]
    rw [count k] at hj
    have origin : rowBase root z d k=rowBase root z c k := by simp [rowBase,change]
    rw [origin]
    by_cases zero : k=0
    · subst k;simp only [ite_true] at hj
      by_cases fresh : waiting c 0≤j
      · rw [if_pos ⟨rfl,fresh,hj⟩]; congr 1
        simp [rowBase,waiting] at fresh ⊢
        omega
      · rw [if_neg (by omega),old.cell 0 kz j (by omega)]
    · rw [if_neg zero] at hj
      rw [if_neg (by tauto),old.cell k kz j hj]
end slhdsa.Buffered
