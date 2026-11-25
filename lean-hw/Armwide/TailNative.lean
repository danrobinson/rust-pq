import Armwide.Transitions
import Armwide.SignRefill

namespace slhdsa.Armwide.Transitions
open WotsRefill
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

private instance : Inhabited Stepping := ⟨⟨0,⟨[],0,0,0,false⟩,[]⟩⟩

private def tailRow (rows : List Stepping) (r : Register) : SignLane :=
  ⟨rows[r.x]!.digest,rows[r.chain]!.before.chain,rows[r.cur]!.before.curT+r.advanced,
    rows[r.left]!.before.left-r.consumed,r.phase=1⟩

/-- Interpret the registers and chain-addressed store events actually produced by the
native tail. Entries of the hashed digest register pair are represented by their bytes. -/
def tailWithWriter {α : Type} (write : Writer α) (q : Count) (rows : List Stepping) (o : α) :=
  let tr := actual q (fun i => 1 < rows[i]!.before.left) (fun i => rows[i]!.before.isPrf)
  (tr.kept.map (tailRow rows),
   tr.writes.foldl (fun out e => write out rows[e.chain]!.before.chain rows[e.x]!.digest) o)

abbrev tailUpdates := tailWithWriter setOut

private theorem noqueue (rows : List SignLane) (o : Nat → Spec.Bytes) :
    signRetireRefill [] (fun _ => 0) rows [] o =
      (rows.filter (fun r => r.left ≠ 0),[],
       (rows.filter (fun r => r.left = 0)).foldl (fun acc l => setOut acc l.chain l.x) o) := by
  induction rows generalizing o with
  | nil => rfl
  | cons l ls ih =>
    by_cases dead : l.left=0 <;> simp [signRetireRefill,dead,ih,List.filter_cons]

private theorem indexes {α : Type} [Inhabited α] (rs : List α) :
    (List.range rs.length).map (fun i => rs[i]!) = rs := by
  apply List.ext_getElem (by simp)
  intro i h h'
  simp only [List.getElem_map,List.getElem_range,getElem!_pos rs i h']

theorem tail_updates_eq (q : Count) (short : width q < 4) (rows : List Stepping)
    (size : rows.length = width q) (out : Nat → Spec.Bytes) :
    tailWithWriter setOut q rows out =
      let (rem,_,o) := signRetireRefill [] (fun _ => 0) (rows.map (progressed false 1)) [] out
      (rem,o) := by
  rw [noqueue]
  unfold tailWithWriter
  rw [active_step]
  have small : rows.length < 4 := by omega
  simp only [blueprint,←size,small,decide_true,Bool.true_and,↓reduceIte,List.map_map,List.foldl_map]
  have ix := indexes rows
  conv_rhs => rw [←ix]
  simp only [List.map_map,List.filter_map,List.foldl_map]
  have keep : (fun i : Nat => decide (1 < rows[i]!.before.left)) =
      ((fun r => decide (r.left ≠ 0)) ∘ progressed false 1 ∘ fun i => rows[i]!) := by
    funext i
    simp [progressed,Function.comp_def]; omega
  have dead : (fun i : Nat => !decide (1 < rows[i]!.before.left)) =
      ((fun r => decide (r.left = 0)) ∘ progressed false 1 ∘ fun i => rows[i]!) := by
    funext i
    simp [progressed,Function.comp_def]; omega
  rw [keep,dead]
  congr 1
  apply List.map_congr_left
  intro i _
  cases ph : rows[i]!.before.isPrf <;> simp only [tailRow,progressed,Function.comp_def,ph,Bool.not_true,Bool.not_false,Bool.false_eq_true,↓reduceIte,Nat.add_zero] <;> rfl

private instance : Inhabited SignLane := ⟨⟨[],0,0,0,false⟩⟩

def uncompactedWith {α : Type} (write : Writer α) (sk : Spec.Bytes) (digits : Nat → Nat) (shared : Bool) (bulk : Nat) :
    List Stepping → List Nat → α → List SignLane × List Nat × α
  | [], q, o => ([],q,o)
  | l::ls,q,o =>
    let (row,q',o') := transitionWith write sk digits shared bulk l q o
    let (rest,q'',o'') := uncompactedWith write sk digits shared bulk ls q' o'
    (row::rest,q'',o'')


private theorem uncompacted_size (sk : Spec.Bytes) (digits : Nat → Nat) (shared : Bool) (bulk : Nat)
    (ls : List Stepping) (q : List Nat) (o : Nat → Spec.Bytes) :
    (uncompactedWith setOut sk digits shared bulk ls q o).1.length = ls.length := by
  induction ls generalizing q o with
  | nil => rfl
  | cons l ls ih => simp only [uncompactedWith,List.length_cons,ih]

private theorem uncompacted_filter (sk : Spec.Bytes) (digits : Nat → Nat) (shared : Bool) (bulk : Nat)
    (ls : List Stepping) (q : List Nat) (o : Nat → Spec.Bytes) :
    let (rows,q',o') := uncompactedWith setOut sk digits shared bulk ls q o
    (rows.filter (fun l => l.left ≠ 0),q',o') = nativeUpdates sk digits shared bulk ls q o := by
  induction ls generalizing q o with
  | nil => rfl
  | cons l ls ih =>
    simp only [uncompactedWith,nativeUpdates]
    set v := transitionWith setOut sk digits shared bulk l q o
    specialize ih v.2.1 v.2.2
    cases e : uncompactedWith setOut sk digits shared bulk ls v.2.1 v.2.2 with
    | mk rem pair =>
      rw [e] at ih
      rw [←ih]
      by_cases h : v.1.left=0 <;> simp [h]

/-- Interpret the in-place moves of the full-loop compaction after every posthash
retirement and refill has modified the physical register array. -/
def compactWithWriter {α : Type} (write : Writer α) (sk : Spec.Bytes) (digits : Nat → Nat) (shared : Bool) (bulk : Nat)
    (ls : List Stepping) (q : List Nat) (o : α) :=
  let (rows,q',o') := uncompactedWith write sk digits shared bulk ls q o
  let tr := actual 3 (fun i => rows[i]!.left ≠ 0) (fun i => rows[i]!.isPrf)
  (tr.kept.map (fun (reg : Register) =>
    (⟨rows[reg.x]!.x,rows[reg.chain]!.chain,rows[reg.cur]!.curT,rows[reg.left]!.left,reg.phase=1⟩ : SignLane)),
   q',o')

abbrev compactFour := compactWithWriter setOut

theorem compact_four_eq (sk : Spec.Bytes) (digits : Nat → Nat) (shared : Bool) (bulk : Nat)
    (ls : List Stepping) (q : List Nat) (o : Nat → Spec.Bytes) (size : ls.length=4) :
    compactWithWriter setOut sk digits shared bulk ls q o = nativeUpdates sk digits shared bulk ls q o := by
  unfold compactWithWriter
  rw [←uncompacted_filter]
  have len := uncompacted_size sk digits shared bulk ls q o
  cases e : uncompactedWith setOut sk digits shared bulk ls q o with
  | mk rows pair =>
    rw [e] at len
    have four : rows.length = 4 := len.trans size
    simp only [active_step,blueprint,show width 3=4 by rfl,show ¬(4<4) by decide,
      decide_false,Bool.false_and,↓reduceIte,List.map_map]
    congr 1
    have project (i : Nat) : (⟨rows[i]!.x,rows[i]!.chain,rows[i]!.curT,rows[i]!.left,rows[i]!.isPrf.toNat=1⟩ : SignLane) = rows[i]! := by
      cases h : rows[i]! with | mk x c t l ph => cases ph <;> rfl
    conv_rhs => rw [←indexes rows]
    simp only [List.filter_map,List.map_map,Function.comp_def,project,four]

end slhdsa.Armwide.Transitions
