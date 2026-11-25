import Armplatform.WideForsRecovery

namespace slhdsa.WideFors
set_option maxHeartbeats 1000000

/-- Actual call boundaries in traversal order. Source replay also checks the
state, addresses and byte origins passed at each boundary. -/
inductive Op
  | leaves
  | all16 (height count : Nat)
  | pair (height count : Nat)
  | scalar (height row : Nat)
  | final256 (size : Nat)
  | try512 (size : Nat)
  | block512 (offset : Nat)
  | truncate512 (size : Nat)
  deriving Inhabited, DecidableEq

def levelOps (n k : Nat) (paired : Bool) (h : Nat) :=
  if n=16 then [.all16 h k] else
    let count := if paired then k/2*2 else 0
    Op.pair h count :: (List.range' count (k-count)).map (.scalar h ·)

def finalOps (n k : Nat) (multi : Bool) : List Op :=
  let block := if n=16 then 64 else 128
  let total := (22+n*k+1+block/8+block-1)/block*block
  if n=16 then [.final256 total] else
    .try512 total :: (if multi then [] else
      (List.range (total/128)).map (fun i => .block512 (128*i)) ++ [.truncate512 total])

def plan (p : Spec.Params) (paired multi : Bool) :=
  Op.leaves :: (List.range p.a).flatMap (levelOps p.n p.k paired) ++ finalOps p.n p.k multi

private def coord (p : Spec.Params) (sig pk : Spec.Bytes) (a : Spec.Adrs) (paired : Bool) (t h : Nat)
    (old : Spec.Bytes × Nat) : Spec.Bytes × Nat :=
  let sib := Spec.block p sig (t*(p.a+1)+1+h)
  (parentAt p paired t h pk a old.2 old.1 sib, old.2/2)

private def run (p : Spec.Params) (sig md pk : Spec.Bytes) (a : Spec.Adrs) (paired : Bool)
    (t : Nat) (old : Spec.Bytes × Nat) : Op → Spec.Bytes × Nat
  | .leaves => physicalRows p paired sig pk a (Spec.base2b md p.a p.k) 0 t
  | .all16 h k | .pair h k => if t<k then coord p sig pk a paired t h old else old
  | .scalar h i => if t=i then coord p sig pk a paired t h old else old
  | .final256 _ | .try512 _ | .block512 _ | .truncate512 _ => old

private theorem singles {α : Type} (f : α → α) (t : Nat) (xs : List Nat) (distinct : xs.Nodup) (v : α) :
    xs.foldl (fun x i => if t=i then f x else x) v = if t∈xs then f v else v := by
  induction xs generalizing v with
  | nil => simp
  | cons i xs ih =>
    obtain ⟨fresh,rest⟩ := List.nodup_cons.mp distinct
    simp only [List.foldl_cons,ih rest,List.mem_cons]
    by_cases eq : t=i
    · subst i; simp [fresh]
    · simp [eq]

private theorem run_level (p : Spec.Params) (sig md pk : Spec.Bytes) (a : Spec.Adrs) (paired : Bool)
    (t h : Nat) (ht : t<p.k) (v : Spec.Bytes × Nat) :
    (levelOps p.n p.k paired h).foldl (run p sig md pk a paired t) v = coord p sig pk a paired t h v := by
  by_cases small : p.n=16
  · simp [levelOps,small,run,ht]
  · let c := if paired then p.k/2*2 else 0
    have lim : c≤p.k := by dsimp [c]; split <;> omega
    simp only [levelOps,if_neg small,List.foldl_cons,List.foldl_map,Function.comp_def,run]
    change (List.range' c (p.k-c)).foldl (fun x i => if t=i then coord p sig pk a paired t h x else x)
      (if t<c then coord p sig pk a paired t h v else v) = _
    rw [singles _ _ _ (List.nodup_range' _ (by decide))]
    have member : t ∈ List.range' c (p.k-c) ↔ c≤t := by rw [List.mem_range'_1]; omega
    by_cases before : t<c
    · rw [if_neg (fun h => Nat.not_le_of_gt before (member.mp h)),if_pos before]
    · rw [if_pos (member.mpr (by omega)),if_neg before]

private theorem run_final (p : Spec.Params) (sig md pk : Spec.Bytes) (a : Spec.Adrs) (paired multi : Bool)
    (t : Nat) (v : Spec.Bytes × Nat) :
    (finalOps p.n p.k multi).foldl (run p sig md pk a paired t) v = v := by
  unfold finalOps
  split
  · rfl
  · cases multi
    · simp [run,List.foldl_map,Function.comp_def]
    · rfl

private def isFinal : Op → Bool
  | .leaves | .all16 .. | .pair .. | .scalar .. => false
  | _ => true

private theorem plan_final (p : Spec.Params) (paired multi : Bool) :
    (plan p paired multi).filter isFinal = finalOps p.n p.k multi := by
  have none (h : Nat) : (levelOps p.n p.k paired h).filter isFinal=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro op mem
    unfold levelOps at mem
    split at mem
    · simp only [List.mem_singleton] at mem
      subst op; simp [isFinal]
    · simp only [List.mem_cons,List.mem_map] at mem
      rcases mem with rfl|⟨i,_,rfl⟩ <;> simp [isFinal]
  have levels (hs : List Nat) : (hs.flatMap (levelOps p.n p.k paired)).filter isFinal=[] := by
    induction hs with
    | nil => rfl
    | cons h hs ih => simp only [List.flatMap_cons,List.filter_append,none,ih,List.append_nil]
  have all : (finalOps p.n p.k multi).filter isFinal = finalOps p.n p.k multi := by
    apply List.filter_eq_self.mpr
    intro op mem
    unfold finalOps at mem
    split at mem
    · simp only [List.mem_singleton] at mem; subst op; rfl
    · cases multi <;> simp only [Bool.false_eq_true,ite_false,List.mem_cons,List.mem_append,
        List.mem_map,List.mem_singleton,ite_true,List.not_mem_nil,or_false] at mem
      · rcases mem with rfl|⟨_,_,rfl⟩|rfl <;> rfl
      · subst op; rfl
  simp only [plan,List.cons_append,List.filter_cons,isFinal,Bool.false_eq_true,ite_false,List.filter_append,levels,all,List.nil_append]

def evaluated (p : Spec.Params) (paired multi : Bool) (sig md pk : Spec.Bytes) (a : Spec.Adrs)
    (ops : List Op) :=
  let roots := (List.range p.k).flatMap (fun t => (ops.foldl (run p sig md pk a paired t) ([],0)).1)
  if ops.filter isFinal = finalOps p.n p.k multi then
    final p pk {a.setTypeAndClear Spec.FORS_ROOTS with keypair:=a.keypair} roots multi
  else []

theorem evaluate_plan (p : Spec.Params) (paired multi : Bool) (sig md pk : Spec.Bytes) (a : Spec.Adrs) :
    evaluated p paired multi sig md pk a (plan p paired multi) = hardwareRecover p paired multi sig md pk a := by
  unfold evaluated hardwareRecover
  rw [if_pos (plan_final p paired multi)]
  apply congrArg (fun xs => final p pk _ xs multi)
  apply List.flatMap_congr
  intro t ht
  have walk (h : Nat) : ((List.range h).flatMap (levelOps p.n p.k paired)).foldl
      (run p sig md pk a paired t) (physicalRows p paired sig pk a (Spec.base2b md p.a p.k) 0 t) =
      physicalRows p paired sig pk a (Spec.base2b md p.a p.k) h t := by
    induction h with
    | zero => rfl
    | succ h ih =>
      rw [List.range_succ,List.flatMap_append,List.foldl_append,ih]
      simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
      rw [run_level _ _ _ _ _ _ _ _ (List.mem_range.mp ht)]
      rfl
  simp only [plan,List.cons_append,List.foldl_cons,List.foldl_append,run_final]
  exact congrArg Prod.fst (walk p.a)

theorem source_plan_fips (p : Spec.Params) [Fact (p.family=.sha2)] (valid : p.Valid)
    (paired multi : Bool) (sig md pk : Spec.Bytes) (hs : sig.length=p.k*(1+p.a)*p.n)
    (hp : pk.length=p.n) (a : Spec.Adrs) :
    evaluated p paired multi sig md pk a (plan p paired multi) = Spec.forsPkFromSig p sig md pk a := by
  rw [evaluate_plan,hardware_recover_fips p valid _ _ _ _ _ hs hp]

end slhdsa.WideFors
