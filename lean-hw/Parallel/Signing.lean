import Spec.SlhDsa
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Basic

namespace ParallelSigning
open Spec

/-- Each successful ticket owns one cell. Completing a ticket changes only that cell. -/
def fill (node : Nat → Bytes) (order : List Nat) : Nat → Option Bytes :=
  order.foldl (fun slots job k => if k = job then some (node job) else slots k) (fun _ => none)

theorem fill_lookup (node : Nat → Bytes) (order : List Nat) (k : Nat) :
    fill node order k = if k ∈ order then some (node k) else none := by
  induction order using List.reverseRecOn with
  | nil => simp [fill]
  | append_singleton xs j ih =>
    simp only [fill, List.foldl_append, List.foldl_cons, List.foldl_nil] at *
    by_cases h : k = j <;> simp [h, ih]

def ticket (d hp j h : Nat) := (hp - 1 - h) * d + j

theorem decode_ticket {d hp j h : Nat} (layer : j < d) (height : h < hp) :
    let k := ticket d hp j h
    k < d * hp ∧ k % d = j ∧ hp - 1 - k / d = h := by
  dsimp [ticket]
  have div : ((hp-1-h)*d+j)/d = hp-1-h := by
    rw [Nat.mul_comm (hp-1-h), Nat.mul_add_div (by omega : 0 < d), Nat.div_eq_of_lt layer, Nat.add_zero]
  have bound := Nat.mul_le_mul_right d (show hp-1-h+1 ≤ hp by omega)
  rw [Nat.add_mul, Nat.one_mul] at bound
  exact ⟨by rw [Nat.mul_comm d hp]; omega, by simp [Nat.mod_eq_of_lt layer], by omega⟩

def loc (hp t l : Nat) : Nat → Nat × Nat
  | 0 => (t,l)
  | j+1 => let tree := (loc hp t l j).1; (tree >>> hp, tree % 2^hp)

def addr (j t : Nat) : Adrs := { Adrs.zero with layer := j, tree := t }

def worker (p : Params) (sk pk : Bytes) (t l k : Nat) : Bytes :=
  let j := k % p.d
  let h := p.hp - 1 - k / p.d
  let (tree,leaf) := loc p.hp t l j
  xmssNode p sk ((leaf >>> h) ^^^ 1) h pk (addr j tree)

/-- Assemble from completed tickets, allowing any interleaving of their writes. -/
def part (p : Params) (sk pk : Bytes) (t l : Nat) (slots : Nat → Option Bytes)
    (root : Bytes) (j : Nat) : Bytes :=
  let (tree,leaf) := loc p.hp t l j
  wotsSign p root sk pk { (addr j tree).setTypeAndClear WOTS_HASH with keypair := leaf } ++
    (List.range p.hp).flatMap fun h => (slots (ticket p.d p.hp j h)).getD []

theorem part_eq (p : Params) (sk pk : Bytes) (t l : Nat) (order : List Nat)
    (covers : ∀ k < p.d * p.hp, k ∈ order) (root : Bytes) (j : Nat) (hj : j < p.d) :
    part p sk pk t l (fill (worker p sk pk t l) order) root j =
      xmssSign p root sk (loc p.hp t l j).2 pk (addr j (loc p.hp t l j).1) := by
  unfold part xmssSign
  dsimp only
  congr 1
  apply List.flatMap_congr; intro h hh
  obtain ⟨bound,layer,height⟩ := decode_ticket hj (List.mem_range.mp hh)
  simp [fill_lookup, covers _ bound, worker, layer, height, Nat.shiftRight_eq_div_pow]

def assemble (p : Params) (sk pk : Bytes) (t l : Nat) (slots : Nat → Option Bytes)
    (st : Bytes × Bytes) (j : Nat) : Bytes × Bytes :=
  let (tree,leaf) := loc p.hp t l j
  let s := part p sk pk t l slots st.2 j
  (st.1 ++ s, if j+1 < p.d then xmssPkFromSig p leaf s st.2 pk (addr j tree) else st.2)

def serial (p : Params) (sk pk : Bytes) (st : Bytes × Bytes × Nat × Nat) (j : Nat) :=
  let (sig,root,tree,leaf) := st
  let a := addr j tree
  let s := xmssSign p root sk leaf pk a
  (sig ++ s, xmssPkFromSig p leaf s root pk a, tree >>> p.hp, tree % 2^p.hp)

/-- Equality of all signature bytes. The final unused root need never be rebuilt. -/
theorem hypertree_eq (p : Params) (msg sk pk : Bytes) (t l : Nat) (order : List Nat)
    (covers : ∀ k < p.d * p.hp, k ∈ order) :
    ((List.range p.d).foldl (assemble p sk pk t l (fill (worker p sk pk t l) order))
      ([],msg)).1 = htSign p msg sk pk t l := by
  let a := assemble p sk pk t l (fill (worker p sk pk t l) order)
  let x := fun n => (List.range n).foldl a ([],msg)
  let y := fun n => (List.range n).foldl (serial p sk pk) ([],msg,t,l)
  have inv (n : Nat) (hn : n ≤ p.d) : (x n).1 = (y n).1 ∧
      (n < p.d → (x n).2 = (y n).2.1) ∧ (y n).2.2 = loc p.hp t l n := by
    induction n with
    | zero => exact ⟨rfl, fun _ => rfl, rfl⟩
    | succ n ih =>
      have lt : n < p.d := by omega
      obtain ⟨sig,root,pos⟩ := ih (by omega)
      have xs : x (n+1) = a (x n) n := by simp [x,List.range_succ]
      have ys : y (n+1) = serial p sk pk (y n) n := by simp [y,List.range_succ]
      rw [xs,ys]
      dsimp only [a, assemble, serial]
      rw [part_eq _ _ _ _ _ _ covers _ _ lt, root lt, sig, ← pos]
      exact ⟨rfl, fun h => ite_eq_left h, by simp [loc, ← pos]⟩
  exact (inv p.d (by omega)).1

/-- At scope exit the caller has observed at least one out-of-range fetch. Every
in-range fetch has completed its set by the join. Relaxed fetch-add has a
single modification order, while the writes can complete in any permutation. -/
structure Joined (jobs : Nat) (completed : List Nat) where
  fetches : Nat
  drained : jobs < fetches
  writes : completed.Perm ((List.range fetches).filter (· < jobs))

/-- Atomic steps for the shared counter and per-ticket slots. A worker can
complete any outstanding job. An out-of-range fetch changes only the counter. -/
inductive Trace (jobs : Nat) : Nat → List Nat → List Nat → Prop where
  | start : Trace jobs 0 [] []
  | claim {k pending done} : Trace jobs k pending done → k < jobs →
      Trace jobs (k+1) (k::pending) done
  | stop {k pending done} : Trace jobs k pending done → jobs ≤ k →
      Trace jobs (k+1) pending done
  | publish {k pending done j rest} : Trace jobs k pending done → pending.Perm (j::rest) →
      Trace jobs k rest (j::done)

theorem Trace.ledger {jobs k pending done} (t : Trace jobs k pending done) :
    (pending ++ done).Perm ((List.range k).filter (· < jobs)) := by
  induction t with
  | start => simp
  | claim prior h ih =>
    simp only [List.cons_append,List.range_succ,List.filter_append]
    simpa [h] using (ih.cons _).trans (by simpa using (List.perm_middle (l₂ := [])).symm)
  | stop prior h ih =>
    simpa [List.range_succ, Nat.not_lt.mpr h] using ih
  | publish prior move ih =>
    exact (List.perm_middle.trans (move.append_right _).symm).trans ih

/-- A joined scope has no unfinished publications. The caller drains to the
first unavailable ticket even when every worker spawn fails. -/
def Trace.joined {jobs k done} (t : Trace jobs k [] done) (drained : jobs < k) :
    Joined jobs done := ⟨k, drained, by simpa using t.ledger⟩

theorem Joined.exactly_once {jobs : Nat} {completed : List Nat} (q : Joined jobs completed) :
    completed.Nodup ∧ (∀ k, k ∈ completed ↔ k < jobs) := by
  constructor
  · apply q.writes.nodup_iff.mpr
    exact List.nodup_range.filter _
  · intro k
    rw [q.writes.mem_iff]
    simp only [List.mem_filter,List.mem_range,decide_eq_true_eq]
    have := q.drained
    omega

/-- Compose the new algorithm with the unchanged message digest and FORS operations. -/
def signInternal (p : Params) (m sk randomness : Bytes) (completed : List Nat) : Bytes :=
  let secret := block p sk 0
  let pk := block p sk 2
  let r := PRFmsg p (block p sk 1) randomness m
  let digest := Hmsg p r pk (block p sk 3) m
  let t := digestTree p digest
  let l := digestLeaf p digest
  let md := digest.take p.mdBytes
  let a := {{Adrs.zero with tree := t}.setTypeAndClear FORS_TREE with keypair := l}
  let fors := forsSign p md secret pk a
  let root := forsPkFromSig p fors md pk a
  let slots := fill (worker p secret pk t l) completed
  r ++ fors ++ ((List.range p.d).foldl (assemble p secret pk t l slots) ([],root)).1

theorem signInternal_eq (p : Params) (m sk randomness : Bytes) (completed : List Nat)
    (joined : Joined (p.d*p.hp) completed) :
    signInternal p m sk randomness completed = slhSignInternal p m sk randomness := by
  have covers := fun k hk => (joined.exactly_once.2 k).mpr hk
  unfold signInternal slhSignInternal
  dsimp only
  exact congrArg (_ ++ ·) (hypertree_eq _ _ _ _ _ _ _ covers)

theorem joined_sign_fips {p : Params} (m sk randomness : Bytes) {fetches completed}
    (trace : Trace (p.d*p.hp) fetches [] completed) (drained : p.d*p.hp < fetches) :
    signInternal p m sk randomness completed = slhSignInternal p m sk randomness :=
  signInternal_eq p m sk randomness completed (trace.joined drained)

/-- The public pure-signature framing and its 255-byte context limit. -/
theorem context_sign_fips {p : Params} (m ctx sk randomness : Bytes) {fetches completed}
    (trace : Trace (p.d*p.hp) fetches [] completed) (drained : p.d*p.hp < fetches) :
    (if ctx.length > 255 then none else
      some (signInternal p (withContext m ctx) sk randomness completed)) =
      slhSign p m ctx sk randomness := by
  simp only [slhSign, joined_sign_fips _ _ _ trace drained]

#print axioms context_sign_fips
#print axioms joined_sign_fips
#print axioms signInternal_eq
#print axioms hypertree_eq
end ParallelSigning
