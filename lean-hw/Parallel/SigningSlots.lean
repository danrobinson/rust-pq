import Parallel.Fused
import Parallel.CacheTicketSignature

open Spec ParallelSigning ParallelCached
namespace ParallelFused.Slots

private def hashStep (p : Params) (pk : Bytes) (a : Adrs) (layer : Nat) (auth : Nat → Bytes)
    (s : Bytes × Nat) (h : Nat) : Bytes × Nat :=
  let other := auth (layer*p.hp+h)
  let parent := s.2/2
  let input := if s.2%2=0 then s.1++other else other++s.1
  (H p pk {a.setTypeAndClear TREE with word2:=h+1,word3:=parent} input,parent)

/-- The last phase-one finisher walks each authentication path using the previously
published leaf and siblings. The Rust code updates its index after hashing a pair. -/
def climb (p : Params) (pk : Bytes) (a : Adrs) (layer : Nat) (auth : Nat → Bytes)
    (leaf : Bytes) (index levels : Nat) : Bytes × Nat :=
  (List.range levels).foldl (hashStep p pk a layer auth) (leaf,index)

theorem climb_succ (p : Params) (pk : Bytes) (a : Adrs) (j : Nat) (auth : Nat → Bytes)
    (leaf : Bytes) (i h : Nat) :
    climb p pk a j auth leaf i (h+1) =
      let prev := climb p pk a j auth leaf i h
      let sibling := auth (j*p.hp+h)
      let parent := prev.2/2
      (H p pk {a.setTypeAndClear TREE with word2:=h+1,word3:=parent}
        (if prev.2%2=0 then prev.1++sibling else sibling++prev.1),parent) := by
  simp only [climb,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
  rfl

theorem climbed (p : Params) (sk pk : Bytes) (a : Adrs) (j i : Nat) (auth : Nat → Bytes)
    (leaf : Bytes) (base : leaf=xmssNode p sk i 0 pk a)
    (siblings : ∀ h<p.hp, auth (j*p.hp+h)=xmssNode p sk ((i/2^h)^^^1) h pk a)
    (c : Nat) (bound : c≤p.hp) :
    climb p pk a j auth leaf i c = (xmssNode p sk (i/2^c) c pk a,i/2^c) := by
  induction c with
  | zero => simp [climb,base]
  | succ c ih =>
    rw [show climb p pk a j auth leaf i (c+1)=hashStep p pk a j auth (climb p pk a j auth leaf i c) c by
      simp [climb,List.range_succ],ih (by omega)]
    simp only [hashStep,siblings c (by omega),Nat.pow_succ,← Nat.div_div_eq_div_mul]
    simp only [xmssNode]
    generalize i/2^c = idx
    rw [Spec.xor_one_eq]
    by_cases even : idx%2=0
    · simp only [even,ite_true]
      rw [show 2*(idx/2)=idx by omega]
    · simp only [even,ite_false]
      rw [show 2*(idx/2)=idx-1 by omega,show idx-1+1=idx by omega]

def signerInput (p : Params) (pk first : Bytes) (tree leaf : Nat)
    (leaves auth : Nat → Bytes) : Nat → Bytes
  | 0 => first
  | j+1 =>
    let pos := loc p.hp tree leaf j
    (climb p pk (addr j pos.1) j auth (leaves j) pos.2 p.hp).1

def wots (p : Params) (sk pk : Bytes) (tree leaf : Nat) (input : Nat → Bytes) (j : Nat) :=
  let pos := loc p.hp tree leaf j
  wotsSign p (input j) sk pk {(addr j pos.1).setTypeAndClear WOTS_HASH with keypair:=pos.2}

def assemble (p : Params) (r : Bytes) (forest : List Bytes) (auth : Nat → Bytes)
    (cells : Nat → Option Bytes) :=
  r ++ forest.flatten ++ (List.range p.d).flatMap fun j =>
    (cells j).getD [] ++ (List.range p.hp).flatMap fun h => auth (j*p.hp+h)

private def jobs (d : Nat) := (List.range d).map fun j => [j]

/-- Worker evidence for a successful Rust return. Phase one publishes the
selected FORS secrets, authentication nodes and signing-leaf public keys.
Phase two signs the actual climbed roots. The join reads the published cells. -/
def Output (p : Params) (md sk pk : Bytes) (a : Adrs) (r : Bytes) (tree leaf : Nat) (out : Bytes) : Prop :=
  ∃ forest auth leaves,
    forest=forsRows p md sk pk a ∧
    (∀ j<p.d, ∀ h<p.hp,
      let pos := loc p.hp tree leaf j
      auth (j*p.hp+h)=xmssNode p sk ((pos.2/2^h)^^^1) h pk (addr j pos.1)) ∧
    (∀ j, j+1<p.d →
      let pos := loc p.hp tree leaf j
      leaves j=xmssNode p sk pos.2 0 pk (addr j pos.1)) ∧
    let first := forsPkFromSig p forest.flatten md pk a
    let want := wots p sk pk tree leaf (signerInput p pk first tree leaf leaves auth)
    ∃ workers st, 0<workers ∧ Tickets.Reach (Tickets.valued (jobs p.d) want) workers st ∧
      (¬∃ next, Tickets.Step (Tickets.valued (jobs p.d) want) st next) ∧
      out=assemble p r forest auth st.cells

theorem output_fips (p : Params) (valid : p.Valid) (md sk pk : Bytes) (a : Adrs) (r : Bytes)
    (tree leaf : Nat) (out : Bytes) (bounded : leaf<2^p.hp) (published : Output p md sk pk a r tree leaf out) :
    out=r ++ forsSign p md sk pk a ++ htSign p (forsPkFromSig p (forsSign p md sk pk a) md pk a) sk pk tree leaf := by
  obtain ⟨forest,auth,leaves,rows,sibs,lvs,workers,st,positive,run,stopped,layout⟩ := published
  have forestEq : forest.flatten=forsSign p md sk pk a := rows ▸ fors_bytes _ _ _ _ _
  let first := forsPkFromSig p forest.flatten md pk a
  let want := wots p sk pk tree leaf (signerInput p pk first tree leaf leaves auth)
  have cover : (jobs p.d).flatten.Perm (List.range p.d) := by simp [jobs,← List.flatMap_def,List.flatMap_singleton]
  have final := (Tickets.ticket_join want run positive cover stopped).2
  have bound (j : Nat) : (loc p.hp tree leaf j).2<2^p.hp := by
    cases j with
    | zero => exact bounded
    | succ j => exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have inputs (j : Nat) (hj : j<p.d) :
      signerInput p pk first tree leaf leaves auth j=message p first sk pk tree leaf j := by
    cases j with
    | zero => rfl
    | succ j =>
      simp only [signerInput,message]
      rw [climbed p sk pk _ j _ auth _ (lvs j hj) (sibs j (by omega)) p.hp (by omega)]
      simp [Nat.div_eq_of_lt (bound j)]
  rw [layout,← forestEq,← hypertree p valid first sk pk tree leaf bounded]
  unfold assemble
  congr 1
  apply List.flatMap_congr
  intro j inside
  have hj := List.mem_range.mp inside
  rw [joined_value _ _ want cover final _ hj]
  simp only [Option.getD_some,wots,want,inputs j hj,layer,xmssSign]
  congr 1
  apply List.flatMap_congr
  intro h insideH
  exact sibs j hj h (List.mem_range.mp insideH)

/-- Existence independently of the safety implication: for every standard
input and any positive worker count the specified phase-one cells admit a
complete phase-two run yielding the FIPS signature body. -/
theorem constructed (p : Params) (valid : p.Valid) (md sk pk : Bytes) (a : Adrs) (r : Bytes)
    (tree leaf workers : Nat) (bounded : leaf<2^p.hp) (positive : 0<workers) :
    ∃ out, Output p md sk pk a r tree leaf out ∧
      out=r ++ forsSign p md sk pk a ++ htSign p (forsPkFromSig p (forsSign p md sk pk a) md pk a) sk pk tree leaf := by
  let forest := forsRows p md sk pk a
  let leaves := fun j =>
    let pos := loc p.hp tree leaf j
    xmssNode p sk pos.2 0 pk (addr j pos.1)
  let auth := fun i =>
    let pos := loc p.hp tree leaf (i/p.hp)
    xmssNode p sk ((pos.2/2^(i%p.hp))^^^1) (i%p.hp) pk (addr (i/p.hp) pos.1)
  let first := forsPkFromSig p forest.flatten md pk a
  let want := wots p sk pk tree leaf (signerInput p pk first tree leaf leaves auth)
  obtain ⟨st,_,reachable,stopped⟩ := Tickets.maximal_extension
    (Tickets.Reach.start (jobs:=Tickets.valued (jobs p.d) want) (workerCount:=workers))
  let out := assemble p r forest auth st.cells
  have witness : Output p md sk pk a r tree leaf out := by
    refine ⟨forest,auth,leaves,rfl,?_,fun _ _ => rfl,workers,st,positive,reachable,stopped,rfl⟩
    intro j _ h hh
    have layer : (j*p.hp+h)/p.hp=j := by rw [Nat.mul_comm j, Nat.mul_add_div valid.hp_pos,Nat.div_eq_of_lt hh,Nat.add_zero]
    simp [auth,layer,Nat.mod_eq_of_lt hh]
  exact ⟨out,witness,output_fips _ valid _ _ _ _ _ _ _ _ bounded witness⟩

end ParallelFused.Slots
