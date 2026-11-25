import Parallel.LowForsWrites
import Parallel.LowForsNodes
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelLowFors
open ShakeBatch NativeVerify
variable [machine : Machine] [host : Host machine] [wide : Wide]

def field {N} (p : params.Params) (sk seed : Array U8 N) (addr : address.Adrs)
    (choices : alloc.vec.Vec U32) (t : Nat) : Nat → Spec.Bytes
  | 0 => Spec.forsSkGen (Shake.params p) (bytes sk.val) (bytes seed.val) (adrsS addr) (absolute choices p.a t)
  | j+1 => Spec.forsNode (Shake.params p) (bytes sk.val) (ForsDriver.sibling choices.slice p.a t j)
      j (bytes seed.val) (adrsS addr)

def Fields {N} (first active stride cols : Nat) (value : Nat → Nat → Spec.Bytes) (journal : Journal N) :=
  journal.length=cols*active ∧ ∀ c<cols, ∀ l<active,
    journal.val[c*active+l]!.1.val=(first+l)*stride+c ∧ bytes journal.val[c*active+l]!.2.val=value (first+l) c

/-- The full journal publishes each selected field once. Distinct lanes or
columns within the ticket cannot target the same physical OnceLock. -/
theorem slots_injective {N : Usize} {first active stride cols : Nat} {value : Nat → Nat → Spec.Bytes}
    {journal : Journal N} (fields : Fields first active stride cols value journal) (shape : cols≤stride)
    {a b i j : Nat} (ca : a<cols) (cb : b<cols) (li : i<active) (lj : j<active)
    (same : journal.val[a*active+i]!.1=journal.val[b*active+j]!.1) : i=j ∧ a=b := by
  have eq := congrArg (fun x : Usize => x.val) same
  rw [(fields.2 a ca i li).1,(fields.2 b cb j lj).1] at eq
  have mono (x y c d : Nat) (lt : x<y) (hc : c<cols) :
      (first+x)*stride+c < (first+y)*stride+d := by
    have m := Nat.mul_le_mul_right stride (show first+x+1≤first+y by omega)
    rw [Nat.add_one_mul] at m;omega
  have ij : i=j := by
    rcases Nat.lt_trichotomy i j with t|t|t
    · have := mono i j a b t ca;omega
    · exact t
    · have := mono j i b a t cb;omega
  exact ⟨ij,by subst j;omega⟩

theorem extend {N} (first active stride c : Nat) (value : Nat → Nat → Spec.Bytes)
    (init out : Journal N) (rows : Array (Array U8 N) machine.width)
    (prev : Fields first active stride c value init)
    (writes : Written init active (fun l => (first+l)*stride+c) rows out)
    (values : ∀ l<active, bytes rows.val[l]!.val=value (first+l) c) :
    Fields first active stride (c+1) value out := by
  obtain ⟨len,records⟩ := prev
  obtain ⟨size,frame,new⟩ := writes
  refine ⟨by rw [size,len,Nat.add_one_mul],?_⟩
  intro col bound lane live
  by_cases same : c=col
  · subst col
    rw [←len];obtain ⟨slot,row⟩ := new lane live
    exact ⟨slot,by rw [row,values lane live]⟩
  · have limit := Nat.mul_le_mul_right active (show col+1≤c by omega)
    rw [Nat.add_one_mul] at limit
    rw [frame _ (by omega)]
    exact records _ (by omega) _ live

theorem rounds_spec {N} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N) (addr : address.Adrs)
    (choices : alloc.vec.Vec U32) (first active stride : Usize) (low : U32) (ids : Array U32 machine.width)
    (journal : Journal N) (correct : ActiveCorrect machine host.perm)
    (domain : addr.typ=address.FORS_TREE ∧ addr.word2=0#u32 ∧ addr.word3=0#u32)
    (ha : p.a.val≤14) (count : choices.length≤35) (digits : ∀ t<choices.length, choices.val[t]!.val<2^p.a.val)
    (enabled : 0<active.val) (width : active.val≤machine.width.val) (capacity : first.val+active.val≤choices.length)
    (height : low.val≤p.a.val) (narrow : machine.width≠8#usize ∨ low.val≤3) (shape : stride.val=p.a.val+1)
    (absoluteIds : ∀ i<machine.width.val, ids.val[i]!.val=absolute choices p.a (ParallelForsTicket.treeAt first.val active.val i))
    (start : Fields first.val active.val stride.val 1 (field p sk seed addr choices) journal) :
    ticket_loop1 ⟨0#u32,low⟩ sk seed addr stride journal first active ids ⦃ out =>
      Fields first.val active.val stride.val (low.val+1) (field p sk seed addr choices) out ⦄ := by
  unfold ticket_loop1
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range U32 × Journal N => low.val-q.1.start.val)
    (inv := fun q => q.1.end=low ∧ q.1.start.val≤low.val ∧
      Fields first.val active.val stride.val (q.1.start.val+1) (field p sk seed addr choices) q.2)
  · rintro ⟨it,cur⟩ ⟨stop,lim,prev⟩
    simp only at stop lim prev ⊢
    unfold ticket_loop1.body
    by_cases more : it.start.val < it.end.val
    · have live : it.start.val<low.val := stop ▸ more
      step with core.iter.range.IteratorRange.next_U32_some_spec it more as ⟨_,next,tag,inc,ends⟩
      simp only [tag]
      step with sibling_indices N ids it.start (by omega) as ⟨siblings,positions⟩
      have indices (i : Nat) (hi : i<machine.width.val) :
          siblings.val[i]!.val=ParallelForsTicket.sibling choices p.a it.start (ParallelForsTicket.treeAt first.val active.val i) := by
        rw [positions i hi,absoluteIds i hi];rfl
      have bounds (i : Nat) (hi : i<machine.width.val) : (siblings.val[i]!.val+1)*2^it.start.val<2^32 := by
        let t := ParallelForsTicket.treeAt first.val active.val i
        have inside : t<choices.length := by
          change first.val+min i (active.val-1)<choices.length
          have := Nat.min_le_right i (active.val-1);omega
        rw [indices i hi]
        exact lt_of_le_of_lt (ParallelForsTicket.sibling_room choices p.a it.start t ha (by omega) count inside (digits t inside)) (by decide : 1048576<2^32)
      step with nodes_spec correct p hp sk seed addr siblings active it.start domain width bounds
        (by rcases narrow with e|e;exact Or.inl e;exact Or.inr (by omega)) as ⟨rows,rowValues⟩
      have mx : 2^32-1≤Usize.max := by agrind
      have size := prev.1
      have cap := Nat.mul_le_mul (show it.start.val+1≤15 by omega) (show active.val≤35 by omega)
      have fit (l : Nat) (hl : l<active.val) : (first.val+l)*stride.val+1+it.start.val≤Usize.max := by
        have lim := Nat.mul_le_mul (show first.val+l≤35 by omega) (show stride.val≤15 by omega)
        omega
      step with sibling_writes active first stride it.start cur rows width (by omega) (by omega) fit as ⟨out,writes⟩
      try simp only [step_simps]
      refine ⟨ends.trans stop,by omega,?_,by omega⟩
      rw [inc]
      apply extend first.val active.val stride.val (it.start.val+1) _ cur out rows prev
      · simpa only [Nat.add_assoc,Nat.add_comm 1] using writes
      · intro l hl
        have tv : ParallelForsTicket.treeAt first.val active.val l=first.val+l := by
          unfold ParallelForsTicket.treeAt;rw [min_eq_left (by omega)]
        rw [rowValues l hl,indices l (hl.trans_le width),tv];rfl
    · step with core.iter.range.IteratorRange.next_U32_none_spec it (by omega) as ⟨_,_,tag,_⟩
      simp only [tag,step_simps]
      have eq : it.start.val=low.val := by rw [stop] at more;omega
      simpa only [eq] using prev
  · exact ⟨rfl,Nat.zero_le _,start⟩
end slhdsa.ParallelLowFors
