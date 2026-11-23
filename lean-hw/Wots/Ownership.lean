import Wots.Cycle
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots

/-- Each occupied lane owns a distinct consumed queue position, and its Rust
index register contains the signature index stored at that position. -/
def owns (order : Order) (indices : LaneArray) (active : U16) (pos : Nat)
    (owner : Fin 16 → Option Nat) :=
  (∀ i j q, owner i = some q → owner j = some q → i = j) ∧
  ∀ j, match owner j with
  | none => enabled active j = false
  | some q => enabled active j = true ∧ q < pos ∧ indices.val[j.val]! = UScalar.hcast .I32 order.val[q]!

theorem refill_owns {digits order ix st active pos ix' st' mask next assigned owner}
    (before : owns order ix active pos.val owner)
    (fill : mapped digits order ix st active pos (ix',st',mask,next,assigned)) :
    ∃ owner', owns order ix' mask next.val owner' ∧
      (∀ j q, owner j = some q → owner' j = some q) ∧
      ∀ q, pos.val ≤ q → q < next.val → ∃! j, owner' j = some q := by
  obtain ⟨oldUnique,oldLane⟩ := before
  obtain ⟨job,le,assignedOnce,newLane⟩ := fill
  let owner' (j : Fin 16) := (job j).orElse (fun _ => owner j)
  have prior (j q) (h : owner j = some q) : job j = none ∧ q < pos.val := by
    have old := oldLane j
    rw [h] at old
    cases eq : job j with
    | none => exact ⟨rfl,old.2.1⟩
    | some k =>
      have new := newLane j
      rw [eq] at new
      simp_all
  have classify (j q) (h : owner' j = some q) :
      (job j = some q ∧ pos.val ≤ q) ∨ (owner j = some q ∧ q < pos.val) := by
    cases eq : job j with
    | none =>
      have old : owner j = some q := by simpa [owner',eq] using h
      exact Or.inr ⟨old,(prior j q old).2⟩
    | some k =>
      have same : k = q := by simpa [owner',eq] using h
      subst k
      have new := newLane j
      rw [eq] at new
      exact Or.inl ⟨rfl,new.1⟩
  refine ⟨owner',⟨?_,?_⟩,?_,?_⟩
  · intro i j q hi hj
    rcases classify i q hi with a|a <;> rcases classify j q hj with b|b
    · have v := newLane i
      rw [a.1] at v
      obtain ⟨_,_,uniq⟩ := assignedOnce q a.2 v.2.1
      exact (uniq i a.1).trans (uniq j b.1).symm
    · omega
    · omega
    · exact oldUnique i j q a.1 b.1
  · intro j
    have n := newLane j
    have o := oldLane j
    cases eq : job j with
    | none =>
      rw [eq] at n
      simp only [owner',eq,Option.orElse_none]
      cases h : owner j with
      | none => rw [h] at o; exact n.2.1.trans o
      | some q =>
        rw [h] at o
        exact ⟨n.2.1.trans o.1,by have := o.2.1; omega,n.2.2.1.trans o.2.2⟩
    | some q =>
      rw [eq] at n
      simpa [owner',eq] using And.intro n.2.2.2.2.1 (And.intro n.2.1 n.2.2.2.2.2.1)
  · intro j q h
    simp [owner',(prior j q h).1,h]
  · intro q lo hi
    obtain ⟨j,hj,unique⟩ := assignedOnce q lo hi
    refine ⟨j,by simp [owner',hj],?_⟩
    intro i h
    rcases classify i q h with a|a
    · exact unique i a.1
    · omega

theorem index_roundtrip (x : Usize) (bound : x.val < 67) :
    (IScalar.hcast .Usize (UScalar.hcast .I32 x)).val = x.val := by
  have first : (UScalar.hcast .I32 x).val = (x.val : Int) :=
    by simpa only [lift,WP.spec_ok] using UScalar.hcast_inBounds_spec .I32 x (by scalar_tac)
  have second : ((IScalar.hcast .Usize (UScalar.hcast .I32 x)).val : Int) = (UScalar.hcast .I32 x).val :=
    by simpa only [lift,WP.spec_ok] using IScalar.hcast_inBounds_spec .Usize (UScalar.hcast .I32 x) (by rw [first]; scalar_tac)
  omega

theorem owned_destinations {digits : Slice U32} {order indices active pos owner}
    (inv : owns order indices active pos owner)
    (ordered : ∀ i < digits.length, order.val[rank digits.val i]!.val = i)
    (bound : pos ≤ digits.length) (small : digits.length ≤ 67) :
    (∀ j, enabled active j = true → outputKey indices j < digits.length) ∧
    ∀ i j, enabled active i = true → enabled active j = true →
      outputKey indices i = outputKey indices j → i = j := by
  obtain ⟨unique,lanes⟩ := inv
  have dest (j) (on : enabled active j = true) :
      ∃ q, owner j = some q ∧ outputKey indices j < digits.length ∧
        rank digits.val (outputKey indices j) = q := by
    have lane := lanes j
    cases h : owner j with
    | none => rw [h] at lane; simp_all
    | some q =>
      rw [h] at lane
      obtain ⟨_,lt,key⟩ := lane
      have atQ := order_at digits order ordered q (by omega)
      refine ⟨q,rfl,?_⟩
      unfold outputKey
      rw [key,index_roundtrip _ (by omega)]
      exact atQ
  refine ⟨fun j on => (dest j on).choose_spec.2.1,?_⟩
  intro i j a b eq
  obtain ⟨q,hi,_,ri⟩ := dest i a
  obtain ⟨r,hj,_,rj⟩ := dest j b
  rw [eq,rj] at ri
  exact unique i j q hi (ri ▸ hj)

theorem remaining_owns {order indices active pos owner} (before : owns order indices active pos owner)
    (next : U16) (subset : ∀ j, enabled next j = true → enabled active j = true) :
    owns order indices next pos (fun j => if enabled next j then owner j else none) := by
  obtain ⟨unique,lanes⟩ := before
  constructor
  · intro i j q hi hj
    dsimp only at hi hj
    split at hi <;> try contradiction
    split at hj <;> try contradiction
    exact unique i j q hi hj
  · intro j
    cases h : enabled next j with
    | false => simp [h]
    | true =>
      have old := lanes j
      have on := subset j h
      cases e : owner j with
      | none => rw [e] at old; simp_all
      | some q =>
        rw [e] at old
        simpa [h,e] using old.2

theorem finish_owned {digits : Slice U32} {order indices active pos owner}
    (inv : owns order indices active pos owner)
    (ordered : ∀ i < digits.length, order.val[rank digits.val i]!.val = i)
    (bound : pos ≤ digits.length) (small : digits.length ≤ 67)
    (N : Usize) (counter : Reg) (hash : Hash) (out : Buffers)
    (shape : N.val=16 ∨ N.val=24 ∨ N.val=32) (rows : digits.length ≤ out.length) :
    finishRound (N := N) counter active hash out indices ⦃ next mask buf =>
      (∀ j, next j = counter j+1) ∧
      (∀ j, enabled mask j = true ↔ enabled active j = true ∧ next j ≠ 15) ∧
      owns order indices mask pos (fun j => if enabled mask j then owner j else none) ∧
      ∃ staged : Staged N, retired indices staged out buf (finishes active counter) ∧
        ∀ j, finishes active counter j → ∀ k < N.val, (staged.val[j.val]!.val[k]!).bv = Store.digestByte hash j k ⦄ := by
  obtain ⟨valid,distinct⟩ := owned_destinations inv ordered bound small
  apply WP.spec_mono (finish_spec counter active hash out indices shape
    (fun j f => Nat.lt_of_lt_of_le (valid j f.1) rows) (fun i j fi fj => distinct i j fi.1 fj.1))
  rintro ⟨next,mask,buf⟩ ⟨counts,bits,writes⟩
  exact ⟨counts,bits,remaining_owns inv mask (fun j h => ((bits j).mp h).1),writes⟩

end slhdsa.X86.Wots
