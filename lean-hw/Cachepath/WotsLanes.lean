import Cachepath.WotsOrder
import Slhdsa.Proofs.ShakeWots

/-! The WOTS lane schedule calls the extracted digit decoder and stable counting sort.
The hash step uses the FIPS function on one lane. The native harness separately checks that
the production packed step submits the right words to the permutation and commits only active
lanes. Scatter is modeled by an indexed table; `WotsScatter` proves the two Rust writers. -/

open Aeneas Aeneas.Std Result slhdsa
namespace CacheopsRust.WotsLanes

/-- The index and value of a lane after one shared permutation, including idle lanes. -/
def advance (p : Spec.Params) (pk : Spec.Bytes) (addr : Spec.Adrs) (stop : Nat)
    (lane : Nat × Spec.Bytes) : Nat × Spec.Bytes :=
  if lane.1 < stop then (lane.1+1, Spec.F p pk {addr with word3 := lane.1} lane.2) else lane

def rounds (p : Spec.Params) (pk : Spec.Bytes) (addr : Spec.Adrs) (start stop : Nat)
    (x : Spec.Bytes) (n : Nat) :=
  (List.range n).foldl (fun lane _ => advance p pk addr stop lane) (start,x)

theorem tracked_lane (p : Spec.Params) (pk : Spec.Bytes) (addr : Spec.Adrs)
    (start stop : Nat) (bound : start ≤ stop) (x : Spec.Bytes) (n : Nat) :
    rounds p pk addr start stop x n =
      (start+min n (stop-start),Spec.chain p x start (min n (stop-start)) pk addr) := by
  induction n with
  | zero => simp [rounds,Spec.chain]
  | succ n ih =>
    rw [rounds,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change advance p pk addr stop (rounds p pk addr start stop x n) = _
    rw [ih]
    by_cases active : n < stop-start
    · simp only [Nat.min_eq_left (Nat.le_of_lt active),Nat.min_eq_left (Nat.succ_le_of_lt active)]
      simp [advance,show start+n < stop by omega,Spec.chain,List.range_succ,Nat.add_assoc]
    · simp [Nat.min_eq_right (by omega : stop-start ≤ n),Nat.min_eq_right (by omega : stop-start ≤ n+1),
        advance,show ¬start+(stop-start)<stop by omega]

/-- The shared loop exits at the longest active chain. Every earlier round has a live lane. -/
theorem loop_termination {width : Nat} (start stop : Fin width → Nat)
    (bound : ∀ i, start i ≤ stop i ∧ stop i ≤ 15) :
    ∃ k ≤ 15, (∀ i, start i + min k (stop i-start i) = stop i) ∧
      ∀ t < k, ∃ i, start i + min t (stop i-start i) < stop i := by
  let k := Finset.univ.sup (fun i => stop i-start i)
  have le (i : Fin width) : stop i-start i ≤ k := Finset.le_sup (f := fun j => stop j-start j) (Finset.mem_univ i)
  refine ⟨k,Finset.sup_le (fun i _ => by have := bound i; omega),?_,?_⟩
  · intro i
    rw [Nat.min_eq_right (le i)]
    have := bound i
    omega
  · intro t ht
    by_contra! no
    have all (i : Fin width) : stop i-start i ≤ t := by
      have h := no i
      have := Nat.min_le_left t (stop i-start i)
      omega
    exact (Nat.not_lt_of_ge (Finset.sup_le (fun i _ => all i))) ht

/-- Scatter active lanes to original chain slots, then serialize those slots in increasing order. -/
def emit (length : Nat) (order : Array Usize 67#usize) (endpoint : Nat → Spec.Bytes) : Spec.Bytes :=
  let table := (List.range length).foldl (fun (t : Nat → Spec.Bytes) slot =>
    let id := order.val[slot]!.val
    Function.update t id (endpoint id)) (fun _ => [])
  (List.range length).flatMap table

private theorem stored (order : List Nat) (endpoint table : Nat → Spec.Bytes) (i : Nat) :
    (order.foldl (fun t j => Function.update t j (endpoint j)) table) i =
      if i ∈ order then endpoint i else table i := by
  induction order generalizing table with
  | nil => simp
  | cons j rest ih =>
    rw [List.foldl_cons,ih]
    by_cases h : i ∈ rest <;> by_cases e : i = j <;> simp [h,e,Function.update]

private theorem emit_eq (n : Nat) (ord : Array Usize 67#usize) (value : Nat → Spec.Bytes)
    (covers : ∀ i < n, ∃ s < n, ord.val[s]!.val = i) :
    emit n ord value = (List.range n).flatMap value := by
  unfold emit
  apply List.flatMap_congr
  intro i hi
  obtain ⟨s,hs,e⟩ := covers i (List.mem_range.mp hi)
  let ids := (List.range n).map fun j => ord.val[j]!.val
  have mem : i ∈ ids := List.mem_map.mpr ⟨s,List.mem_range.mpr hs,e⟩
  have h := stored ids value (fun _ => []) i
  rw [ite_eq_left mem] at h
  simpa only [ids,List.foldl_map] using h

private def run {N : Usize} (m : Array U8 N) (endpoint : List U32 → Nat → Spec.Bytes) :
    Result Spec.Bytes := do
  let digits ← slhdsa.wots.wots_digits m
  let order ← cache.shake_ops.simd.chain_order digits.deref
  ok (emit digits.length order (endpoint digits.val))

private theorem run_eq {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (m : Array U8 N)
    (endpoint : List U32 → Nat → Spec.Bytes) (ref : Nat → Spec.Bytes)
    (eq : ∀ (ds : List U32), nats ds = Spec.wotsDigits (Shake.params p) (bytes m.val) →
      ds.length = (Shake.params p).len → (∀ d ∈ ds, d.val < 16) →
      ∀ i < ds.length, endpoint ds i = ref i) :
    run m endpoint ⦃ out => out = (List.range (Shake.params p).len).flatMap ref ⦄ := by
  unfold run
  let* ⟨digits,ds,hlen,bounded⟩ ← wots_digits_spec p hp m
  have len : digits.length = (Shake.params p).len := hlen.trans hp.len.symm
  have le : digits.deref.length ≤ 67 := by rw [vec_deref_length,hlen]; have := hp.le32; omega
  have small : ∀ i < digits.deref.length, digits.deref.val[i]!.val < 16 := by
    intro i hi
    rw [vec_deref_length] at hi
    rw [vec_deref_val,getElem!_pos digits.val i hi]
    exact bounded _ (List.getElem_mem hi)
  let* ⟨ord,cov,_⟩ ← WotsOrder.chain_order_spec digits.deref le small
  rw [vec_deref_length] at cov
  rw [emit_eq _ _ _ (fun i hi => ⟨_,(cov i hi).1,(cov i hi).2⟩),← len]
  apply List.flatMap_congr
  intro i hi
  exact eq digits.val ds len bounded i (List.mem_range.mp hi)

def sign {N : Usize} (p : slhdsa.params.Params) (m : Array U8 N)
    (sk pk : Spec.Bytes) (a : Spec.Adrs) :=
  let P := Shake.params p
  run m fun ds i =>
    let secret := Spec.PRF P pk sk {Spec.wotsSkAdrs a with word2 := i}
    (rounds P pk {a with word2 := i} 0 ds[i]!.val secret 15).2

theorem sign_spec {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (m : Array U8 N)
    (sk pk : Spec.Bytes) (a : Spec.Adrs) :
    sign p m sk pk a ⦃ out => out = Spec.wotsSign (Shake.params p) (bytes m.val) sk pk a ⦄ := by
  unfold sign Spec.wotsSign
  apply run_eq p hp m _ _
  intro ds digits len small i hi
  have d := small ds[i]! (by rw [getElem!_pos ds i hi]; exact List.getElem_mem hi)
  dsimp only
  rw [tracked_lane _ _ _ _ _ (Nat.zero_le _) _ _]
  simp only [Nat.sub_zero,Nat.min_eq_right (show ds[i]!.val ≤ 15 by omega),← digits,nats_getElem! ds i hi]

def recover {N : Usize} (p : slhdsa.params.Params) (m : Array U8 N) (sig pk : Spec.Bytes) (a : Spec.Adrs) :=
  let P := Shake.params p
  do let endpoints ← run m fun ds i =>
       (rounds P pk {a with word2 := i} ds[i]!.val 15 (Spec.block P sig i) 15).2
     ok (Spec.T P pk (Spec.wotsPkAdrs a) endpoints)

theorem recover_spec {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (m : Array U8 N)
    (sig pk : Spec.Bytes) (a : Spec.Adrs) :
    recover p m sig pk a ⦃ out => out = Spec.wotsPkFromSig (Shake.params p) sig (bytes m.val) pk a ⦄ := by
  unfold recover
  let P := Shake.params p
  let ref := fun i => Spec.chain P (Spec.block P sig i) (Spec.wotsDigits P (bytes m.val))[i]!
    (P.w-1-(Spec.wotsDigits P (bytes m.val))[i]!) pk {a with word2 := i}
  apply WP.spec_bind (run_eq p hp m _ ref ?_)
  · rintro _ rfl
    simp only [WP.spec_ok]
    rfl
  · intro ds digits len small i hi
    have d := small ds[i]! (by rw [getElem!_pos ds i hi]; exact List.getElem_mem hi)
    rw [tracked_lane _ _ _ _ _ (by omega) _ _]
    simp only [ref,P,← digits,nats_getElem! ds i hi,show (Shake.params p).w = 16 from w_eq p,
      Nat.min_eq_right (show 15 - ds[i]!.val ≤ 15 by omega)]

/-- Compare the lane model directly to the bytes returned by the extracted portable signer. -/
theorem sign_eq_scalar {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (m sk seed : Array U8 N) (a : slhdsa.address.Adrs) :
    sign p m (bytes sk.val) (bytes seed.val) (adrsS a) =
      (do let sig ← shake.wots.wots_sign m sk seed a; ok (bytes sig.val)) := by
  obtain ⟨x,hx,ex⟩ := spec_imp_exists (sign_spec p hp m (bytes sk.val) (bytes seed.val) (adrsS a))
  obtain ⟨v,hv,ev,_⟩ := spec_imp_exists (Shake.wots_sign_spec p hp m sk seed a)
  simp only [hx,hv,bind_ok,ex,ev]

/-- All signature slices accepted by the scalar contract yield the same recovered WOTS key. -/
theorem recover_eq_scalar {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sig : Slice U8) (m seed : Array U8 N) (a : slhdsa.address.Adrs)
    (room : N.val*(2*N.val+3) ≤ sig.length) :
    recover p m (bytes sig.val) (bytes seed.val) (adrsS a) =
      (do let key ← shake.wots.wots_pk_from_sig sig m seed a; ok (bytes key.val)) := by
  obtain ⟨x,hx,ex⟩ := spec_imp_exists (recover_spec p hp m (bytes sig.val) (bytes seed.val) (adrsS a))
  obtain ⟨v,hv,ev⟩ := spec_imp_exists (Shake.wots_pk_from_sig_spec p hp sig m seed a room)
  simp only [hx,hv,bind_ok,ex,ev]

end CacheopsRust.WotsLanes
