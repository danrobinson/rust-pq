import Cachepath.WotsLanes

open Aeneas Aeneas.Std Result slhdsa
namespace CacheopsRust.WotsLanes
open slhdsa.Shake

theorem block_reject {N : Usize} (sig : Slice U8) (i : Usize)
    (room : (i.val+1)*N.val ≤ Usize.max) (truncated : sig.length < (i.val+1)*N.val) :
    util.block N sig i = fail .panic := by
  rw [Nat.add_mul,Nat.one_mul] at room truncated
  obtain ⟨lo,mul,loe⟩ := spec_imp_exists (Usize.mul_spec (x:=i) (y:=N) (by omega))
  obtain ⟨hi,add,hie⟩ := spec_imp_exists (Usize.add_spec (x:=lo) (y:=N) (by omega))
  have bad : ¬(lo.val ≤ hi.val ∧ hi.val ≤ sig.val.length) := by change ¬(_ ∧ hi.val ≤ sig.length); omega
  simp [util.block,lift,mul,add,Array.to_slice_mut,core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeUsizeSlice.index,bad]

private theorem reject_loop {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sig : Slice U8) (seed : Array U8 N) (a : slhdsa.address.Adrs)
    (ds : alloc.vec.Vec U32) (len : ds.length = 2*N.val+3) (valid : ∀ d ∈ ds.val, d.val<16)
    (short : sig.length < ds.length*N.val) (s : slhdsa.shake256.Sponge)
    (x : Spec.Bytes) (hs : Absorbed s x) (i : Usize) (live : i.val < ds.length) :
    shake.wots.wots_pk_from_sig_loop sig seed a.layer a.tree a.typ a.keypair a.word2 a.word3 ds s i =
      fail .panic := by
  have lt : i < alloc.vec.Vec.len ds := live
  have hn := hp.le32
  by_cases readable : (i.val+1)*N.val ≤ sig.length
  · have stepok : shake.wots.wots_pk_from_sig_loop.body sig seed a.layer a.tree a.typ a.keypair a.word2 a.word3 ds s i
        ⦃ out => ∃ (s' : slhdsa.shake256.Sponge) (j : Usize) (xs : Spec.Bytes),
          out = .cont (s',j) ∧ j.val = i.val+1 ∧ Absorbed s' xs ⦄ := by
      simp only [shake.wots.wots_pk_from_sig_loop.body,lt,ite_true]
      let* ⟨start,_⟩ ← block_spec N sig i readable
      simp only [lift,bind_ok]
      let* ⟨addr,_⟩ ← with_word2_spec
      let* ⟨d,hidx⟩ ← alloc.vec.Vec.index_usize_spec
      simp only [W_eq]
      let* ⟨last,hend⟩ ← U32.sub_spec
      have dvalid : d.val ≤ last.val := by
        rw [hidx]
        have := valid _ (List.getElem_mem (l:=ds.val) live)
        scalar_tac
      let* ⟨val,_⟩ ← chain_spec p hp start seed addr d last dvalid
      let* ⟨s',h⟩ ← append_spec s _ hs
      let* ⟨j,hj⟩ ← Usize.add_spec
      exact ⟨s',j,_,rfl,hj,h⟩
    obtain ⟨_,eq,s',j,xs,rfl,hj,h⟩ := spec_imp_exists stepok
    have more : j.val < ds.length := by
      by_contra! no
      have e : ds.length = i.val+1 := by omega
      rw [e] at short
      omega
    unfold shake.wots.wots_pk_from_sig_loop
    conv_lhs => rw [loop.eq_def]
    simp only [eq,bind_ok]
    exact reject_loop p hp sig seed a ds len valid short s' xs h j more
  · have small : (i.val+1)*N.val ≤ Usize.max := by
      have : i.val+1 ≤ 67 := by omega
      exact le_trans (Nat.mul_le_mul this hn) (by scalar_tac)
    have bad := block_reject sig i small (Nat.lt_of_not_ge readable)
    unfold shake.wots.wots_pk_from_sig_loop
    conv_lhs => rw [loop.eq_def]
    simp only [shake.wots.wots_pk_from_sig_loop.body,lt,ite_true,bad,bind_fail]
termination_by ds.length - i.val
decreasing_by omega

/-- The extracted portable WOTS verifier reaches the first missing block and returns Rust's panic. -/
theorem scalar_reject {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sig : Slice U8) (m seed : Array U8 N) (a : slhdsa.address.Adrs)
    (short : sig.length < N.val*(2*N.val+3)) :
    shake.wots.wots_pk_from_sig sig m seed a = fail .panic := by
  obtain ⟨ds,run,_,len,valid⟩ := spec_imp_exists (wots_digits_spec p hp m)
  obtain ⟨a0,e0,_⟩ := spec_imp_exists (with_type_spec a slhdsa.address.WOTS_PK)
  obtain ⟨a1,e1,_⟩ := spec_imp_exists (with_keypair_spec a0 a.keypair)
  obtain ⟨s,es,hs⟩ := spec_imp_exists (start_spec seed a1)
  have bad := reject_loop p hp sig seed a ds len valid (by rwa [len,Nat.mul_comm]) s _ hs 0#usize (by simp [len])
  simp only [shake.wots.wots_pk_from_sig,run,e0,e1,es,bind_ok,bad,bind_fail]

/-- Replay the accessible signature-block reads of a sorted batch schedule. -/
def readSchedule (N : Usize) (sig : Slice U8) : List Usize → Result Unit
  | [] => ok ()
  | id :: ids => do
    let _ ← util.block N sig id
    readSchedule N sig ids

theorem readSchedule_eq (N : Usize) (sig : Slice U8) (ids : List Usize)
    (room : ∀ id ∈ ids, (id.val+1)*N.val ≤ Usize.max) :
    readSchedule N sig ids = if ids.all (fun id => decide ((id.val+1)*N.val ≤ sig.length)) then ok () else fail .panic := by
  induction ids with
  | nil => rfl
  | cons id ids ih =>
    simp only [readSchedule,List.all_cons]
    by_cases accessible : (id.val+1)*N.val ≤ sig.length
    · obtain ⟨b,e,_⟩ := spec_imp_exists (block_spec N sig id accessible)
      simpa only [e,bind_ok,decide_eq_true accessible,Bool.true_and] using ih (by
        intro j h; exact room j (List.mem_cons_of_mem _ h))
    · have e := block_reject sig id (room id (by simp)) (Nat.lt_of_not_ge accessible)
      simp [e,accessible]

def sortedReads {N : Usize} (m : Array U8 N) (sig : Slice U8) : Result Unit := do
  let digits ← wots.wots_digits m
  let order ← cache.shake_ops.simd.chain_order digits.deref
  readSchedule N sig ((List.range digits.length).map (fun j => order.val[j]!))

theorem sortedReads_eq {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (m : Array U8 N) (sig : Slice U8) :
    sortedReads m sig = if N.val*(2*N.val+3) ≤ sig.length then ok () else fail .panic := by
  obtain ⟨ds,digits,_,hlen,valid⟩ := spec_imp_exists (wots_digits_spec p hp m)
  have hn := hp.le32
  have hsize : ds.deref.length ≤ 67 := by rw [vec_deref_length,hlen]; omega
  have small : ∀ i < ds.deref.length, ds.deref.val[i]!.val<16 := by
    intro i hi
    rw [vec_deref_length] at hi
    rw [vec_deref_val,getElem!_pos ds.val i hi]
    exact valid _ (List.getElem_mem hi)
  obtain ⟨ord,order,covers,inside⟩ := spec_imp_exists (WotsOrder.chain_order_spec ds.deref hsize small)
  rw [vec_deref_length] at covers inside
  let ids := (List.range ds.length).map (fun j => ord.val[j]!)
  have inRange : ∀ id ∈ ids, id.val < ds.length := by
    intro id hit
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hit
    obtain ⟨i,hi,_,e⟩ := inside j (List.mem_range.mp hj)
    exact e ▸ hi
  have bounded : ∀ id ∈ ids, (id.val+1)*N.val ≤ Usize.max := by
    intro id hi
    have := inRange id hi
    exact le_trans (Nat.mul_le_mul (show id.val+1 ≤ 67 by omega) hn) (by scalar_tac)
  have full : (ids.all (fun id => decide ((id.val+1)*N.val ≤ sig.length))) = true ↔
      N.val*(2*N.val+3) ≤ sig.length := by
    simp only [List.all_eq_true,decide_eq_true_eq]
    constructor
    · intro h
      have last : ds.length-1 < ds.length := by omega
      obtain ⟨hj,he⟩ := covers _ last
      have hit : ord.val[WotsOrder.rank ds.deref.val (ds.length-1)]! ∈ ids :=
        List.mem_map.mpr ⟨_,List.mem_range.mpr hj,rfl⟩
      have enough := h _ hit
      rw [he,show ds.length-1+1 = ds.length by omega,hlen,Nat.mul_comm] at enough
      exact enough
    · intro enough id hi
      have hlen' : id.val+1 ≤ 2*N.val+3 := by have := inRange id hi; omega
      exact le_trans (Nat.mul_le_mul_right _ hlen') ((Nat.mul_comm ..) ▸ enough)
  simp only [sortedReads,digits,order,bind_ok]
  rw [show (List.range ds.length).map (fun j => ord.val[j]!) = ids from rfl,readSchedule_eq N sig ids bounded]
  simp only [propext full]

/-- Model recovery with the Rust block reads in stable sorted order, including truncated signatures. -/
def checkedRecover {N : Usize} (p : slhdsa.params.Params) (sig : Slice U8) (m seed : Array U8 N)
    (a : slhdsa.address.Adrs) : Result Spec.Bytes := do
  sortedReads m sig
  recover p m (bytes sig.val) (bytes seed.val) (adrsS a)

theorem checkedRecover_eq_scalar {N : Usize} (p : slhdsa.params.Params) (hp : PN p N)
    (sig : Slice U8) (m seed : Array U8 N) (a : slhdsa.address.Adrs) :
    checkedRecover p sig m seed a =
      (do let key ← shake.wots.wots_pk_from_sig sig m seed a; ok (bytes key.val)) := by
  rw [checkedRecover,sortedReads_eq p hp]
  split <;> rename_i h
  · simpa only [bind_ok] using recover_eq_scalar p hp sig m seed a h
  · simp only [bind_fail,scalar_reject p hp sig m seed a (Nat.lt_of_not_ge h)]

end CacheopsRust.WotsLanes
