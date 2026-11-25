import Armwide.NativeWotsProgram
import Slhdsa.Proofs.Util

open Aeneas Aeneas.Std Result
namespace slhdsa.Armwide.Public
set_option maxHeartbeats 1000000

private theorem fused_spec {N : Usize} (p : params.Params) (hp : PN p N)
    (m sk : Array U8 N) (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs)
    (ds : Slice U32) (out : Slice U8) (size : ds.length=(paramsS p).len)
    (digs : nats ds.val = Spec.wotsDigits (paramsS p) (bytes m.val))
    (bounded : ∀ i < ds.length, ds.val[i]!.val ≤ 15) (room : out.length = ds.length*N.val)
    (empty : out.val = List.replicate out.length 0#u8) :
    sha256.arm_wide.wots_sign_fused seed.state sk a ds out ⦃ r => bytes r.val =
      Spec.wotsSign (paramsS p) (bytes m.val) (bytes sk.val) (bytes seed.pk_seed.val) (hashAddress (slhdsa.adrsS a)) ⦄ := by
  have cap : ds.length ≤ 67 := by have := hp.le32; rw [size,hp.len]; omega
  unfold sha256.arm_wide.wots_sign_fused
  step with SignOrder.sort_spec ds cap bounded as ⟨sorted,nd,covers⟩
  let order := (sorted.val.take ds.length).map (·.val)
  let digit := fun (i : Nat) => ds.val[i]!.val
  let base := hashAddress (slhdsa.adrsS a)
  have st : wv seed.state.val = seedState (paramsS p).n (bytes seed.pk_seed.val) := by rw [hp.n]; exact hs.1
  have native := Transitions.native_sign_scheduler (paramsS p) hp.valid (bytes seed.pk_seed.val) (bytes sk.val)
    (by rw [hp.n]; simp) (by rw [hp.n]; simp) base digit ds.length cap order bounded nd covers
  let row := signRows N.val (wv seed.state.val) (bytes sk.val) (slhdsa.adrsS a) digit order
  have rows : (List.range ds.length).flatMap row =
      Spec.wotsSign (paramsS p) (bytes m.val) (bytes sk.val) (bytes seed.pk_seed.val) base := by
    simp only [Spec.wotsSign,←size]
    apply List.flatMap_congr
    intro i mem
    have hi := List.mem_range.mp mem
    have h := native i hi
    have dig : digit i = (Spec.wotsDigits (paramsS p) (bytes m.val))[i]! := by
      rw [←digs]
      change ds.val[i]!.val = (ds.val.map (·.val))[i]!
      rw [getElem!_pos (ds.val.map (·.val)) i (by simp; exact hi),List.getElem_map,getElem!_pos ds.val i hi]
    unfold row signRows
    rw [Transitions.initialized_eq,st,←hp.n]
    unfold WotsRefill.wotsSignTarget at h
    simpa only [dig] using h
  have sizes : ∀ i < ds.length, (row i).length=N.val := by
    intro i hi
    unfold row signRows
    rw [Transitions.initialized_eq,st,←hp.n,native i hi]
    unfold WotsRefill.wotsSignTarget
    apply Spec.chain_length _ hp.valid _ (Spec.PRF_length _ hp.valid ..)
  have zero : bytes out.val = List.replicate (ds.length*N.val) 0#8 := by rw [empty,bytes_replicate,room]; rfl
  simp only [Slice.from_val,bytes,List.map_map,Function.comp_def,List.map_id_fun,List.map_id]
  rw [show List.map (fun x : U8 => x.bv) out.val = _ from zero,Transitions.buffer_sign_table _ _ _ _ _ _ _ hp.nok]
  change List.map id (Transitions.encode N.val ds.length row) = _
  rw [List.map_id,Transitions.encode_done _ _ _ sizes]
  exact rows

/-- The production Arm signing entry, including allocation, embedded Rust digit sort,
native register hashing and the returned buffer, matches FIPS WOTS+. -/
theorem sign_spec {N : Usize} (p : params.Params) (hp : PN p N) (m sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) :
    wots.arm.sign m sk seed a ⦃ r =>
      bytes r.val = Spec.wotsSign (paramsS p) (bytes m.val) (bytes sk.val) (bytes seed.pk_seed.val)
        (hashAddress (slhdsa.adrsS a)) ⦄ := by
  have bound := hp.le32
  unfold wots.arm.sign
  simp only [LEN2_eq]
  let* ⟨i,hi⟩ ← Usize.mul_spec
  let* ⟨len,hl⟩ ← Usize.add_spec
  have length : len.val = (paramsS p).len := by rw [hp.len,hl,hi]
  have cap : len.val ≤ 67 := by rw [length,hp.len]; omega
  step with wots_digits_stack_spec (paramsS p) hp.valid hp.n m as ⟨digits,hv,hb⟩
  let* ⟨sz,hsz⟩ ← Usize.mul_spec
  step*
  have se : s.val = digits.val.take len.val := by simpa [List.slice,Array.val_to_slice] using s_post
  have eq : nats s.val = Spec.wotsDigits (paramsS p) (bytes m.val) := by rw [se,length,hp.len]; exact hv
  have small : ∀ j < s.length, s.val[j]!.val ≤ 15 := by
    intro j hj
    have hj' : j < 2*N.val+3 := by rwa [s_post1,length,hp.len] at hj
    have h := hb j hj'
    rw [getElem!_pos _ _ (by simp; omega)] at h
    rw [se,getElem!_pos _ _ (by rw [←se]; exact hj),List.getElem_take]; omega
  simp only [alloc.vec.Vec.deref_mut,lift,bind_ok]
  step with fused_spec p hp m sk seed hs a s _ (s_post1.trans length) eq small (by change sig.length=_; rw [sig_post1,hsz,s_post1])
    (by change sig.val = List.replicate sig.length 0#u8; rw [sig_post,sig_post1]) as ⟨r,hr⟩
  exact hr

/-- XMSS invokes the wide entry with a WOTS_HASH address whose two scratch words
are zero. Its returned Rust vector equals the reference WOTS signing entry. -/
theorem sign_eq_scalar {N : Usize} (p : params.Params) (hp : PN p N) (m sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs)
    (reachable : hashAddress (slhdsa.adrsS a) = slhdsa.adrsS a) :
    wots.arm.sign m sk seed a = slhdsa.wots.wots_sign m sk seed a := by
  obtain ⟨native,hn,pn⟩ := spec_imp_exists (sign_spec p hp m sk seed hs a)
  obtain ⟨scalar,hr,pr,_⟩ := spec_imp_exists (wots_sign_spec p hp m sk seed hs a)
  rw [reachable] at pn
  rw [hn,hr]
  congr 1
  exact alloc.vec.Vec.ext _ _ ((bytes_inj _ _).mp (pn.trans pr.symm))

end slhdsa.Armwide.Public
