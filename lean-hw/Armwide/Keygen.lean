import Armwide.KeygenProgram
import Slhdsa.Proofs.Util

open Aeneas Aeneas.Std Result
namespace slhdsa.Armwide.Keygen
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem filled_size (n : Nat) (width : n=16 ∨ n=24 ∨ n=32) (msg : Spec.Bytes) (size : msg.length=payLen n) :
    (filled n msg).length=total n := by
  simp only [filled,List.length_append,List.length_replicate,size]
  rcases width with rfl|rfl|rfl <;> decide

theorem compress_tlen_spec [cpu : Features] {N : Usize} (p : params.Params) (hp : PN p N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (buf : Slice U8) (len : Usize)
    (msg : Spec.Bytes) (data : slhdsa.bytes buf.val=filled N.val msg) (size : msg.length=payLen N.val)
    (chains : len.val=2*N.val+3) :
    wots.arm.compress_tlen_1 seed a buf len ⦃ result =>
      slhdsa.bytes result.1.val = Spec.T (paramsS p) (slhdsa.bytes seed.pk_seed.val)
        (Spec.wotsPkAdrs (slhdsa.adrsS a)) msg ⦄ := by
  let P := paramsS p
  have buf_size : buf.length=total N.val := by
    have h := congrArg List.length data
    rw [slhdsa.bytes_length,filled_size N.val hp.nok msg size] at h
    exact h
  have st : wv seed.state.val=seedState P.n (slhdsa.bytes seed.pk_seed.val) := by rw [hp.n]; exact hs.1
  have wide (large : P.n ≠ 16) : S512.wv seed.state512.val=H512.Multi.pkState512 P.n (slhdsa.bytes seed.pk_seed.val) := by
    rw [hp.n] at large ⊢
    simpa only [H512.Multi.pkState512,toByte_zero] using hs.2 large
  have h := compression_T P hp.valid (slhdsa.bytes seed.pk_seed.val) msg (by rw [hp.n]; simp)
    (by rw [hp.n]; exact size) (slhdsa.adrsS a) cpu.sha512 _ wide
  rw [hp.n] at h st
  unfold wots.arm.compress_tlen_1
  have guard : (decide (len.val≠2*N.val+3) || decide (buf.length≠total N.val)) = false := by simp [chains,buf_size]
  simp only [guard,Bool.false_eq_true,↓reduceIte,data,st,h]
  have correct := Spec.T_length P hp.valid (slhdsa.bytes seed.pk_seed.val) (Spec.wotsPkAdrs (slhdsa.adrsS a)) msg
  rw [hp.n] at correct
  split
  · simp only [WP.spec_ok,Array.from_val,slhdsa.bytes,List.map_map,Function.comp_def]
    exact List.map_id _
  · rename_i nope
    exact False.elim (nope correct)

private theorem endpoints_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (buf : Slice U8)
    (zero : buf.val=List.replicate (total N.val) 0#u8) :
    sha256.arm_wide.wots_endpoints_1 seed.state sk a buf ⦃ out =>
      slhdsa.bytes out.val = filled N.val (payload (paramsS p) (slhdsa.bytes seed.pk_seed.val) (slhdsa.bytes sk.val)
        (slhdsa.adrsS a) (2*N.val+3)) ∧ out.length=total N.val ⦄ := by
  let P:=paramsS p
  have st : wv seed.state.val=seedState P.n (slhdsa.bytes seed.pk_seed.val) := by rw [hp.n]; exact hs.1
  have bound : 22+payLen N.val ≤ total N.val := by rcases hp.nok with h|h|h <;> rw [h] <;> decide
  have room : buf.length = total N.val := by change buf.val.length=_; rw [zero,List.length_replicate]
  have good := written P hp.valid (slhdsa.bytes seed.pk_seed.val) (slhdsa.bytes sk.val)
    (by rw [hp.n];simp) (by rw [hp.n];simp) (slhdsa.adrsS a) (total N.val) (by rw [hp.n];exact bound)
  rw [hp.n] at good st
  unfold sha256.arm_wide.wots_endpoints_1
  simp only [room,not_lt_of_ge bound,↓reduceIte,WP.spec_ok,Slice.from_val,Slice.length,slhdsa.bytes,List.map_map,Function.comp_def]
  rw [st,show List.map (fun x : U8 => x.bv) buf.val=List.replicate (total N.val) 0#8 by
    rw [zero,List.map_replicate]; rfl]
  simp only [List.length_map]
  change List.map id _ = _ ∧ _
  rw [List.map_id,write_size,List.length_replicate]
  exact ⟨good,rfl⟩

private theorem allocated [Features] {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (len L : Usize)
    (chains : len.val=2*N.val+3) (geom : L.val=total N.val) :
    (do let buf := Array.repeat L 0#u8
        let (s,back) ← lift (Array.to_slice_mut buf)
        let written ← sha256.arm_wide.wots_endpoints_1 seed.state sk a s
        let (s2,_) ← lift (Array.to_slice_mut (back written))
        let (r,_) ← wots.arm.compress_tlen_1 seed a s2 len
        ok r) ⦃ r => slhdsa.bytes r.val = Spec.wotsPkGen (paramsS p) (slhdsa.bytes sk.val)
          (slhdsa.bytes seed.pk_seed.val) (hashAddr (slhdsa.adrsS a)) ⦄ := by
  let P := paramsS p
  let payload_ := payload P (slhdsa.bytes seed.pk_seed.val) (slhdsa.bytes sk.val) (slhdsa.adrsS a) (2*N.val+3)
  simp only [Array.to_slice_mut,lift,bind_ok]
  let arr := Array.repeat L 0#u8
  have zero : arr.to_slice.val = List.replicate (total N.val) 0#u8 := by rw [Array.val_to_slice,Array.repeat_val,geom]
  step with endpoints_spec p hp sk seed hs a arr.to_slice zero as ⟨r,data,size⟩
  have len' : r.val.length=L.val := by rw [geom]; exact size
  step with compress_tlen_spec p hp seed hs a (Array.from_slice arr r).to_slice len payload_ (by rw [Array.val_to_slice,Array.from_slice_val _ _ len']; exact data)
    (by unfold payload_; rw [payload_size P hp.valid,hp.n]; rfl) chains as ⟨z,back,value⟩
  rw [value]
  unfold Spec.wotsPkGen
  simp only [hp.len,show (paramsS p).w=16 from by simp [Spec.Params.w,hp.valid.lgw_eq],Nat.reduceSub]
  rfl

/-- The production Arm single-key WOTS keygen wrapper returns its FIPS Algorithm 6
public key for either result of SHA-512 feature detection and every supported width. -/
theorem pk_gen_spec [Features] {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) :
    wots.arm.pk_gen sk seed a ⦃ r => slhdsa.bytes r.val =
      Spec.wotsPkGen (paramsS p) (slhdsa.bytes sk.val) (slhdsa.bytes seed.pk_seed.val) (hashAddr (slhdsa.adrsS a)) ⦄ := by
  have small := hp.le32
  unfold wots.arm.pk_gen
  simp only [LEN2_eq]
  let* ⟨i,hi⟩ ← Usize.mul_spec
  let* ⟨len,hl⟩ ← Usize.add_spec
  have chains : len.val=2*N.val+3 := by rw [hl,hi]
  split
  · rename_i n
    apply allocated p hp sk seed hs a len 640#usize chains
    rw [n]; rfl
  · split
    · rename_i n
      apply allocated p hp sk seed hs a len 1280#usize chains
      rw [n]; rfl
    · rename_i n24
      apply allocated p hp sk seed hs a len 2304#usize chains
      have n : N.val=32 := by
        rcases hp.nok with h|h|h
        · exact False.elim (by rename_i n16; apply n16; exact by scalar_tac)
        · exact False.elim (n24 (by scalar_tac))
        · exact h
      rw [n]; rfl

theorem pk_gen_eq_scalar [Features] {N : Usize} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (reachable : hashAddr (slhdsa.adrsS a)=slhdsa.adrsS a) :
    wots.arm.pk_gen sk seed a = slhdsa.wots.wots_pk_gen sk seed a := by
  obtain ⟨x,hx,xs⟩ := spec_imp_exists (pk_gen_spec p hp sk seed hs a)
  obtain ⟨y,hy,ys⟩ := spec_imp_exists (wots_pk_gen_spec p hp sk seed hs a)
  rw [reachable] at xs
  rw [hx,hy,ok.injEq]
  exact Aeneas.Std.Array.ext _ _ ((bytes_inj _ _).mp (xs.trans ys.symm))

end slhdsa.Armwide.Keygen
