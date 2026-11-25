import Armwide.RecoveryRows
import Armwide.Keygen
import Armwide.Encoders
open Aeneas Aeneas.Std Result
namespace slhdsa.Armwide.Recovery
open WotsRefill
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option linter.concreteInstances false

def payload (p : Spec.Params) (pk sig msg : Spec.Bytes) (a : Spec.Adrs) := (List.range p.len).flatMap
  (ends p pk a (Spec.block p sig) (fun i => (Spec.wotsDigits p msg)[i]!))

private theorem payload_len {N : Usize} (p : params.Params) (hp : PN p N) (sig : Slice U8) (m pk : Spec.Bytes)
    (a : Spec.Adrs) (fits : (2*N.val+3)*N.val≤sig.length) :
    (payload (paramsS p) pk (slhdsa.bytes sig.val) m a).length=Keygen.payLen N.val := by
  unfold payload
  rw [←Transitions.encode_done (paramsS p).n _ _ _,encode_size,hp.n,hp.len]
  · rfl
  · intro j hj
    apply Spec.chain_length _ hp.valid
    unfold Spec.block
    rw [hp.n]
    exact sig_row_size N.val sig _ fits j (hp.len ▸ hj)

private theorem fused {N : Usize} (p : params.Params) (hp : PN p N) (sig : Slice U8) (m : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (ds : Slice U32)
    (count : ds.length=2*N.val+3) (digits : nats ds.val=Spec.wotsDigits (paramsS p) (slhdsa.bytes m.val))
    (valid : ∀ i<ds.length, digit ds i≤15) (fits : ds.length*N.val≤sig.length)
    (buf : Slice U8) (zero : buf.val=List.replicate (Keygen.total N.val) 0#u8) :
    sha256.arm_wide.wots_recover N seed.state a sig ds buf ⦃ out =>
      slhdsa.bytes out.val=Keygen.filled N.val (payload (paramsS p) (slhdsa.bytes seed.pk_seed.val) (slhdsa.bytes sig.val)
        (slhdsa.bytes m.val) (slhdsa.adrsS a)) ∧ out.length=Keygen.total N.val ⦄ := by
  let P := paramsS p
  let pk := slhdsa.bytes seed.pk_seed.val
  have cap : ds.length≤67 := by have := hp.le32;omega
  unfold sha256.arm_wide.wots_recover
  step with prepare_spec N hp.nok ds sig buf count valid fits zero as ⟨weights,b,ws,framed,blen⟩
  step as ⟨s,rows,len⟩
  have part : s.val=weights.val.take ds.length := by simpa [List.slice,Array.val_to_slice] using rows
  change s.length=ds.length at len
  have w (i : Nat) (hi : i<s.length) : s.val[i]!.val=15-digit ds i := by
    have h := ws i (len ▸ hi)
    rw [part,getElem!_pos _ _ (by rw [←part];exact hi),List.getElem_take]
    rw [getElem!_pos weights.val i (by simp;omega)] at h
    exact h
  step with sort_descending_spec s (Array.repeat 67#usize 0#u8) (by omega) (by intro j hj; rw [w j hj];omega)
    as ⟨sorted,_,orderLen,unique,members,_⟩
  let order := (sorted.2.val.take sorted.1.val).map (·.val)
  have membership (j : Nat) : j∈order ↔ j<ds.length ∧ digit ds j<15 := by
    rw [members]
    constructor
    · rintro ⟨lt,gt⟩;rw [w j lt] at gt;exact ⟨by omega,by omega⟩
    · rintro ⟨lt,lt15⟩;have sl : j<s.length := by omega
      exact ⟨sl,by rw [w j sl];omega⟩
  have st : wv seed.state.val=seedState P.n pk := by rw [hp.n];exact hs.1
  have allDigits (i : Nat) (bound : i<ds.length) :
      digit ds i=(Spec.wotsDigits P (slhdsa.bytes m.val))[i]! := by
    rw [←digits]
    change ds.val[i]!.val = (ds.val.map (·.val))[i]!
    rw [getElem!_pos (ds.val.map (·.val)) i (by simp;exact bound),List.getElem_map,getElem!_pos ds.val i bound]
  have init : slhdsa.bytes b.val=frame P.n ds.length (fun c => if digit ds c=15 then signatureRow P.n sig c else []) := by
    rw [hp.n,framed]
    exact frame_congr _ _ _ _ (fun j hj => by simp [copied,hj])
  have computed := complete_fips P hp.valid pk (by rw [hp.n];simp [pk]) (slhdsa.adrsS a)
    (signatureRow P.n sig) (digit ds) order ds.length cap
    (fun i hi => sig_row_size _ _ _ (hp.n ▸ fits) _ hi) valid unique membership _ init
  have native : completeRows N.val (wv seed.state.val) (slhdsa.adrsS a) (signatureRow N.val sig) (digit ds)
        order (slhdsa.bytes b.val)=Keygen.filled N.val (payload P pk (slhdsa.bytes sig.val) (slhdsa.bytes m.val) (slhdsa.adrsS a)) := by
    rw [show P.n=N.val from hp.n] at computed
    rw [show P.n=N.val from hp.n] at st
    rw [st]
    refine computed.trans (congrArg (Keygen.filled N.val) ?_)
    unfold payload
    have l : ds.length=P.len := count.trans hp.len.symm
    rw [l]
    apply List.flatMap_congr
    intro j hj
    unfold ends
    simp only [allDigits j (l ▸ List.mem_range.mp hj),signatureRow,Spec.block,show P.n=N.val from hp.n]
  have extent : (payload P pk (slhdsa.bytes sig.val) (slhdsa.bytes m.val) (slhdsa.adrsS a)).length=Keygen.payLen N.val :=
    payload_len p hp sig _ _ _ (count ▸ fits)
  have size : (Keygen.filled N.val (payload P pk (slhdsa.bytes sig.val) (slhdsa.bytes m.val) (slhdsa.adrsS a))).length=Keygen.total N.val := by
    simp only [Keygen.filled,List.length_append,List.length_replicate,extent]
    rcases hp.nok with h|h|h <;> rw [h] <;> decide
  split
  · rename_i none
    have empty : order=[] := by simp [order,none]
    rw [empty] at native
    rw [WP.spec_ok]
    exact ⟨native,blen⟩
  · have fits' : (completeRows N.val (wv seed.state.val) (slhdsa.adrsS a) (signatureRow N.val sig) (digit ds)
        order (slhdsa.bytes b.val)).length≤Usize.max := by rw [native,size,←blen];exact b.property
    split
    · rw [WP.spec_ok]
      simp only [Slice.from_val,Slice.length,slhdsa.bytes,List.map_map,Function.comp_def,List.length_map]
      refine ⟨(List.map_id _).trans native,(congrArg List.length native).trans size⟩
    · rename_i bad
      exact False.elim (bad fits')

private theorem allocated [Keygen.Features] {N : Usize} (p : params.Params) (hp : PN p N)
    (sig : Slice U8) (m : Array U8 N) (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs)
    (len L : Usize) (chains : len.val=2*N.val+3) (geom : L.val=Keygen.total N.val)
    (digits : Array U32 67#usize)
    (hv : nats (digits.val.take (2*N.val+3))=Spec.wotsDigits (paramsS p) (slhdsa.bytes m.val))
    (hb : ∀ j<2*N.val+3,digits.val[j]!.val<16) (fits : (2*N.val+3)*N.val≤sig.length) :
    (do let arr := Array.repeat L 0#u8
        let s ← core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice U32)) digits ⟨len⟩
        let (b,back) ← lift (Array.to_slice_mut arr)
        let written ← sha256.arm_wide.wots_recover N seed.state a sig s b
        let (b2,_) ← lift (Array.to_slice_mut (back written))
        let (r,_) ← Keygen.wots.arm.compress_tlen_1 seed a b2 len
        ok r) ⦃ r => slhdsa.bytes r.val=Spec.wotsPkFromSig (paramsS p) (slhdsa.bytes sig.val)
          (slhdsa.bytes m.val) (slhdsa.bytes seed.pk_seed.val) (slhdsa.adrsS a) ⦄ := by
  have cap := hp.le32
  step as ⟨s,rows,count⟩
  have se : s.val=digits.val.take len.val := by simpa [List.slice,Array.val_to_slice] using rows
  have count' : s.length=2*N.val+3 := count.trans chains
  have value : nats s.val=Spec.wotsDigits (paramsS p) (slhdsa.bytes m.val) := by rw [se,chains];exact hv
  have small (j : Nat) (hj : j<s.length) : digit s j≤15 := by
    have h := hb j (count' ▸ hj)
    rw [getElem!_pos digits.val j (by simp;omega)] at h
    unfold digit
    rw [se,getElem!_pos _ _ (by rw [←se];exact hj),List.getElem_take];omega
  simp only [Array.to_slice_mut,lift,bind_ok]
  let arr := Array.repeat L 0#u8
  have zero : arr.to_slice.val=List.replicate (Keygen.total N.val) 0#u8 := by rw [Array.val_to_slice,Array.repeat_val,geom]
  step with fused p hp sig m seed hs a s count' value small (count' ▸ fits) arr.to_slice zero as ⟨r,data,size⟩
  have same : r.val.length=L.val := by rw [geom];exact size
  step with Keygen.compress_tlen_spec p hp seed hs a (Array.from_slice arr r).to_slice len _
    (by rw [Array.val_to_slice,Array.from_slice_val _ _ same];exact data)
    (payload_len p hp sig _ _ _ fits) chains as ⟨z,back,correct⟩
  rw [correct]
  simp only [Spec.wotsPkFromSig,payload,show (paramsS p).w=16 from by simp [Spec.Params.w],Nat.reduceSub]
  rfl

theorem recover_spec [Keygen.Features] {N : Usize} (p : params.Params) (hp : PN p N)
    (sig : Slice U8) (m : Array U8 N) (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs)
    (fits : N.val*(2*N.val+3)≤sig.length) :
    wots.arm.recover sig m seed a ⦃ r => slhdsa.bytes r.val=Spec.wotsPkFromSig (paramsS p)
      (slhdsa.bytes sig.val) (slhdsa.bytes m.val) (slhdsa.bytes seed.pk_seed.val) (slhdsa.adrsS a) ⦄ := by
  have bound := hp.le32
  rw [Nat.mul_comm] at fits
  unfold wots.arm.recover
  simp only [LEN2_eq]
  let* ⟨i,hi⟩ ← Usize.mul_spec
  let* ⟨len,hl⟩ ← Usize.add_spec
  have chains : len.val=2*N.val+3 := by rw [hl,hi]
  step with wots_digits_stack_spec (paramsS p) hp.valid hp.n m as ⟨digits,hv,hb⟩
  split
  · rename_i n
    exact allocated p hp sig m seed hs a len 640#usize chains (by rw [n];rfl) digits hv hb fits
  · split
    · rename_i n
      exact allocated p hp sig m seed hs a len 1280#usize chains (by rw [n];rfl) digits hv hb fits
    · rename_i n24
      have n : N.val=32 := by
        rcases hp.nok with h|h|h
        · exact False.elim (by rename_i n16;apply n16;scalar_tac)
        · exact False.elim (n24 (by scalar_tac))
        · exact h
      exact allocated p hp sig m seed hs a len 2304#usize chains (by rw [n];rfl) digits hv hb fits

theorem recover_eq_scalar [Keygen.Features] {N : Usize} (p : params.Params) (hp : PN p N)
    (sig : Slice U8) (m : Array U8 N) (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs)
    (fits : N.val*(2*N.val+3)≤sig.length) :
    wots.arm.recover sig m seed a = slhdsa.wots.wots_pk_from_sig sig m seed a := by
  obtain ⟨x,hx,xs⟩ := spec_imp_exists (recover_spec p hp sig m seed hs a fits)
  obtain ⟨y,hy,ys⟩ := spec_imp_exists (wots_pk_from_sig_spec p hp sig m seed hs a fits)
  rw [hx,hy,ok.injEq]
  exact Aeneas.Std.Array.ext _ _ ((bytes_inj _ _).mp (xs.trans ys.symm))

#print axioms recover_eq_scalar

end slhdsa.Armwide.Recovery
