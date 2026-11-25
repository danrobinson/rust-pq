import Parallel.FusedSignature
import Shakeopt.ForsWideSignature
import Parallel.KeygenPublic
import Cachepath.NativeVerify.Hosted
import Shakebatch.WidthThreeHost
open Aeneas Aeneas.Std Result
namespace slhdsa.WidthEight
noncomputable section

inductive Platform where
  | apple (sha3 : Bool)
  | x86

def Platform.wide : Platform → Bool
  | .apple _ => true
  | .x86 => GatherRust.avx512Available

/-- The Rust dispatcher accepts only the three FIPS byte lengths. -/
def Platform.available (host : Platform) (N : Usize) : Bool :=
  (N.val == 16 || N.val == 24 || N.val == 32) && host.wide

def Platform.recovery : Platform → CacheopsRust.NativeVerifier.Recovery
  | .apple sha3 => AppleNativeRecovery.slhdsa.NativeVerify.appleRecovery sha3
  | .x86 => X86NativeRecovery.slhdsa.NativeVerify.x86Recovery

/-- Project a completed native output buffer into its Aeneas byte vector. -/
def packVec (value : Spec.Bytes) : Result (alloc.vec.Vec U8) :=
  if h : value.length ≤ Usize.max then
    ok (alloc.vec.Vec.from (value.map (fun b => (⟨b⟩ : U8))) (by simpa using h))
  else fail .panic

theorem packVec_eq (b : Spec.Bytes) (r : alloc.vec.Vec U8) (eq : bytes r.val=b) : packVec b=ok r := by
  subst b
  rw [packVec,dif_pos (by simpa [bytes] using r.slice.length_le_usize)]
  congr 1
  cases r with
  | mk s =>
    apply congrArg alloc.vec.Vec.mk
    apply Slice.ext
    simp only [alloc.vec.Vec.from,alloc.vec.Vec.val,Slice.from_val,bytes,List.map_map]
    change List.map id s.val = s.val
    exact List.map_id _

/-- Value of the width-eight fused XMSS signing branch. The portable branch
is shared by x86 hosts without the available instruction set. -/
def xmssSign (host : Platform) {N : Usize} (p : params.Params) (m sk : Array U8 N) (idx : U32) (seed : Array U8 N)
    (a : address.Adrs) : Result (alloc.vec.Vec U8) :=
  if 3≤p.hp.val && host.available N then
    packVec (ParallelFusedSignature.sign (Shake.params p) (bytes m.val) (bytes sk.val) idx.val (bytes seed.val)
      (adrsS a) (fun _ => []))
  else shake.xmss.xmss_sign p m sk idx seed a

theorem xmssSign_spec (host : Platform) {N : Usize} (p : params.Params) (hp : PN p N) (m sk : Array U8 N)
    (idx : U32) (seed : Array U8 N) (a : address.Adrs) (fits : idx.val < 2^p.hp.val) :
    xmssSign host p m sk idx seed a ⦃ r => bytes r.val=Spec.xmssSign (Shake.params p) (bytes m.val) (bytes sk.val)
      idx.val (bytes seed.val) (adrsS a) ∧ r.length=(2*N.val+3+p.hp.val)*N.val ⦄ := by
  have scalar := Shake.xmss_sign_spec p hp m sk idx seed a fits
  unfold xmssSign
  split
  · obtain ⟨r,_,eq,size⟩ := spec_imp_exists scalar
    rw [ParallelFusedSignature.sign_fips (Shake.params p) _ _ _ _ _ _ (by change (paramsS p).len=2*p.n.val+3; simpa [hp.n_eq] using hp.len) (by rfl) (by exact hp.valid.hp_le),
      packVec_eq _ r eq]
    exact (WP.spec_ok _).mpr ⟨eq,size⟩
  · exact scalar

def forsSign (host : Platform) {N : Usize} (p : params.Params) (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs) :=
  if host.available N then packVec (Shakeopt.ForsWideSignature.signature (Shake.params p) (bytes md.val) (bytes sk.val) (bytes seed.val) (adrsS a))
  else shake.fors.fors_sign p md sk seed a

theorem forsSign_spec (host : Platform) {N : Usize} (p : params.Params) (hp : PN p N) (md : Slice U8)
    (sk seed : Array U8 N) (a : address.Adrs) (size : md.length=(p.k.val*p.a.val+7)/8)
    (domain : a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32) :
    forsSign host p md sk seed a ⦃ r => bytes r.val=Spec.forsSign (Shake.params p) (bytes md.val) (bytes sk.val)
      (bytes seed.val) (adrsS a) ∧ r.length=p.k.val*(1+p.a.val)*N.val ⦄ := by
  have scalar := Shake.fors_sign_domain p hp md sk seed a size domain
  unfold forsSign
  split
  · obtain ⟨r,_,eq,len⟩ := spec_imp_exists scalar
    rw [Shakeopt.ForsWideSignature.signature_eq (Shake.params p) _ _ _ _ (by exact hp.valid.a_le),packVec_eq _ r eq]
    exact (WP.spec_ok _).mpr ⟨eq,len⟩
  · exact scalar

abbrev xmssRecover (host : Platform) := @CacheopsRust.NativeVerifier.xmssPk host.recovery
abbrev xmssRecoverSpec (host : Platform) := @CacheopsRust.NativeVerifier.xmssSpec host.recovery
abbrev forsRecover (host : Platform) := @host.recovery.fors
abbrev forsRecoverSpec (host : Platform) := @host.recovery.fors_spec

end
end slhdsa.WidthEight
