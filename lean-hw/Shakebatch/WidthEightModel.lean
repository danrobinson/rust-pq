import Fused.Entry
import Buffered.Hosted
import Shakebatch.WidthEightFors
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

@[instance_reducible] noncomputable def Platform.fused (host : Platform) (p : params.Params) : Fused.Kernel :=
  match host with
  | .apple sha3 => BufferedApple.slhdsa.Buffered.Host.apple sha3 p
  | .x86 => BufferedX86.slhdsa.Buffered.Host.x86 p

/-- The eight-lane branch runs the complete extracted fused signer. The feature
test retains the portable implementation on x86 hosts without AVX-512. -/
noncomputable def xmssSign (host : Platform) {N : Usize} (p : params.Params) (m sk : Array U8 N)
    (idx : U32) (seed : Array U8 N) (a : address.Adrs) : Result (alloc.vec.Vec U8) :=
  if 3≤p.hp.val && host.available N then
    @Fused.xmss_sign_batch (host.fused p) N p m sk idx seed a
  else shake.xmss.xmss_sign p m sk idx seed a

theorem xmssSign_spec (host : Platform) {N : Usize} (p : params.Params) (hp : PN p N) (m sk : Array U8 N)
    (idx : U32) (seed : Array U8 N) (a : address.Adrs) (fits : idx.val < 2^p.hp.val) :
    xmssSign host p m sk idx seed a ⦃ r => bytes r.val=Spec.xmssSign (Shake.params p) (bytes m.val) (bytes sk.val)
      idx.val (bytes seed.val) (adrsS a) ∧ r.length=(2*N.val+3+p.hp.val)*N.val ⦄ := by
  unfold xmssSign
  split
  · rename_i on
    obtain ⟨height,feature⟩ := Bool.and_eq_true_iff.mp on
    have height : 3≤p.hp.val := of_decide_eq_true height
    have byteProof : @Fused.xmss_sign_batch (host.fused p) N p m sk idx seed a ⦃ out =>
        bytes out.val=Spec.xmssSign (Shake.params p) (bytes m.val) (bytes sk.val) idx.val (bytes seed.val) (adrsS a) ⦄ := by
      cases host with
      | apple sha3 =>
        exact @Fused.sign_spec (BufferedApple.slhdsa.Buffered.Host.apple sha3 p) N p hp m sk idx seed a height fits
          (AppleHybrid.permutation_correct sha3) (NativeVerify.apple sha3)
          (BufferedApple.slhdsa.Buffered.Host.apple_nodes sha3 p hp sk seed a)
      | x86 =>
        have cpu : GatherRust.avx512Available=true := (Bool.and_eq_true_iff.mp feature).2
        exact @Fused.sign_spec (BufferedX86.slhdsa.Buffered.Host.x86 p) N p hp m sk idx seed a height fits
          (Kxdispatch.permutation_correct cpu) (NativeVerify.x86 cpu)
          (BufferedX86.slhdsa.Buffered.Host.x86_nodes cpu p hp sk seed a)
    apply WP.spec_mono byteProof
    intro r eq
    refine ⟨eq,?_⟩
    have h := congrArg List.length eq
    have valid : (Shake.params p).Valid := Suite.valid .shake hp
    rw [Spec.xmssSign_length _ valid] at h
    have len : (Shake.params p).len=2*N.val+3 := by change (paramsS p).len=_; exact hp.len
    simpa only [bytes_length,Spec.Params.xmssSigBytes,len,show (Shake.params p).n=N.val from hp.n,
      show (Shake.params p).hp=p.hp.val from rfl] using h
  · exact Shake.xmss_sign_spec p hp m sk idx seed a fits

theorem apple_fast {N : Usize} (sha3 : Bool) (p : params.Params) (hp : PN p N)
    (m sk : Array U8 N) (idx : U32) (seed : Array U8 N) (a : address.Adrs) (height : 3≤p.hp.val) :
    xmssSign (.apple sha3) p m sk idx seed a =
      @Fused.xmss_sign_batch (BufferedApple.slhdsa.Buffered.Host.apple sha3 p) N p m sk idx seed a := by
  have geom := hp.nok
  unfold xmssSign Platform.available Platform.wide
  rcases geom with h|h|h <;> simp [h,height]

theorem x86_select {N : Usize} (p : params.Params) (hp : PN p N)
    (m sk : Array U8 N) (idx : U32) (seed : Array U8 N) (a : address.Adrs) (height : 3≤p.hp.val) :
    xmssSign .x86 p m sk idx seed a =
      if GatherRust.avx512Available then
        @Fused.xmss_sign_batch (BufferedX86.slhdsa.Buffered.Host.x86 p) N p m sk idx seed a
      else shake.xmss.xmss_sign p m sk idx seed a := by
  have geom := hp.nok
  unfold xmssSign Platform.available Platform.wide
  rcases geom with h|h|h <;> simp [h,height]

/-- Project each active lane through the host's actual hash implementation.
The surrounding wide shuffle and field trace are handled by the physical tree. -/
def wideFors (host : Platform) {N : Usize} (p : params.Params) (md : Slice U8)
    (sk seed : Array U8 N) (a : address.Adrs) : Spec.Bytes :=
  match host with
  | .apple sha3 => @Fors.signature (AppleHybrid.machine sha3) (NativeVerify.appleActive sha3) N p md sk seed a
  | .x86 => @Fors.signature Kxdispatch.machine
      (NativeVerify.fullActive Kxdispatch.machine KxdispatchRust.shake256.parallel.available) N p md sk seed a

theorem wideFors_spec (host : Platform) {N : Usize} (p : params.Params) (hp : PN p N)
    (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs)
    (domain : a.typ=address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32) (on : host.available N=true) :
    wideFors host p md sk seed a=Spec.forsSign (Shake.params p) (bytes md.val) (bytes sk.val)
      (bytes seed.val) (adrsS a) := by
  cases host with
  | apple sha3 =>
    exact @Fors.signature_eq (AppleHybrid.machine sha3) _ (NativeVerify.apple sha3)
      (by change 0<8; decide) N p hp md sk seed a domain
  | x86 =>
    exact @Fors.signature_eq Kxdispatch.machine _ (NativeVerify.x86 (Bool.and_eq_true_iff.mp on).2)
      (by change 0<8; decide) N p hp md sk seed a domain

def forsSign (host : Platform) {N : Usize} (p : params.Params) (md : Slice U8) (sk seed : Array U8 N) (a : address.Adrs) :=
  if host.available N then packVec (wideFors host p md sk seed a)
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
    rw [wideFors_spec host p hp md sk seed a domain (by assumption),packVec_eq _ r eq]
    exact (WP.spec_ok _).mpr ⟨eq,len⟩
  · exact scalar

abbrev xmssRecover (host : Platform) := @CacheopsRust.NativeVerifier.xmssPk host.recovery
abbrev xmssRecoverSpec (host : Platform) := @CacheopsRust.NativeVerifier.xmssSpec host.recovery
abbrev forsRecover (host : Platform) := @host.recovery.fors
abbrev forsRecoverSpec (host : Platform) := @host.recovery.fors_spec

end
end slhdsa.WidthEight
