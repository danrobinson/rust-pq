import Cachepath.NativeHashReplay
import Shakebatch.PortablePublic
open Aeneas Aeneas.Std Result slhdsa

namespace CacheopsRust.NativeVerifier
/-- The only two recovery operations which change when the production SIMD verifier is enabled. -/
structure Recovery where
  wots {N : Usize} : Slice U8 → Array U8 N → Array U8 N → slhdsa.address.Adrs → Result (Array U8 N)
  fors {N : Usize} : slhdsa.params.Params → Slice U8 → Slice U8 → Array U8 N → slhdsa.address.Adrs → Result (Array U8 N)
  wots_spec {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (sig : Slice U8)
      (m seed : Array U8 N) (a : slhdsa.address.Adrs) (enough : N.val*(2*N.val+3)≤sig.length) (domain : a.typ=slhdsa.address.WOTS_HASH ∧ a.word2=0#u32 ∧ a.word3=0#u32) :
      wots sig m seed a ⦃ out => bytes out.val=Spec.wotsPkFromSig (Shake.params p)
        (bytes sig.val) (bytes m.val) (bytes seed.val) (adrsS a) ⦄
  fors_spec {N : Usize} (p : slhdsa.params.Params) (hp : PN p N) (sig md : Slice U8)
      (seed : Array U8 N) (a : slhdsa.address.Adrs) (len : sig.length=p.k.val*(1+p.a.val)*N.val)
      (mdLen : md.length=(p.k.val*p.a.val+7)/8)
      (domain : a.typ=slhdsa.address.FORS_TREE ∧ a.word2=0#u32 ∧ a.word3=0#u32) :
      fors p sig md seed a ⦃ out => bytes out.val=Spec.forsPkFromSig (Shake.params p)
        (bytes sig.val) (bytes md.val) (bytes seed.val) (adrsS a) ⦄

open slhdsa.Shake

def xmssPk (recovery : Recovery) {N : Usize} (p : slhdsa.params.Params) (idx : U32)
    (sig : Slice U8) (m seed : Array U8 N) (a : slhdsa.address.Adrs) : Result (Array U8 N) := do
  let a1 ← slhdsa.address.Adrs.with_type a slhdsa.address.WOTS_HASH
  let a2 ← slhdsa.address.Adrs.with_keypair a1 idx
  let node ← recovery.wots sig m seed a2
  let n ← 2#usize * N
  let len ← n + slhdsa.params.LEN2
  let a3 ← slhdsa.address.Adrs.with_type a slhdsa.address.TREE
  slhdsa.shake.xmss.climb node idx sig len p.hp seed a3

theorem xmssSpec (recovery : Recovery) {N : Usize} (p : _root_.slhdsa.params.Params) (hp : PN p N) (idx : U32)
    (sig : Slice U8) (m : Array U8 N) (seed : Array U8 N) (a : slhdsa.address.Adrs)
    (h : sig.length = (2 * N.val + 3 + p.hp.val) * N.val) (hidx : idx.val < 2 ^ p.hp.val) :
    xmssPk recovery p idx sig m seed a ⦃ r =>
      bytes r.val = Spec.xmssPkFromSig (Shake.params p) idx.val (bytes sig.val) (bytes m.val)
        (bytes seed.val) (adrsS a) ⦄ := by
  unfold xmssPk
  have hhp := valid_hp_le p hp.valid
  have hN32 := hp.le32
  simp only [LEN2_eq]
  let* ⟨ a1, a1_post, a1_post1 ⟩ ← slhdsa.with_type_spec
  let* ⟨ a2, a2_post ⟩ ← with_keypair_spec
  have hsl : N.val * (2 * N.val + 3) ≤ sig.length := by
    rw [h]; have := Nat.mul_le_mul_right N.val (show 2 * N.val + 3 ≤ 2 * N.val + 3 + p.hp.val by omega)
    rw [Nat.mul_comm] at this; exact this
  let* ⟨ node, node_post ⟩ ← recovery.wots_spec p hp sig m seed a2 hsl (by simp [a2_post,a1_post1])
  let* ⟨ i, i_post ⟩ ← Usize.mul_spec
  let* ⟨ i1, i1_post ⟩ ← Usize.add_spec
  let* ⟨ a3, a3_post, a3_post1 ⟩ ← slhdsa.with_type_spec
  apply WP.spec_mono
  · exact slhdsa.Shake.climb_spec p hp node idx sig i1 p.hp seed a3 0 idx.val
      (by rw [i1_post, i_post, h]) (by omega) (by simp) hidx
  · intro r hr
    rw [hr, node_post, a3_post, i1_post, i_post]
    simp only [Spec.xmssPkFromSig]
    rw [wotsPkFromSig_take, show (Shake.params p).len = _ from hp.len, show (Shake.params p).n = _ from hp.n, show (Shake.params p).hp = _ from paramsS_hp p]
    simp [a2_post, a1_post1, adrsS,
      Spec.Adrs.setTypeAndClear, Spec.WOTS_HASH, slhdsa.address.WOTS_HASH, Spec.TREE, slhdsa.address.TREE]


open Lean Meta in
partial def abstractCalls (destination : Name) (modules : List Name) (source : Name) (seen : IO.Ref (Std.HashMap Name Name)) : MetaM Name := do
  if let some target := (← seen.get).get? source then return target
  let env ← getEnv
  let some idx := env.getModuleIdxFor? source | return source
  let origin := env.header.moduleNames[idx]!
  unless modules.any (·.isPrefixOf origin) do return source
  let info ← getConstInfo source
  let some body := info.value? true | return source
  let mut changed := false
  for child in info.type.getUsedConstants ++ body.getUsedConstants do
    if (← abstractCalls destination modules child seen) != child then changed := true
  unless changed do
    seen.modify (·.insert source source)
    return source
  let target := destination ++ source
  let names ← seen.get
  withLocalDeclD `recovery (mkConst `CacheopsRust.NativeVerifier.Recovery) fun r => do
    let replace (e : Expr) := e.replace fun
      | .const n ls => (names.get? n).bind fun dst => if n==dst then none else some (mkApp (mkConst dst ls) r)
      | _ => none
    let type ← mkForallFVars #[r] (replace info.type)
    let value ← mkLambdaFVars #[r] (replace body)
    let decl ← match info with
      | .defnInfo d => pure <| .defnDecl { d with «name» := target, type, value, all := [target] }
      | .thmInfo t => pure <| .thmDecl { t with «name» := target, type, value, all := [target] }
      | _ => throwError "unexpected recovery dependency {source}"
    addDecl decl
    seen.modify (·.insert source target)
    return target

open Lean Meta Elab Command in
set_option Elab.async false in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let pairs := [(`slhdsa.shake.xmss.xmss_pk_from_sig,`CacheopsRust.NativeVerifier.xmssPk),
    (`slhdsa.Shake.xmss_pk_from_sig_spec,`CacheopsRust.NativeVerifier.xmssSpec),
    (`slhdsa.shake.fors.fors_pk_from_sig,`CacheopsRust.NativeVerifier.Recovery.fors),
    (`slhdsa.Shake.fors_verify_spec,`CacheopsRust.NativeVerifier.Recovery.fors_spec)]
  let names ← IO.mkRef (Std.HashMap.ofList pairs)
  let _ ← abstractCalls `VerifierWithRecovery [`Slhdsa,`Shakebatch,`Shakeopt] `SegmentedPublic.slhdsa.Shake.api_verify_spec names
  pure ()

end CacheopsRust.NativeVerifier
