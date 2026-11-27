import Parallel.WidthEightHosted
open Aeneas Aeneas.Std Result
namespace slhdsa.WidthEight.ParallelSign
noncomputable section

def sign (c : Config) {N : Usize} (p : params.Params) (m ctx sk : Slice U8) (rnd : Array U8 N) :=
  match c.host with
  | .apple _ => ParallelApple.WidthEightParallel.ShakeoptSeg.shake.slh.slh_sign c p m ctx sk rnd
  | .x86 => ParallelX86.WidthEightParallel.ShakeoptSeg.shake.slh.slh_sign c p m ctx sk rnd

theorem sign_spec (c : Config) {N : Usize} (p : params.Params) (hp : PN p N)
    (m ctx sk : Slice U8) (rnd : Array U8 N) (ks : sk.length=4*N.val) :
    sign c p m ctx sk rnd ⦃ r => r.map (fun x => bytes x.val) =
      Spec.slhSign (Shake.params p) (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes rnd.val) ⦄ := by
  unfold sign
  split
  · exact ParallelApple.WidthEightParallel.Shakeopt.Segmented.slh_sign_spec c p hp m ctx sk rnd ks
  · exact ParallelX86.WidthEightParallel.Shakeopt.Segmented.slh_sign_spec c p hp m ctx sk rnd ks

def generateSignVerify {N : Usize} (c : Config) (pool : ParallelKeygenHost.PoolOutcome)
    (p : params.Params) (secret prf publicSeed : Array U8 N) (sk pk msg ctx : Slice U8) (rnd : Array U8 N) :
    Result Bool := do
  let (secretKey,publicKey) ← @ParallelKeygenHost.Sh.shake.slh.slh_keygen_internal (keyEngine c.host p)
    ⟨c.host.isX86,c.threads.val,pool⟩ N p secret prf publicSeed sk pk
  let signature ← sign c p msg ctx secretKey rnd
  match signature with
  | none => ok false
  | some sig => WidthEight.verify c.host N p msg sig.deref ctx publicKey

theorem roundtrip {N : Usize} (p : params.Params) (hp : PN p N) (c : Config) (pool : ParallelKeygenHost.PoolOutcome)
    (secret prf publicSeed : Array U8 N) (sk pk msg ctx : Slice U8) (rnd : Array U8 N)
    (ks : sk.length=4*N.val) (ps : pk.length=2*N.val) (hc : ctx.length≤255) :
    generateSignVerify c pool p secret prf publicSeed sk pk msg ctx rnd=ok true := by
  obtain ⟨⟨sk',pk'⟩,gen,bytesEq,ks',ps'⟩ := spec_imp_exists
    (keys c.host p hp c.threads.val pool secret prf publicSeed sk pk ks ps)
  have valid : (Shake.params p).Valid := Suite.valid .shake hp
  have length (v : Array U8 N) : (bytes v.val).length=(Shake.params p).n := by simp only [bytes_length,Array.property];exact hp.n.symm
  have good := Spec.keygen_keyOk (Shake.params p) valid _ _ _ (length secret) (length prf) (length publicSeed)
  rw [←bytesEq] at good
  obtain ⟨ret,sg,bytesSig⟩ := spec_imp_exists (sign_spec c p hp msg ctx sk' rnd ks')
  obtain ⟨expected,signed,ok⟩ := Spec.slh_complete (Shake.params p) valid (bytes msg.val) (bytes ctx.val)
    (bytes sk'.val) (bytes rnd.val) (by simpa [bytes] using hc) good.1
  rw [signed] at bytesSig
  cases ret with
  | none => contradiction
  | some sig =>
    obtain ⟨verdict,verify,answer⟩ := spec_imp_exists (WidthEight.verify_spec c.host p hp msg sig.deref ctx pk' ps')
    have sigEq : bytes sig.val=expected := Option.some.inj bytesSig
    have pkEq : bytes pk'.val=Spec.skPk (Shake.params p) (bytes sk'.val) := good.2
    rw [vec_deref_val,sigEq,pkEq,ok] at answer
    simp only [generateSignVerify,gen,bind_ok,uncurry,sg,verify,answer]

open Lean Meta Elab Command in
set_option Elab.async false in
run_cmd liftTermElabM do
  let install (root : Name) (args : Array Expr) (proof : Expr) : MetaM Unit := do
    let value ← mkLambdaFVars args proof
    addDecl <| .thmDecl {«name» := root, levelParams := [], type := ← inferType value, value}
  for suite in [`shake_128s,`shake_128f,`shake_192s,`shake_192f,`shake_256s,`shake_256f] do
    for apple in [true,false] do
      let publish (host : Expr) (args : Array Expr) : MetaM Unit := do
        let scheduleTy := mkConst ``Ticket.Schedules
        withLocalDeclD `schedule scheduleTy fun schedule =>
         withLocalDeclD `threads (mkConst `Aeneas.Std.Usize) fun threads => do
          let config ← mkAppM ``Config.mk #[host,threads,schedule]
          let dst := (if apple then `ParallelAppleAPI else `ParallelX86API) ++ suite
          let ns := (if apple then `ParallelApple else `ParallelX86) ++ `WidthEightParallel
          for op in [`slh_sign_internal_spec,`slh_sign_spec,`sign_spec,`sign_deterministic_spec] do
            let base := `slhdsa ++ suite ++ op
            let root := if (← getEnv).contains (ns ++ `SegmentedPublic ++ base) then ns ++ `SegmentedPublic ++ base else ns ++ base
            install (dst ++ op) ((args.push schedule).push threads) (mkApp (mkConst root) config)
          let p := mkConst (`slhdsa.sets ++ suite ++ `params.PARAMS)
          let hp := mkConst (`slhdsa ++ suite ++ `pn)
          install (dst ++ `roundtrip) ((args.push schedule).push threads) (←mkAppOptM ``roundtrip #[none,some p,some hp,some config])
      if apple then withLocalDeclD `sha3 (mkConst `Bool) fun sha3 => publish (mkApp (mkConst ``Platform.apple) sha3) #[sha3]
      else publish (mkConst ``Platform.x86) #[]

end
end slhdsa.WidthEight.ParallelSign
