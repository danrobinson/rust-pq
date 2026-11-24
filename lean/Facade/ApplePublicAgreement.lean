import Facade.PublicSession
import Spec.AppleSha2PublicSession

/-! Compare the extracted Rust public API with the measured Apple executable’s
public keygen, signing and verification returns. The comparison reads both
returned key buffers and the bytes of the returned Some(Vec). Each verifier
receives the signature produced by its own public signer. Native alias choices
are compared with the Rust canonical public calls. -/
open Aeneas Aeneas.Std Result
open LinkedArm LinkedArm.Signer
namespace slhdsa.Suite.ApplePublic

abbrev Set := PureNativeSession.Set

def params (family : Spec.HashFamily) (s : Set) : Spec.Params :=
  match family with
  | .sha2 => Sha2PureNativeSession.params s
  | .shake => PureNativeSession.params s

def signing (deterministic useAlias : Bool) : PureNativeSession.Signing :=
  if deterministic then .deterministic else if useAlias then .alias else .sign

def allocation (i : Fin 8) : PureNativeSession.Allocation :=
  ⟨i.val.testBit 0,i.val.testBit 1,i.val.testBit 2⟩

def native (family : Spec.HashFamily) (s : Set) (det sa va : Bool) (a b : Fin 8) (prof : Fin 4)
    (sec prf seed msg ctx supplied : Spec.Bytes) :=
  match family with
  | .sha2 => Sha2PureNativeSession.run s (signing det sa) va (allocation a) prof b
      (Sha2PureNativeSession.referenceOuter s) sec prf seed msg ctx supplied
  | .shake => PureNativeSession.run s (signing det sa) va (allocation a) (allocation b) prof
      sec prf seed msg ctx supplied

private theorem native_eq (family : Spec.HashFamily) (s : Set) (det sa va : Bool)
    (a b : Fin 8) (prof : Fin 4) (sec prf seed msg ctx supplied : Spec.Bytes)
    (sizes : sec.length = (params family s).n ∧ prf.length = (params family s).n ∧ seed.length = (params family s).n)
    (rnd : supplied.length = (params family s).n) (valid : ctx.length ≤ 255)
    (fits : 2 + ctx.length + msg.length < 2^63) :
    let p := params family s
    let keys := Spec.slhKeygenInternal p sec prf seed
    native family s det sa va a b prof sec prf seed msg ctx supplied =
      some (keys, Spec.slhSign p msg ctx keys.1 (if det then Spec.block p keys.1 2 else supplied), true) := by
  have convert (p : Spec.Params) (sk : Spec.Bytes) :
      PureNativeSession.randomness (signing det sa) p sk supplied = (if det then Spec.block p sk 2 else supplied) := by
    cases det <;> cases sa <;> rfl
  cases family with
  | sha2 =>
    simpa only [native,params,convert] using (Sha2PureNativeSession.public_run_eq s (signing det sa) va
      (allocation a) prof b sec prf seed msg ctx supplied sizes (fun _ => rnd) valid fits)
  | shake =>
    simpa only [native,params,convert] using (PureNativeSession.run_eq s (signing det sa) va
      (allocation a) (allocation b) prof sec prf seed msg ctx supplied sizes (fun _ => rnd) valid fits)

def Agreement {S K V N : Usize} (family : Spec.HashFamily) (s : Set) (slack : Nat)
    (kg : Array U8 S → Array U8 K → Array U8 V → Result (Array U8 K × Array U8 V))
    (sign : Slice U8 → Slice U8 → Array U8 K → Array U8 N → Result (Option (alloc.vec.Vec U8)))
    (det : Slice U8 → Slice U8 → Array U8 K → Result (Option (alloc.vec.Vec U8)))
    (check : Slice U8 → Slice U8 → Slice U8 → Array U8 V → Result Bool) : Prop :=
  ∀ (a b : Fin 8) (prof : Fin 4) (signAlias verifyAlias : Bool)
    (seeds : Array U8 S) (skBuf : Array U8 K) (pkBuf : Array U8 V) (m ctx : Slice U8)
    (random : Array U8 N) (deterministic : Bool) (_ : Room m.length slack) (_ : ctx.length ≤ 255),
    let part := Spec.block (params family s) (bytes seeds.val)
    ∃ sk pk sig, kg seeds skBuf pkBuf = ok (sk,pk) ∧
      (if deterministic then det m ctx sk else sign m ctx sk random) = ok (some sig) ∧
      check m sig.deref ctx pk = ok true ∧
      native family s deterministic signAlias verifyAlias a b prof (part 0) (part 1) (part 2)
          (bytes m.val) (bytes ctx.val) (bytes random.val) =
        some ((bytes sk.val,bytes pk.val),some (bytes sig.val),true)

theorem agree {S K V N : Usize} {family s slack kg sign det check}
    (rust : @PublicSession S K V N (params family s) slack kg sign det check)
    (set : params family s ∈ parameterSets ∨ params family s ∈ sha2ParameterSets)
    (seedsLength : S.val = 3*(params family s).n) (randomLength : N.val = (params family s).n) :
    Agreement family s slack kg sign det check := by
  intro a b prof sa va seeds skBuf pkBuf m ctx random mode room context
  let p := params family s
  let part := Spec.block p (bytes seeds.val)
  have plen (i : Nat) (hi : i < 3) : (part i).length = p.n := by
    simp [part,Spec.block,seedsLength,p]
    interval_cases i <;> omega
  obtain ⟨sk,pk,sig,kgRun,signRun,verifyRun,session⟩ := rust seeds skBuf pkBuf m ctx random mode room context
  have sizes := And.intro (plen 0 (by decide)) (And.intro (plen 1 (by decide)) (plen 2 (by decide)))
  have valid : (bytes ctx.val).length ≤ 255 := by simpa using context
  have fitted : 2 + (bytes ctx.val).length + (bytes m.val).length < 2^63 := by
    have bound := room.2
    have mLength : (bytes m.val).length = m.length := by simp
    omega
  obtain ⟨keyBytes,sigBytes,_,_⟩ := (session_iff set sizes valid).mp session
  refine ⟨sk,pk,sig,kgRun,signRun,verifyRun,?_⟩
  rw [native_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ sizes (by simpa using randomLength) valid fitted,← keyBytes]
  exact congrArg (fun signed => some ((bytes sk.val,bytes pk.val),signed,true)) sigBytes.symm

theorem sha2_128s : Agreement .sha2 .s128 409
    sets.sha2_128s.keygen sets.sha2_128s.sign sets.sha2_128s.sign_deterministic sets.sha2_128s.verify :=
  agree sha2_128s_session (by right; decide) (by decide) (by decide)

theorem sha2_128f : Agreement .sha2 .f128 409
    sets.sha2_128f.keygen sets.sha2_128f.sign sets.sha2_128f.sign_deterministic sets.sha2_128f.verify :=
  agree sha2_128f_session (by right; decide) (by decide) (by decide)

theorem sha2_192s : Agreement .sha2 .s192 561
    sets.sha2_192s.keygen sets.sha2_192s.sign sets.sha2_192s.sign_deterministic sets.sha2_192s.verify :=
  agree sha2_192s_session (by right; decide) (by decide) (by decide)

theorem sha2_192f : Agreement .sha2 .f192 561
    sets.sha2_192f.keygen sets.sha2_192f.sign sets.sha2_192f.sign_deterministic sets.sha2_192f.verify :=
  agree sha2_192f_session (by right; decide) (by decide) (by decide)

theorem sha2_256s : Agreement .sha2 .s256 561
    sets.sha2_256s.keygen sets.sha2_256s.sign sets.sha2_256s.sign_deterministic sets.sha2_256s.verify :=
  agree sha2_256s_session (by right; decide) (by decide) (by decide)

theorem sha2_256f : Agreement .sha2 .f256 561
    sets.sha2_256f.keygen sets.sha2_256f.sign sets.sha2_256f.sign_deterministic sets.sha2_256f.verify :=
  agree sha2_256f_session (by right; decide) (by decide) (by decide)

theorem shake_128s : Agreement .shake .s128 409
    sets.shake_128s.keygen sets.shake_128s.sign sets.shake_128s.sign_deterministic sets.shake_128s.verify :=
  agree shake_128s_session (by left; decide) (by decide) (by decide)

theorem shake_128f : Agreement .shake .f128 409
    sets.shake_128f.keygen sets.shake_128f.sign sets.shake_128f.sign_deterministic sets.shake_128f.verify :=
  agree shake_128f_session (by left; decide) (by decide) (by decide)

theorem shake_192s : Agreement .shake .s192 561
    sets.shake_192s.keygen sets.shake_192s.sign sets.shake_192s.sign_deterministic sets.shake_192s.verify :=
  agree shake_192s_session (by left; decide) (by decide) (by decide)

theorem shake_192f : Agreement .shake .f192 561
    sets.shake_192f.keygen sets.shake_192f.sign sets.shake_192f.sign_deterministic sets.shake_192f.verify :=
  agree shake_192f_session (by left; decide) (by decide) (by decide)

theorem shake_256s : Agreement .shake .s256 561
    sets.shake_256s.keygen sets.shake_256s.sign sets.shake_256s.sign_deterministic sets.shake_256s.verify :=
  agree shake_256s_session (by left; decide) (by decide) (by decide)

theorem shake_256f : Agreement .shake .f256 561
    sets.shake_256f.keygen sets.shake_256f.sign sets.shake_256f.sign_deterministic sets.shake_256f.verify :=
  agree shake_256f_session (by left; decide) (by decide) (by decide)

run_cmd
  for decl in [``agree,
      ``sha2_128s,
      ``sha2_128f,
      ``sha2_192s,
      ``sha2_192f,
      ``sha2_256s,
      ``sha2_256f,
      ``shake_128s,
      ``shake_128f,
      ``shake_192s,
      ``shake_192f,
      ``shake_256s,
      ``shake_256f] do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{decl} depends on unexpected axiom {ax}"
#print axioms agree
end slhdsa.Suite.ApplePublic
