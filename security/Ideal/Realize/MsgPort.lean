import Ideal.Realize.MsgHarness
import Reduction.Open.Wrappers

/-!
# The open `PRF_msg` distinguishers for a forger with a compression port

The game slot of the open programs `Reduction.Open.msgOpenWV` / `msgOpenV` (over
`Lazy.OSpec prims (msgG prims)`) is widened to `hS + msgG prims`: the forger's compression queries
are port queries of the open program.

* `msgSignOP`, `msgPreWP`, `msgOpenWVP` (SUF), `msgPreP`, `msgOpenVP` (EUF): the port programs.
* **Fusion** `msgOpenWVP_fusion`, `msgOpenVP_fusion`: answering the port by `g` (`portR g`) gives
  `msgOpenWV wO` / `msgOpenV` at the forger with its port answered by `g` (`fusedF`).
* `portR_openKeygen`, `portR_openSign`, `portR_embR`: the pieces.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize.Msg

open Reduction Reduction.Lazy Reduction.Open

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Generic

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable {ι : Type} {G : OracleSpec ι}

attribute [local instance] Lazy.openQ

/-- `portR g` as a hash-preserving monad morphism. -/
noncomputable def portHom (g : CF St Blk) :
    HasQuery.QueryHom (publicHashSpec prims.core) (OracleComp (OSpec prims (hS St Blk + G)))
      (OracleComp (OSpec prims G)) :=
  { toMonadHom := simulateQ' (portR g)
    map_query' := fun q => by simp [portR] }

theorem portHom_apply (g : CF St Blk) {α : Type} (oa : OracleComp (OSpec prims (hS St Blk + G)) α) :
    (portHom (prims := prims) (G := G) g).toMonadHom oa = simulateQ (portR g) oa := rfl

theorem portR_secQ (g : CF St Blk) (a : Adrs) :
    simulateQ (portR g) (secQ prims (hS St Blk + G) a) = secQ prims G a := by
  unfold secQ
  rw [simulateQ_spec_query]
  rfl

theorem portR_openKeygen (g : CF St Blk) (pkSeed : prims.PkSeed) :
    simulateQ (portR g) (openKeygen prims (hS St Blk + G) pkSeed) = openKeygen prims G pkSeed :=
  GeneralScheme.keygenInternalWithSecretM_natural (vp := vp) prims.core (portHom g)
    (secQ prims _) (secQ prims _) (fun a _ => portR_secQ g a) pkSeed

theorem portR_openSign (g : CF St Blk) (msg : List Byte) (pkSeed : prims.PkSeed)
    (pkRoot R : prims.Y) :
    simulateQ (portR g) (openSign prims (hS St Blk + G) msg pkSeed pkRoot R) =
      openSign prims G msg pkSeed pkRoot R :=
  GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp) prims.core (portHom g)
    (secQ prims _) (secQ prims _) (fun a _ => portR_secQ g a) msg pkSeed pkRoot R

theorem portR_embR (g : CF St Blk) {α : Type} (Q : OracleComp (publicHashSpec prims.core) α) :
    simulateQ (portR g)
        (embR (gspec := hS St Blk + G) (D := SecIdx) (V := prims.Y) Q) =
      embR (gspec := G) (D := SecIdx) (V := prims.Y) Q := by
  induction Q using OracleComp.inductionOn with
  | pure a => simp [embR]
  | query_bind t k ih =>
    simp only [embR, simulateQ_bind, simulateQ_spec_query] at ih ⊢
    simp only [hashEmbR]
    rw [simulateQ_spec_query]
    exact bind_congr fun u => ih u

end Generic

section Msg

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

/-- The game slot of the port programs: port, then the `PRF_msg` game oracle. -/
abbrev GP (prims : Primitives vp.params) := hS St Blk + msgG prims

/-- The interface of the port programs. -/
abbrev OP (prims : Primitives vp.params) := OSpec prims (GP prims)

/-- A port query of the open program. -/
def portO (q : St × Blk) : OracleComp (OP prims) St := gameQ prims (GP prims) (.inl q)

/-- Signing in the port programs: `opt_rand`, one `PRF_msg` game query, open signing. -/
def msgSignOP (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pk : PublicKeyCore prims.core) (m : List Byte) :
    OracleComp (OP prims) (GeneralScheme.SignatureCore vp prims.core) := do
  let addrnd ← (liftM (optRand pk) : OracleComp (OP prims) prims.Y)
  let R ← gameQ prims (GP prims) (.inr (addrnd, m))
  openSign prims (GP prims) m pk.pkSeed pk.pkRoot R

/-- The SUF part before the final check. -/
def msgPreWP (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) (mainP : PortForgerProg vp prims) :
    OracleComp (OP prims)
      (PublicKeyCore prims.core ×
        ((List Byte × GeneralScheme.SignatureCore vp prims.core) × SigLog vp prims)) := do
  let pkSeed ← (liftM pkSeedDist : OracleComp (OP prims) prims.PkSeed)
  let root ← openKeygen prims (GP prims) pkSeed
  let z ← (simulateQ (harnP (portO (prims := prims))
    (sigSignOracle (msgSignOP optRand ⟨pkSeed, root⟩))) (mainP ⟨pkSeed, root⟩)).run []
  return (⟨pkSeed, root⟩, z)

/-- **The open SUF `PRF_msg` distinguisher for a port forger.** -/
def msgOpenWVP (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) (wO : WinCheckO vp prims)
    (mainP : PortForgerProg vp prims) : OracleComp (OP prims) Bool :=
  msgPreWP optRand pkSeedDist mainP >>= fun x => embR (wO x.1 x.2.1 x.2.2)

/-- The EUF part before the final check. -/
def msgPreP (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) (mainP : PortForgerProg vp prims) :
    OracleComp (OP prims)
      (PublicKeyCore prims.core ×
        ((List Byte × GeneralScheme.SignatureCore vp prims.core) × List (List Byte))) := do
  let pkSeed ← (liftM pkSeedDist : OracleComp (OP prims) prims.PkSeed)
  let root ← openKeygen prims (GP prims) pkSeed
  let z ← (simulateQ (harnP (portO (prims := prims))
    (harnessSignOracle (vp := vp) (prims := prims) (msgSignOP optRand ⟨pkSeed, root⟩)))
      (mainP ⟨pkSeed, root⟩)).run []
  return (⟨pkSeed, root⟩, z)

/-- **The open EUF `PRF_msg` distinguisher for a port forger.** -/
def msgOpenVP (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) (mainP : PortForgerProg vp prims) :
    OracleComp (OP prims) Bool :=
  msgPreP optRand pkSeedDist mainP >>= fun x => embR (eufCheckO x.1 x.2.2 x.2.1.1 x.2.1.2)

/-- The forger whose port is answered by `g`. -/
def fusedF (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) (g : CF St Blk) (mainP : PortForgerProg vp prims) :
    Forger vp prims optRand pkSeedDist :=
  ⟨fun pk => simulateQ (instImpl g) (mainP pk)⟩

variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)

theorem portR_msgSignOP (g : CF St Blk) (pk : PublicKeyCore prims.core) (m : List Byte) :
    simulateQ (portR g) (msgSignOP optRand pk m) = msgSignO optRand pk m := by
  unfold msgSignOP msgSignO
  rw [simulateQ_bind, portR_liftM]
  refine bind_congr fun addrnd => ?_
  rw [simulateQ_bind]
  unfold Lazy.gameQ
  rw [simulateQ_spec_query]
  refine bind_congr fun R => ?_
  exact portR_openSign g m pk.pkSeed pk.pkRoot R

theorem portR_portO (g : CF St Blk) (q : St × Blk) :
    simulateQ (portR (G := msgG prims) (D := SecIdx) (V := prims.Y)
      (H := publicHashSpec prims.core) g) (portO (prims := prims) q) = pure (g q) := by
  unfold portO Lazy.gameQ
  rw [simulateQ_spec_query]
  rfl

theorem msgPreWP_fusion (g : CF St Blk) (mainP : PortForgerProg vp prims) :
    simulateQ (portR g) (msgPreWP optRand pkSeedDist mainP) =
      msgPreW (fusedF optRand pkSeedDist g mainP) := by
  unfold msgPreWP msgPreW
  rw [simulateQ_bind, portR_liftM]
  refine bind_congr fun pkSeed => ?_
  rw [simulateQ_bind, portR_openKeygen]
  refine bind_congr fun root => ?_
  rw [simulateQ_bind]
  have h := harnP_fusion (portR g) g (fun n => rfl) (portO (prims := prims)) (portR_portO g)
    (sigSignOracle (msgSignOP optRand ⟨pkSeed, root⟩))
    (sigSignOracle (fun m => simulateQ (portR g) (msgSignOP optRand ⟨pkSeed, root⟩ m)))
    (fun m s => sigSignOracle_fusion _ _ m s) (mainP ⟨pkSeed, root⟩) []
  rw [h]
  have hs : (fun m => simulateQ (portR g) (msgSignOP optRand ⟨pkSeed, root⟩ m)) =
      msgSignO optRand ⟨pkSeed, root⟩ := funext fun m => portR_msgSignOP optRand g _ m
  rw [hs]
  refine bind_congr fun z => ?_
  simp

theorem msgPreP_fusion (g : CF St Blk) (mainP : PortForgerProg vp prims) :
    simulateQ (portR g) (msgPreP optRand pkSeedDist mainP) =
      msgPre (fusedF optRand pkSeedDist g mainP) := by
  unfold msgPreP msgPre
  rw [simulateQ_bind, portR_liftM]
  refine bind_congr fun pkSeed => ?_
  rw [simulateQ_bind, portR_openKeygen]
  refine bind_congr fun root => ?_
  rw [simulateQ_bind]
  have h := harnP_fusion (portR g) g (fun n => rfl) (portO (prims := prims)) (portR_portO g)
    (harnessSignOracle (vp := vp) (prims := prims) (msgSignOP optRand ⟨pkSeed, root⟩))
    (harnessSignOracle (vp := vp) (prims := prims)
      (fun m => simulateQ (portR g) (msgSignOP optRand ⟨pkSeed, root⟩ m)))
    (fun m s => harnessSignOracle_fusion _ _ m s) (mainP ⟨pkSeed, root⟩) []
  rw [h]
  have hs : (fun m => simulateQ (portR g) (msgSignOP optRand ⟨pkSeed, root⟩ m)) =
      msgSignO optRand ⟨pkSeed, root⟩ := funext fun m => portR_msgSignOP optRand g _ m
  rw [hs]
  refine bind_congr fun z => ?_
  simp

/-- **Fusion (SUF).** -/
theorem msgOpenWVP_fusion (g : CF St Blk) (wO : WinCheckO vp prims)
    (mainP : PortForgerProg vp prims) :
    simulateQ (portR g) (msgOpenWVP optRand pkSeedDist wO mainP) =
      msgOpenWV wO (fusedF optRand pkSeedDist g mainP) := by
  unfold msgOpenWVP msgOpenWV
  rw [simulateQ_bind, msgPreWP_fusion]
  exact bind_congr fun x => portR_embR g _

/-- **Fusion (EUF).** -/
theorem msgOpenVP_fusion (g : CF St Blk) (mainP : PortForgerProg vp prims) :
    simulateQ (portR g) (msgOpenVP optRand pkSeedDist mainP) =
      msgOpenV (fusedF optRand pkSeedDist g mainP) := by
  unfold msgOpenVP msgOpenV
  rw [simulateQ_bind, msgPreP_fusion]
  exact bind_congr fun x => portR_embR g _

end Msg

/-! ## The port forger over a core, and independence of `Thash` / `H_msg` -/

section Typed

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-- `signP` over a core bundle. -/
def signPC (codec : CoreWireCodec vp.params core) : QueryImpl (FSpecP (List Byte))
    (OracleComp (FSpecP (GeneralScheme.SignatureCore vp core)))
  | .inl n => (liftM ((FSpecP (GeneralScheme.SignatureCore vp core)).query (.inl n)) :
      OracleComp (FSpecP (GeneralScheme.SignatureCore vp core)) _)
  | .inr (.inl q) =>
      (liftM ((FSpecP (GeneralScheme.SignatureCore vp core)).query (.inr (.inl q))) :
        OracleComp (FSpecP (GeneralScheme.SignatureCore vp core)) _)
  | .inr (.inr m) => encodeSignature vp codec <$>
      (liftM ((FSpecP (GeneralScheme.SignatureCore vp core)).query (.inr (.inr m))) :
        OracleComp (FSpecP (GeneralScheme.SignatureCore vp core))
          (GeneralScheme.SignatureCore vp core))

/-- `typedP` over a core bundle (it depends on the bundle only through its core). -/
def typedC (codec : CoreWireCodec vp.params core) (dflt : core.Y)
    (mb : List Byte → OracleComp (FSpecP (List Byte)) (List Byte × List Byte)) :
    PublicKeyCore core →
      OracleComp (FSpecP (GeneralScheme.SignatureCore vp core))
        (List Byte × GeneralScheme.SignatureCore vp core) :=
  fun pk => (fun out : List Byte × List Byte =>
      (out.1, ((decodeSignature vp codec out.2).toOption).getD (constSigC dflt))) <$>
    simulateQ (signPC codec) (mb (encodePublicKey codec pk))

end Typed

section Uniform

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

theorem typedP_eq_typedC (codec : CoreWireCodec vp.params prims.core)
    (mb : List Byte → OracleComp (FSpecP (List Byte)) (List Byte × List Byte)) :
    typedP (prims := prims) codec mb = typedC codec default mb := rfl

theorem forger_ext {A B : Forger vp prims optRand pkSeedDist}
    (h : ∀ pk, A.main pk = B.main pk) : A = B := by
  cases A; cases B
  congr 1
  exact funext h

/-- The Reduction's typed strong forger built from a byte forger whose port is answered by `g`
is the forger `typedC …` with its port answered by `g`. -/
theorem bytesToTypedS_inst (codec : CoreWireCodec vp.params prims.core) (g : CF St Blk)
    (mb : List Byte → OracleComp (FSpecP (List Byte)) (List Byte × List Byte)) :
    (bytesToTypedS (prims := prims) (codec := codec) (optRand := optRand)
      (pkSeedDist := pkSeedDist) ⟨fun pk => simulateQ (instImpl g) (mb pk)⟩).toUnforgeableAdversary =
      fusedF optRand pkSeedDist g (typedC codec default mb) :=
  forger_ext fun pk => (typedP_inst codec optRand pkSeedDist g mb pk).symm

/-- The same for the EUF wrapper. -/
theorem bytesToTyped_inst (codec : CoreWireCodec vp.params prims.core) (g : CF St Blk)
    (mb : List Byte → OracleComp (FSpecP (List Byte)) (List Byte × List Byte)) :
    bytesToTyped (prims := prims) (codec := codec) (optRand := optRand)
      (pkSeedDist := pkSeedDist) ⟨fun pk => simulateQ (instImpl g) (mb pk)⟩ =
      fusedF optRand pkSeedDist g (typedC codec default mb) :=
  forger_ext fun pk => (typedP_inst codec optRand pkSeedDist g mb pk).symm

variable (optRand pkSeedDist)

/-- **The SUF port program does not depend on `Thash`, `H_msg`.** -/
theorem msgOpenWVP_withTH (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
    (mainP : PortForgerProg vp prims) :
    msgOpenWVP (prims := Open.withTH prims T H) optRand pkSeedDist sufCheckO mainP =
      msgOpenWVP optRand pkSeedDist sufCheckO mainP := rfl

/-- **The EUF port program does not depend on `Thash`, `H_msg`.** -/
theorem msgOpenVP_withTH (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
    (mainP : PortForgerProg vp prims) :
    msgOpenVP (prims := Open.withTH prims T H) optRand pkSeedDist mainP =
      msgOpenVP optRand pkSeedDist mainP := rfl

end Uniform

end Ideal.Realize.Msg

#print axioms Ideal.Realize.Msg.portR_openKeygen
#print axioms Ideal.Realize.Msg.portR_openSign
#print axioms Ideal.Realize.Msg.msgOpenWVP_fusion
#print axioms Ideal.Realize.Msg.msgOpenVP_fusion
#print axioms Ideal.Realize.Msg.bytesToTypedS_inst
#print axioms Ideal.Realize.Msg.msgOpenWVP_withTH
#print axioms Ideal.Realize.Msg.msgOpenVP_withTH
