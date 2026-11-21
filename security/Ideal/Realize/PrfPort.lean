import Ideal.Realize.PrfTr
import Ideal.Realize.MsgPort

/-!
# The open `PRF` distinguishers for a forger with a compression port

`QSpec prims D = unifSpec + ((hS + (D →ₒ Y)) + HSpec prims)`: the interface `PSpec prims D` of
`Reduction.Open.bPrfWOpen` with a port for compression queries next to the PRF game oracle.

* `embQ` (forward a `PSpec` program), `portP g` (answer the port by `g`), `portQ` (a port query),
  `restrictP` (domain restriction, port forwarded); `portP_embQ`, `portP_restrictP`;
* `bPrfWOpenP`, `bPrfWCOpenP` (SUF), `bPrfOpenP`, `bPrfCOpenP` (EUF): the port programs;
* **Fusion** `bPrfWCOpenP_fusion`, `bPrfCOpenP_fusion`: answering the port by `g` gives
  `bPrfWCOpen sufCheckOpen` / `bPrfCOpen` at the forger with its port answered by `g`;
* `bPrfWCOpenP_withTH`, `bPrfCOpenP_withTH`: independence of `Thash`, `H_msg`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize.Prf

open Reduction Reduction.Open
open Ideal.Realize.Msg (harnP harnP_fusion sigSignOracle_fusion harnessSignOracle_fusion fusedF)

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Spec

variable {p : Params} {prims : Primitives p} {D D' : Type} {α : Type}

/-- The interface of the port programs. -/
abbrev QSpec (prims : Primitives p) (D : Type) :=
  unifSpec + ((hS St Blk + (D →ₒ prims.Y)) + HSpec prims)

/-- Forward a `PSpec` program into `QSpec`. -/
def embQ : QueryImpl (PSpec prims D) (OracleComp (QSpec prims D))
  | .inl n => (liftM ((QSpec prims D).query (.inl n)) : OracleComp (QSpec prims D) _)
  | .inr (.inl d) => (liftM ((QSpec prims D).query (.inr (.inl (.inr d)))) :
      OracleComp (QSpec prims D) _)
  | .inr (.inr q) => (liftM ((QSpec prims D).query (.inr (.inr q))) :
      OracleComp (QSpec prims D) _)

/-- Answer the port by `g`; forward everything else. -/
def portP (g : CF St Blk) : QueryImpl (QSpec prims D) (OracleComp (PSpec prims D))
  | .inl n => (liftM ((PSpec prims D).query (.inl n)) : OracleComp (PSpec prims D) _)
  | .inr (.inl (.inl q)) => pure (g q)
  | .inr (.inl (.inr d)) => (liftM ((PSpec prims D).query (.inr (.inl d))) :
      OracleComp (PSpec prims D) _)
  | .inr (.inr q) => (liftM ((PSpec prims D).query (.inr (.inr q))) :
      OracleComp (PSpec prims D) _)

/-- A port query. -/
def portQ (q : St × Blk) : OracleComp (QSpec prims D) St :=
  (liftM ((QSpec prims D).query (.inr (.inl (.inl q)))) : OracleComp (QSpec prims D) St)

/-- Domain restriction of the PRF game oracle, port forwarded. -/
def restrictP [Inhabited prims.Y] (r : D → Option D') :
    QueryImpl (QSpec prims D) (OracleComp (QSpec prims D'))
  | .inl n => (liftM ((QSpec prims D').query (.inl n)) : OracleComp (QSpec prims D') _)
  | .inr (.inl (.inl q)) => (liftM ((QSpec prims D').query (.inr (.inl (.inl q)))) :
      OracleComp (QSpec prims D') _)
  | .inr (.inl (.inr d)) =>
    match r d with
    | some d' => (liftM ((QSpec prims D').query (.inr (.inl (.inr d')))) :
        OracleComp (QSpec prims D') _)
    | none => pure (default : prims.Y)
  | .inr (.inr q) => (liftM ((QSpec prims D').query (.inr (.inr q))) :
      OracleComp (QSpec prims D') _)

theorem portP_embQ (g : CF St Blk) (X : OracleComp (PSpec prims D) α) :
    simulateQ (portP g) (simulateQ embQ X) = X := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, ih]
    rcases t with n | d | q
    · simp only [embQ]; rw [simulateQ_spec_query]; rfl
    · simp only [embQ]; rw [simulateQ_spec_query]; rfl
    · simp only [embQ]; rw [simulateQ_spec_query]; rfl

theorem portP_liftM (g : CF St Blk) (ob : ProbComp α) :
    simulateQ (portP (prims := prims) (D := D) g) (liftM ob : OracleComp (QSpec prims D) α) =
      (liftM ob : OracleComp (PSpec prims D) α) := by
  induction ob using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n k ih =>
    rw [liftM_bind, liftM_bind, simulateQ_bind]
    simp only [ih]
    have : simulateQ (portP (prims := prims) (D := D) g)
        (liftM (liftM (unifSpec.query n) : ProbComp _) : OracleComp (QSpec prims D) _) =
        (liftM (liftM (unifSpec.query n) : ProbComp _) : OracleComp (PSpec prims D) _) := by
      show simulateQ (portP g) (liftM ((QSpec prims D).query (.inl n))) = _
      rw [simulateQ_spec_query]
      rfl
    rw [this]

theorem portP_portQ (g : CF St Blk) (q : St × Blk) :
    simulateQ (portP (prims := prims) (D := D) g) (portQ q) = pure (g q) := by
  unfold portQ
  rw [simulateQ_spec_query]
  rfl

theorem portP_restrictP [Inhabited prims.Y] (g : CF St Blk) (r : D → Option D')
    (X : OracleComp (QSpec prims D) α) :
    simulateQ (portP g) (simulateQ (restrictP r) X) =
      simulateQ (restrictO (prims := prims) r) (simulateQ (portP g) X) := by
  refine Ideal.Realize.simulateQ_comm_of_step _ _ _ _ (fun t => ?_) X
  rcases t with n | (q | d) | q
  · simp only [restrictP, portP]
    rw [simulateQ_spec_query, simulateQ_spec_query]
    rfl
  · simp only [restrictP, portP, simulateQ_pure]
    rw [simulateQ_spec_query]
    rfl
  · simp only [restrictP, portP]
    rw [simulateQ_spec_query]
    cases hd : r d with
    | none => simp [restrictO, hd]
    | some d' =>
      simp only
      rw [simulateQ_spec_query]
      simp only [restrictO, hd]
      rfl
  · simp only [restrictP, portP]
    rw [simulateQ_spec_query, simulateQ_spec_query]
    rfl

end Spec

section Programs

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)

/-- The PRF-game domain before the restriction. -/
abbrev D₀ (prims : Primitives vp.params) : Type := prims.PkSeed × Adrs

/-- Everything `bPrfWOpenP` does after sampling `PK.seed`. -/
noncomputable def bRestWOpenP (wO : OpenCheck vp prims) (mainP : PortForgerProg vp prims)
    (pkSeed : prims.PkSeed) : OracleComp (QSpec prims (D₀ prims)) Bool :=
  (liftM ($ᵗ prims.SkPrf : ProbComp prims.SkPrf) :
      OracleComp (QSpec prims (D₀ prims)) prims.SkPrf) >>= fun skPrf =>
    simulateQ embQ (openKeygenP prims pkSeed) >>= fun root =>
      (simulateQ (harnP (portQ (prims := prims) (D := D₀ prims))
        (sigSignOracle (fun m => simulateQ embQ (openSignP optRand ⟨pkSeed, root⟩ skPrf m))))
          (mainP ⟨pkSeed, root⟩)).run [] >>= fun z =>
        simulateQ embQ (simulateQ (hashEmb prims (D₀ prims)) (wO ⟨pkSeed, root⟩ z.1 z.2))

/-- The SUF port program before the restriction. -/
noncomputable def bPrfWOpenP (wO : OpenCheck vp prims) (mainP : PortForgerProg vp prims) :
    OracleComp (QSpec prims (D₀ prims)) Bool :=
  (liftM pkSeedDist : OracleComp (QSpec prims (D₀ prims)) prims.PkSeed) >>=
    bRestWOpenP optRand wO mainP

/-- **The open SUF `PRF` distinguisher for a port forger.** -/
noncomputable def bPrfWCOpenP (wO : OpenCheck vp prims) (mainP : PortForgerProg vp prims) :
    OracleComp (QSpec prims (prims.PkSeed × SkAdrs vp)) Bool :=
  simulateQ (restrictP (prims := prims) (skRestrict vp prims)) (bPrfWOpenP optRand pkSeedDist wO mainP)

/-- Everything `bPrfOpenP` does after sampling `PK.seed`. -/
noncomputable def bRestOpenP (mainP : PortForgerProg vp prims) (pkSeed : prims.PkSeed) :
    OracleComp (QSpec prims (D₀ prims)) Bool :=
  (liftM ($ᵗ prims.SkPrf : ProbComp prims.SkPrf) :
      OracleComp (QSpec prims (D₀ prims)) prims.SkPrf) >>= fun skPrf =>
    simulateQ embQ (openKeygenP prims pkSeed) >>= fun root =>
      (simulateQ (harnP (portQ (prims := prims) (D := D₀ prims))
        (harnessSignOracle (vp := vp) (prims := prims)
          (fun m => simulateQ embQ (openSignP optRand ⟨pkSeed, root⟩ skPrf m))))
          (mainP ⟨pkSeed, root⟩)).run [] >>= fun z =>
        simulateQ embQ (simulateQ (hashEmb prims (D₀ prims))
          (GeneralScheme.verifyInternalM vp prims.core z.1.1 z.1.2 ⟨pkSeed, root⟩ :
            OracleComp (publicHashSpec prims.core) Bool)) >>= fun v =>
          pure (decide (z.1.1 ∉ z.2) && v)

/-- The EUF port program before the restriction. -/
noncomputable def bPrfOpenP (mainP : PortForgerProg vp prims) :
    OracleComp (QSpec prims (D₀ prims)) Bool :=
  (liftM pkSeedDist : OracleComp (QSpec prims (D₀ prims)) prims.PkSeed) >>=
    bRestOpenP optRand mainP

/-- **The open EUF `PRF` distinguisher for a port forger.** -/
noncomputable def bPrfCOpenP (mainP : PortForgerProg vp prims) :
    OracleComp (QSpec prims (prims.PkSeed × SkAdrs vp)) Bool :=
  simulateQ (restrictP (prims := prims) (skRestrict vp prims)) (bPrfOpenP optRand pkSeedDist mainP)

theorem bPrfWOpenP_fusion (g : CF St Blk) (wO : OpenCheck vp prims)
    (mainP : PortForgerProg vp prims) :
    simulateQ (portP g) (bPrfWOpenP optRand pkSeedDist wO mainP) =
      bPrfWOpen wO (fusedF optRand pkSeedDist g mainP) := by
  unfold bPrfWOpenP bRestWOpenP bPrfWOpen bRestWOpen
  rw [simulateQ_bind, portP_liftM]
  refine bind_congr fun pkSeed => ?_
  rw [simulateQ_bind, portP_liftM]
  refine bind_congr fun skPrf => ?_
  rw [simulateQ_bind, portP_embQ]
  refine bind_congr fun root => ?_
  rw [simulateQ_bind]
  have h := harnP_fusion (portP g) g (fun n => rfl) (portQ (prims := prims) (D := D₀ prims))
    (portP_portQ g)
    (sigSignOracle (fun m => simulateQ embQ (openSignP optRand ⟨pkSeed, root⟩ skPrf m)))
    (sigSignOracle (fun m => simulateQ (portP g)
      (simulateQ embQ (openSignP optRand ⟨pkSeed, root⟩ skPrf m))))
    (fun m s => sigSignOracle_fusion _ _ m s) (mainP ⟨pkSeed, root⟩) []
  rw [h]
  have hs : (fun m => simulateQ (portP g)
      (simulateQ embQ (openSignP optRand ⟨pkSeed, root⟩ skPrf m))) =
      openSignP optRand ⟨pkSeed, root⟩ skPrf := funext fun m => portP_embQ g _
  rw [hs]
  refine bind_congr fun z => ?_
  exact portP_embQ g _

theorem bPrfOpenP_fusion (g : CF St Blk) (mainP : PortForgerProg vp prims) :
    simulateQ (portP g) (bPrfOpenP optRand pkSeedDist mainP) =
      bPrfOpen (fusedF optRand pkSeedDist g mainP) := by
  unfold bPrfOpenP bRestOpenP bPrfOpen bRestOpen
  rw [simulateQ_bind, portP_liftM]
  refine bind_congr fun pkSeed => ?_
  rw [simulateQ_bind, portP_liftM]
  refine bind_congr fun skPrf => ?_
  rw [simulateQ_bind, portP_embQ]
  refine bind_congr fun root => ?_
  rw [simulateQ_bind]
  have h := harnP_fusion (portP g) g (fun n => rfl) (portQ (prims := prims) (D := D₀ prims))
    (portP_portQ g)
    (harnessSignOracle (vp := vp) (prims := prims)
      (fun m => simulateQ embQ (openSignP optRand ⟨pkSeed, root⟩ skPrf m)))
    (harnessSignOracle (vp := vp) (prims := prims) (fun m => simulateQ (portP g)
      (simulateQ embQ (openSignP optRand ⟨pkSeed, root⟩ skPrf m))))
    (fun m s => harnessSignOracle_fusion _ _ m s) (mainP ⟨pkSeed, root⟩) []
  rw [h]
  have hs : (fun m => simulateQ (portP g)
      (simulateQ embQ (openSignP optRand ⟨pkSeed, root⟩ skPrf m))) =
      openSignP optRand ⟨pkSeed, root⟩ skPrf := funext fun m => portP_embQ g _
  rw [hs]
  refine bind_congr fun z => ?_
  rw [simulateQ_bind, portP_embQ]
  simp

/-- **Fusion (SUF).** -/
theorem bPrfWCOpenP_fusion (g : CF St Blk) (wO : OpenCheck vp prims)
    (mainP : PortForgerProg vp prims) :
    simulateQ (portP g) (bPrfWCOpenP optRand pkSeedDist wO mainP) =
      bPrfWCOpen wO (fusedF optRand pkSeedDist g mainP) := by
  unfold bPrfWCOpenP bPrfWCOpen
  rw [portP_restrictP, bPrfWOpenP_fusion]

/-- **Fusion (EUF).** -/
theorem bPrfCOpenP_fusion (g : CF St Blk) (mainP : PortForgerProg vp prims) :
    simulateQ (portP g) (bPrfCOpenP optRand pkSeedDist mainP) =
      bPrfCOpen (fusedF optRand pkSeedDist g mainP) := by
  unfold bPrfCOpenP bPrfCOpen
  rw [portP_restrictP, bPrfOpenP_fusion]

variable {optRand pkSeedDist}

/-- The SUF port program does not depend on `Thash`, `H_msg`. -/
theorem bPrfWCOpenP_withTH (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
    (mainP : PortForgerProg vp prims) :
    bPrfWCOpenP (prims := withTH prims T H) optRand pkSeedDist sufCheckOpen mainP =
      bPrfWCOpenP optRand pkSeedDist sufCheckOpen mainP := by krfl

/-- The EUF port program does not depend on `Thash`, `H_msg`. -/
theorem bPrfCOpenP_withTH (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
    (mainP : PortForgerProg vp prims) :
    bPrfCOpenP (prims := withTH prims T H) optRand pkSeedDist mainP =
      bPrfCOpenP optRand pkSeedDist mainP := by krfl

end Programs

end Ideal.Realize.Prf

#print axioms Ideal.Realize.Prf.portP_restrictP
#print axioms Ideal.Realize.Prf.bPrfWCOpenP_fusion
#print axioms Ideal.Realize.Prf.bPrfCOpenP_fusion
#print axioms Ideal.Realize.Prf.bPrfWCOpenP_withTH
#print axioms Ideal.Realize.Prf.bPrfCOpenP_withTH
