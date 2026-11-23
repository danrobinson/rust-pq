import Ideal.Direct.MDBadSharp

/-!
# One typed program for both sides of the hop (`status/DIRECT.md` §12)

The simulator of the ROM side needs the public key of the run (relevance is narrow, §10.1), which
the realisers' port program `PprfS` does not expose to its port handler.  Here the port is
**tagged**: `PprfST` is `PprfS` with every compression query of the forger issued as
`(pk, q)`, `pk` the public key of the run (`portQT`).

* `untag_PprfST`: forgetting the tag gives `PprfS` back (an equality of programs), so the walk
  program of the deferred side is `XS = walkProg (simulateQ untagT PprfST)` (`XS_eq_untag`).
* `romH k`: the ROM-side handler of the same program at the secret seed `k`: coins forwarded, a
  tagged port query `(pk, q)` answered by the simulator's step `simStepR pk q` on its table `T`,
  the PRF oracle at `(PK.seed, a)` by the `Thash` oracle at `(PK.seed, key a, [k])`, hash and
  `PRF_msg` queries by the oracles.
* `Yrom S oR := k ← $; (simulateQ (romH k) PprfST).run' ∅`, the ROM-side game.

The remaining statement of the hop splits into
* **`RomGameSuf`** (H3, exact): VCVio's SUF experiment of `simAdv` in the ROM is `Yrom`;
* **`DeferCoreSuf`** (the probabilistic core): the deferred game of `XS` (with `¬ Bad`) is at most
  `Yrom` plus `epsHalf + qs/2^128`;

and `DeferSimSufNB` follows from the two (`deferSimSufNB_of_parts`); EUF twins likewise.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security SignatureAlg ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Ideal.Direct.Rom

open Ideal.Realize Ideal.Realize.Prf Reduction Reduction.Open
open Ideal.Realize.Msg (Rd mainC optRand₀ harnP)

/-! ## The tagged interface -/

/-- The tagged port: a compression query with the public key of the run. -/
abbrev PortT : OracleSpec (PublicKeyCore Cr × (St × Blk)) := (PublicKeyCore Cr × (St × Blk)) →ₒ St

/-- The interface of the tagged port programs (`QSpec Rd D` with the port tagged). -/
abbrev QT (D : Type) := unifSpec + ((PortT + (D →ₒ Bytes 16)) + HSpec Rd)

section Tagged

variable {D D' α : Type}

/-- Forward a `PSpec` program into `QT`. -/
def embQT : QueryImpl (Reduction.Open.PSpec Rd D) (OracleComp (QT D))
  | .inl n => (liftM ((QT D).query (.inl n)) : OracleComp (QT D) _)
  | .inr (.inl d) => (liftM ((QT D).query (.inr (.inl (.inr d)))) : OracleComp (QT D) _)
  | .inr (.inr q) => (liftM ((QT D).query (.inr (.inr q))) : OracleComp (QT D) _)

/-- A tagged port query. -/
def portQT (pk : PublicKeyCore Cr) (q : St × Blk) : OracleComp (QT D) St :=
  (liftM ((QT D).query (.inr (.inl (.inl (pk, q))))) : OracleComp (QT D) St)

/-- Domain restriction of the PRF game oracle, tagged port forwarded. -/
def restrictPT (r : D → Option D') : QueryImpl (QT D) (OracleComp (QT D'))
  | .inl n => (liftM ((QT D').query (.inl n)) : OracleComp (QT D') _)
  | .inr (.inl (.inl q)) => (liftM ((QT D').query (.inr (.inl (.inl q)))) : OracleComp (QT D') _)
  | .inr (.inl (.inr d)) =>
    match r d with
    | some d' => (liftM ((QT D').query (.inr (.inl (.inr d')))) : OracleComp (QT D') _)
    | none => pure (default : Bytes 16)
  | .inr (.inr q) => (liftM ((QT D').query (.inr (.inr q))) : OracleComp (QT D') _)

/-- Forget the tag. -/
def untagT : QueryImpl (QT D) (OracleComp (QSpec Rd D))
  | .inl n => (liftM ((QSpec Rd D).query (.inl n)) : OracleComp (QSpec Rd D) _)
  | .inr (.inl (.inl pq)) => portQ (prims := Rd) (D := D) pq.2
  | .inr (.inl (.inr d)) => (liftM ((QSpec Rd D).query (.inr (.inl (.inr d)))) :
      OracleComp (QSpec Rd D) _)
  | .inr (.inr q) => (liftM ((QSpec Rd D).query (.inr (.inr q))) : OracleComp (QSpec Rd D) _)

theorem untag_embQT (X : OracleComp (Reduction.Open.PSpec Rd D) α) :
    simulateQ untagT (simulateQ embQT X) = simulateQ embQ X := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext t
  rcases t with n | d | q
  · simp only [QueryImpl.apply_compose, embQT, embQ]; erw [simulateQ_spec_query]; rfl
  · simp only [QueryImpl.apply_compose, embQT, embQ]; erw [simulateQ_spec_query]; rfl
  · simp only [QueryImpl.apply_compose, embQT, embQ]; erw [simulateQ_spec_query]; rfl

theorem untag_restrictPT (r : D → Option D') (X : OracleComp (QT D) α) :
    simulateQ untagT (simulateQ (restrictPT r) X) =
      simulateQ (restrictP (prims := Rd) r) (simulateQ untagT X) := by
  refine Ideal.Realize.simulateQ_comm_of_step _ _ _ _ (fun t => ?_) X
  rcases t with n | (pq | d) | q
  · simp only [restrictPT, untagT]
    rw [simulateQ_spec_query, simulateQ_spec_query]; rfl
  · simp only [restrictPT, untagT]
    rw [simulateQ_spec_query]
    unfold portQ
    rw [simulateQ_spec_query]; rfl
  · show simulateQ untagT (restrictPT r (.inr (.inl (.inr d)))) =
        simulateQ (restrictP (prims := Rd) r)
          ((liftM ((QSpec Rd D).query (.inr (.inl (.inr d))))) : OracleComp (QSpec Rd D) _)
    rw [simulateQ_spec_query]
    cases hd : r d with
    | none => simp [restrictPT, restrictP, hd]; rfl
    | some d' =>
      simp only [restrictPT, restrictP, hd]
      rw [simulateQ_spec_query]
      rfl
  · simp only [restrictPT, untagT]
    rw [simulateQ_spec_query, simulateQ_spec_query]; rfl

theorem untag_liftM (ob : ProbComp α) :
    simulateQ (untagT (D := D)) (liftM ob : OracleComp (QT D) α) =
      (liftM ob : OracleComp (QSpec Rd D) α) := by
  induction ob using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n k ih =>
    rw [liftM_bind, liftM_bind, simulateQ_bind]
    simp only [ih]
    have : simulateQ (untagT (D := D))
        (liftM (liftM (unifSpec.query n) : ProbComp _) : OracleComp (QT D) _) =
        (liftM (liftM (unifSpec.query n) : ProbComp _) : OracleComp (QSpec Rd D) _) := by
      show simulateQ untagT (liftM ((QT D).query (.inl n))) = _
      rw [simulateQ_spec_query]
      rfl
    rw [this]

/-- A stateless interpretation of the base monad of a stateful simulation. -/
theorem simulateQ_run_map_of_step {ι₁ ι₂ ι₃ : Type} {spec₁ : OracleSpec ι₁}
    {spec₂ : OracleSpec ι₂} {spec₃ : OracleSpec ι₃} {σ β : Type}
    (φ : QueryImpl spec₂ (OracleComp spec₃))
    (G : QueryImpl spec₁ (StateT σ (OracleComp spec₂)))
    (G' : QueryImpl spec₁ (StateT σ (OracleComp spec₃)))
    (h : ∀ t s, simulateQ φ ((G t).run s) = (G' t).run s) (oa : OracleComp spec₁ β) (s : σ) :
    simulateQ φ ((simulateQ G oa).run s) = (simulateQ G' oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, h, ih]

end Tagged

/-! ## The tagged port programs -/

section Programs

variable (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (pkSeedDist : ProbComp (Bytes 16))

/-- Everything the tagged SUF program does after sampling `PK.seed`. -/
noncomputable def bRestWOpenPT (wO : OpenCheck Link.vp Rd) (mainP : PortForgerProg Link.vp Rd)
    (pkSeed : Bytes 16) : OracleComp (QT (D₀ Rd)) Bool :=
  (liftM ($ᵗ (Bytes 16) : ProbComp (Bytes 16)) : OracleComp (QT (D₀ Rd)) (Bytes 16)) >>= fun skPrf =>
    simulateQ embQT (openKeygenP Rd pkSeed) >>= fun root =>
      (simulateQ (harnP (portQT ⟨pkSeed, root⟩)
        (sigSignOracle (fun m => simulateQ embQT
          (openSignP (prims := Rd) (optRand₀ oR) ⟨pkSeed, root⟩ skPrf m))))
          (mainP ⟨pkSeed, root⟩)).run [] >>= fun z =>
        simulateQ embQT (simulateQ (hashEmb Rd (D₀ Rd)) (wO ⟨pkSeed, root⟩ z.1 z.2))

/-- Everything the tagged EUF program does after sampling `PK.seed`. -/
noncomputable def bRestOpenPT (mainP : PortForgerProg Link.vp Rd) (pkSeed : Bytes 16) :
    OracleComp (QT (D₀ Rd)) Bool :=
  (liftM ($ᵗ (Bytes 16) : ProbComp (Bytes 16)) : OracleComp (QT (D₀ Rd)) (Bytes 16)) >>= fun skPrf =>
    simulateQ embQT (openKeygenP Rd pkSeed) >>= fun root =>
      (simulateQ (harnP (portQT ⟨pkSeed, root⟩)
        (harnessSignOracle (vp := Link.vp) (prims := Rd)
          (fun m => simulateQ embQT (openSignP (prims := Rd) (optRand₀ oR) ⟨pkSeed, root⟩ skPrf m))))
          (mainP ⟨pkSeed, root⟩)).run [] >>= fun z =>
        simulateQ embQT (simulateQ (hashEmb Rd (D₀ Rd))
          (GeneralScheme.verifyInternalM Link.vp Rd.core z.1.1 z.1.2 ⟨pkSeed, root⟩ :
            OracleComp (publicHashSpec Rd.core) Bool)) >>= fun v =>
          pure (decide (z.1.1 ∉ z.2) && v)

/-- **The tagged SUF program.** -/
noncomputable def PprfST (S : ForgerI) : OracleComp (QT Dsk) Bool :=
  simulateQ (restrictPT (D' := Dsk) (skRestrict Link.vp Rd))
    ((liftM pkSeedDist : OracleComp (QT (D₀ Rd)) (Bytes 16)) >>=
      bRestWOpenPT oR sufCheckOpen (mainC S))

/-- **The tagged EUF program.** -/
noncomputable def PprfET (S : ForgerI) : OracleComp (QT Dsk) Bool :=
  simulateQ (restrictPT (D' := Dsk) (skRestrict Link.vp Rd))
    ((liftM pkSeedDist : OracleComp (QT (D₀ Rd)) (Bytes 16)) >>= bRestOpenPT oR (mainC S))

theorem untag_harnP (pk : PublicKeyCore Cr) {σ Sig β : Type}
    (so : QueryImpl (List Byte →ₒ Sig) (StateT σ (OracleComp (QT (D₀ Rd)))))
    (so' : QueryImpl (List Byte →ₒ Sig) (StateT σ (OracleComp (QSpec Rd (D₀ Rd)))))
    (hso : ∀ m s, simulateQ untagT ((so m).run s) = (so' m).run s)
    (oa : OracleComp (FSpecP Sig) β) (s : σ) :
    simulateQ untagT ((simulateQ (harnP (portQT pk) so) oa).run s) =
      (simulateQ (harnP (portQ (prims := Rd) (D := D₀ Rd)) so') oa).run s := by
  refine simulateQ_run_map_of_step _ _ _ (fun t s => ?_) oa s
  rcases t with n | q | m
  · simp only [harnP, StateT.run_monadLift, simulateQ_bind, simulateQ_pure, monadLift_self]
    rw [simulateQ_spec_query]
    rfl
  · simp only [harnP, StateT.run_monadLift, simulateQ_bind, simulateQ_pure, monadLift_self]
    unfold portQT
    rw [simulateQ_spec_query]
    rfl
  · exact hso m s

/-- **Forgetting the tag gives the realisers' SUF port program.** -/
theorem untag_PprfST (S : ForgerI) :
    simulateQ untagT (PprfST oR pkSeedDist S) = PprfS S oR pkSeedDist := by
  unfold PprfST PprfS bPrfWCOpenP bPrfWOpenP
  refine (untag_restrictPT (D' := Dsk) _ _).trans ?_
  congr 1
  rw [simulateQ_bind, untag_liftM]
  refine bind_congr fun pkSeed => ?_
  unfold bRestWOpenPT bRestWOpenP
  rw [simulateQ_bind, untag_liftM]
  refine bind_congr fun skPrf => ?_
  rw [simulateQ_bind, untag_embQT]
  refine bind_congr fun root => ?_
  rw [simulateQ_bind, untag_harnP ⟨pkSeed, root⟩ _
    (sigSignOracle (fun m => simulateQ embQ
      (openSignP (prims := Rd) (optRand₀ oR) ⟨pkSeed, root⟩ skPrf m)))
    (fun m s => by
      rw [Ideal.Realize.Msg.sigSignOracle_fusion]
      exact congrArg (fun f => (sigSignOracle f m).run s) (funext fun m' => untag_embQT _))]
  refine bind_congr fun z => ?_
  rw [untag_embQT]

/-- **Forgetting the tag gives the realisers' EUF port program.** -/
theorem untag_PprfET (S : ForgerI) :
    simulateQ untagT (PprfET oR pkSeedDist S) = PprfE S oR pkSeedDist := by
  unfold PprfET PprfE bPrfCOpenP bPrfOpenP
  refine (untag_restrictPT (D' := Dsk) _ _).trans ?_
  congr 1
  rw [simulateQ_bind, untag_liftM]
  refine bind_congr fun pkSeed => ?_
  unfold bRestOpenPT bRestOpenP
  rw [simulateQ_bind, untag_liftM]
  refine bind_congr fun skPrf => ?_
  rw [simulateQ_bind, untag_embQT]
  refine bind_congr fun root => ?_
  rw [simulateQ_bind, untag_harnP ⟨pkSeed, root⟩ _
    (harnessSignOracle (vp := Link.vp) (prims := Rd) (fun m => simulateQ embQ
      (openSignP (prims := Rd) (optRand₀ oR) ⟨pkSeed, root⟩ skPrf m)))
    (fun m s => by
      rw [Ideal.Realize.Msg.harnessSignOracle_fusion]
      exact congrArg (fun f => (harnessSignOracle (vp := Link.vp) (prims := Rd) f m).run s)
        (funext fun m' => untag_embQT _))]
  refine bind_congr fun z => ?_
  rw [simulateQ_bind, untag_embQT]
  simp

theorem XS_eq_untag (S : ForgerI) :
    XS S oR pkSeedDist = walkProg (simulateQ untagT (PprfST oR pkSeedDist S)) := by
  rw [untag_PprfST]; rfl

theorem XE_eq_untag (S : ForgerI) :
    XE S oR pkSeedDist = walkProg (simulateQ untagT (PprfET oR pkSeedDist S)) := by
  rw [untag_PprfET]; rfl

end Programs

/-! ## The ROM-side handler and game -/

section RomSide

/-- A query of the ROM base interface. -/
def rq (t : RS.Domain) : OracleComp RS (RS.Range t) := (liftM (RS.query t) : OracleComp RS _)

/-- A fresh 256-bit value, by the ROM interface's coins. -/
noncomputable def freshR : OracleComp RS St := (liftM ($ᵗ St : ProbComp St) : OracleComp RS St)

/-- **The simulator's step over the ROM base interface** (`simStep` with its coins and oracle
queries issued directly). -/
noncomputable def simStepR (pk : PublicKeyCore Cr) (q : St × Blk) :
    StateT (hS St Blk).QueryCache (OracleComp RS) St := fun T =>
  match T q with
  | some v => pure (v, T)
  | none => do
    let u ← freshR
    match relQ pk T q with
    | none => pure (u, T.cacheQuery q u)
    | some t => do
      let y ← rq (.inr t)
      let v := overlay t y u
      pure (v, T.cacheQuery q v)

/-- **The ROM-side handler of the tagged program at the secret seed `k`.** -/
noncomputable def romH (k : Bytes 16) :
    QueryImpl (QT Dsk) (StateT (hS St Blk).QueryCache (OracleComp RS))
  | .inl n => (monadLift (rq (.inl n)) : StateT (hS St Blk).QueryCache (OracleComp RS) _)
  | .inr (.inl (.inl pq)) => simStepR pq.1 pq.2
  | .inr (.inl (.inr d)) => (monadLift (rq (.inr (.inl
      (PublicHashQuery.thash d.1 (Cr.adrsToKey d.2.1) [k])))) :
        StateT (hS St Blk).QueryCache (OracleComp RS) _)
  | .inr (.inr (.inl q)) => (monadLift (rq (.inr (.inl q))) :
      StateT (hS St Blk).QueryCache (OracleComp RS) _)
  | .inr (.inr (.inr t)) => (monadLift (rq (.inr (.inr ⟨t.1, t.2.1, t.2.2⟩))) :
      StateT (hS St Blk).QueryCache (OracleComp RS) _)

/-- **The ROM-side game (SUF).** -/
noncomputable def Yrom (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) :
    OracleComp RS Bool := do
  let k ← (liftM ($ᵗ (Bytes 16) : ProbComp (Bytes 16)) : OracleComp RS (Bytes 16))
  (simulateQ (romH k) (PprfST oR ($ᵗ (Bytes 16)) S)).run' ∅

/-- **The ROM-side game (EUF).** -/
noncomputable def YromE (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) :
    OracleComp RS Bool := do
  let k ← (liftM ($ᵗ (Bytes 16) : ProbComp (Bytes 16)) : OracleComp RS (Bytes 16))
  (simulateQ (romH k) (PprfET oR ($ᵗ (Bytes 16)) S)).run' ∅

end RomSide

/-! ## The split of the remaining statement -/

/-- **H3 (SUF), exact game match, not proved**: VCVio's SUF advantage of the simulator in the
ROM is the success probability of the ROM-side game `Yrom`. -/
def RomGameSuf : Prop :=
  ∀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)),
    strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec Cr)) (simAdv S oR ($ᵗ (Bytes 16))) =
      (ProbCompRuntime.rom (hashSpec Cr)).evalDist (Yrom S oR) {true}

/-- **H3 (EUF), not proved.** -/
def RomGameEuf : Prop :=
  ∀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)),
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec Cr)) (simAdvE S oR ($ᵗ (Bytes 16))) =
      (ProbCompRuntime.rom (hashSpec Cr)).evalDist (YromE S oR) {true}

/-- **The probabilistic core (SUF), not proved**: the deferred game of the walk program of the
tagged program (`= XS`, `XS_eq_untag`), winning with `Bad` failing, against the ROM-side game. -/
def DeferCoreSuf : Prop :=
  ∀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (qf qs ℓ : ℕ),
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0) →
    (∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) →
    Pr{let w ← defRun (walkProg (simulateQ untagT (PprfST oR ($ᵗ (Bytes 16)) S)))}[
        w.1 = true ∧ ¬ Gs.Bad w.2] ≤
      (ProbCompRuntime.rom (hashSpec Cr)).evalDist (Yrom S oR) {true} +
        epsHalf qf qs ℓ + (qs : ℝ≥0∞) / 2 ^ 128

/-- **The probabilistic core (EUF), not proved.** -/
def DeferCoreEuf : Prop :=
  ∀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (qf qs ℓ : ℕ),
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs) →
    (∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0) →
    (∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) →
    Pr{let w ← defRun (walkProg (simulateQ untagT (PprfET oR ($ᵗ (Bytes 16)) S)))}[
        w.1 = true ∧ ¬ Gs.Bad w.2] ≤
      (ProbCompRuntime.rom (hashSpec Cr)).evalDist (YromE S oR) {true} +
        epsHalf qf qs ℓ + (qs : ℝ≥0∞) / 2 ^ 128

theorem deferSimSufNB_of_parts (h3 : RomGameSuf) (hc : DeferCoreSuf) : DeferSimSufNB := by
  intro S oR qf qs ℓ hqf hqs hlong hout
  rw [XS_eq_untag, h3 S oR]
  exact hc S oR qf qs ℓ hqf hqs hlong hout

theorem deferSimEufNB_of_parts (h3 : RomGameEuf) (hc : DeferCoreEuf) : DeferSimEufNB := by
  intro S oR qf qs ℓ hqf hqs hlong hout
  rw [XE_eq_untag, h3 S oR]
  exact hc S oR qf qs ℓ hqf hqs hlong hout

end Ideal.Direct.Rom

#print axioms Ideal.Direct.Rom.untag_PprfST
#print axioms Ideal.Direct.Rom.untag_PprfET
#print axioms Ideal.Direct.Rom.XS_eq_untag
#print axioms Ideal.Direct.Rom.deferSimSufNB_of_parts
#print axioms Ideal.Direct.Rom.deferSimEufNB_of_parts
