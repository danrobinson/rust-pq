import Ideal.Realize.PrfPort
import Ideal.Realize.MsgReal

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize.Prf
open Reduction Reduction.Open Ideal.Transport
open Ideal.Realize.Msg (codec₀ optRand₀ Rd mainC cEmb instImpl_cEmb instImpl_liftM typedC
  bytesToTypedS_inst bytesToTyped_inst)

abbrev Dsk : Type := Bytes 16 × SkAd

/-- The hash interface (with `PRF_msg`) answered at the table `g`. -/
def hImpl (g : CF St Blk) : QueryImpl (HSpec Rd) Id
  | .inl q => implTH (thG g) (hmG g) q
  | .inr t => pmG g t.1 t.2.1 t.2.2

/-- The closing handler at the table `g`, over the reference interface. -/
def closeR (g : CF St Blk) : QueryImpl (PSpec Rd Dsk) (OracleComp (unifSpec + (Dsk →ₒ Bytes 16)))
  | .inl n => (liftM (liftM (unifSpec.query n) : ProbComp _) :
      OracleComp (unifSpec + (Dsk →ₒ Bytes 16)) _)
  | .inr (.inl d) => (PRFScheme.functionQuery d : OracleComp (PRFScheme.PRFOracleSpec Dsk (Bytes 16)) _)
  | .inr (.inr q) => pure (hImpl g q)

theorem close_castP' (g : CF St Blk) {α : Type} (X : OracleComp (PSpec Rd Dsk) α) :
    simulateQ (closeImpl (primsG (liftC g)) (Bytes 16 × SkAd))
        (castP' (R₀ (thG g) (hmG g)) (prfG g) (pmG g) Dsk X) =
      simulateQ (closeR g) X := by krfl

/-- The hash interface with `PRF_msg`, as compression programs. -/
def hashPC : QueryImpl (HSpec Rd) (OracleComp CSpec)
  | .inl q => hashC q
  | .inr t => prfMsgC t.1 t.2.1 t.2.2

theorem hashPC_inst (g : CF St Blk) (q : (HSpec Rd).Domain) :
    simulateQ (instImpl₀ g) (hashPC q) = pure (f := ProbComp) (α := (HSpec Rd).Range q) (hImpl g q) := by
  rcases q with q | t
  · exact hashC_inst g q
  · exact prfMsgC_inst g t.1 t.2.1 t.2.2

/-- Interpretation of the port program: port and game queries forwarded, hash and `PRF_msg`
queries issued as compression chains. -/
def chainP : QueryImpl (QSpec Rd Dsk) (OracleComp (unifSpec + (hS St Blk + (Dsk →ₒ Bytes 16))))
  | .inl n => (liftM ((unifSpec + (hS St Blk + (Dsk →ₒ Bytes 16))).query (.inl n)) :
      OracleComp (unifSpec + (hS St Blk + (Dsk →ₒ Bytes 16))) _)
  | .inr (.inl t) => (liftM ((unifSpec + (hS St Blk + (Dsk →ₒ Bytes 16))).query (.inr t)) :
      OracleComp (unifSpec + (hS St Blk + (Dsk →ₒ Bytes 16))) _)
  | .inr (.inr q) => simulateQ (cEmb (X := Dsk →ₒ Bytes 16)) (hashPC q)

theorem close_portP (T : Bytes 16 → Bytes 22 → List (Bytes 16) → Bytes 16)
    (H : Bytes 16 → Bytes 16 → Bytes 16 → List Byte → Bytes 30) (g : CF St Blk) {α : Type}
    (X : OracleComp (QSpec (R₀ T H) Dsk) α) :
    simulateQ (closeR g) (simulateQ (portP (prims := R₀ T H) (D := Dsk) g) X) =
      simulateQ (instImpl g) (simulateQ chainP X) := by
  refine Ideal.Realize.simulateQ_comm_of_step _ _ _ _ (fun t => ?_) X
  rcases t with n | (q | d) | q
  · simp only [portP, chainP]
    rw [simulateQ_spec_query, simulateQ_spec_query]
    rfl
  · simp only [portP, chainP, simulateQ_pure]
    rw [simulateQ_spec_query]
    rfl
  · simp only [portP, chainP]
    rw [simulateQ_spec_query]
    erw [simulateQ_spec_query]
    rfl
  · simp only [portP, chainP]
    rw [simulateQ_spec_query, instImpl_cEmb, hashPC_inst, liftM_pure]
    rfl

noncomputable def PprfS (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) : OracleComp (QSpec Rd Dsk) Bool :=
  bPrfWCOpenP (prims := Rd) (optRand₀ oR) pkSeedDist sufCheckOpen (mainC S)

noncomputable def AprfS (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) : PrfAdvI St Blk (Bytes 16) SkAd (Bytes 16) :=
  simulateQ chainP (PprfS S oR pkSeedDist)

theorem bPrfWC_eq_inst (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    bPrfWC sufCheck (S.typedS (optRandU oR) pkSeedDist g) = (AprfS S oR pkSeedDist).inst g := by
  have h1 := (bPrfWCOpen_close_suf (prims := primsG (liftC g))
    (S.typedS (optRandU oR) pkSeedDist g)).symm
  refine h1.trans ?_
  have h2 := bPrfWCOpen_setPrf (R₀ (thG g) (hmG g)) (prfG g) (pmG g) (optRand₀ oR) (optRandU oR g)
    (fun _ => rfl) codec₀ pkSeedDist (fun pk => simulateQ (instImpl g) (S.main pk))
  have h2'' := congrArg (fun x => simulateQ (closeImpl (primsG (liftC g)) Dsk)
    (castP' (R₀ (thG g) (hmG g)) (prfG g) (pmG g) Dsk x)) h2
  refine (?_ : _ = _).trans (h2''.trans ?_)
  · show _ = _
    krfl
  refine (close_castP' g _).trans ?_
  have h3 := bytesToTypedS_inst (prims := R₀ (thG g) (hmG g)) (optRand := optRand₀ oR)
    (pkSeedDist := pkSeedDist) codec₀ g S.main
  rw [h3]
  have h4 := bPrfWCOpenP_fusion (prims := R₀ (thG g) (hmG g)) (optRand₀ oR) pkSeedDist g
    sufCheckOpen (typedC codec₀ default S.main)
  rw [← h4]
  have h5 : bPrfWCOpenP (prims := R₀ (thG g) (hmG g)) (optRand₀ oR) pkSeedDist sufCheckOpen
      (typedC codec₀ default S.main) = PprfS S oR pkSeedDist :=
    bPrfWCOpenP_withTH (prims := Rd) (thG g) (hmG g) (mainC S)
  rw [h5]
  exact close_portP (thG g) (hmG g) g _

end Ideal.Realize.Prf
#print axioms Ideal.Realize.Prf.close_castP'
#print axioms Ideal.Realize.Prf.bPrfWC_eq_inst
