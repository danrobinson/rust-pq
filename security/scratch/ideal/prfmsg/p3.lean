import Ideal.Realize.MsgPort
import Ideal.Transport.AdvMsg
import Ideal.ComposeFinal

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize.Msg
open Reduction Reduction.Lazy Reduction.Open Ideal.Transport

def codec₀ : CoreWireCodec Link.vp.params core₀ where
  pkSeed := WireCodec.bytes Link.vp.params.n
  skSeed := WireCodec.bytes Link.vp.params.n
  skPrf := WireCodec.bytes Link.vp.params.n
  y := WireCodec.bytes Link.vp.params.n
  y_toBytes := fun _ => rfl

def optRand₀ (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (pk : PublicKeyCore core₀) :
    ProbComp core₀.Y := oR pk.pkSeed pk.pkRoot

abbrev Rd : Primitives Link.vp.params := R₀ dT dH

/-- The byte-level port forger, typed over `core₀`. -/
noncomputable def mainC (S : ForgerI) : PortForgerProg Link.vp Rd :=
  typedC codec₀ default S.main

noncomputable def P₀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) : OracleComp (OP Rd) Bool :=
  msgOpenWVP (prims := Rd) (optRand₀ oR) pkSeedDist sufCheckO (mainC S)

noncomputable def Amsg (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) : MsgPrfAdvI :=
  simulateQ (interpC (G := msgG Rd) hashC) (lazyRes (P₀ S oR pkSeedDist))

theorem eq_msg (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    Lazy.bPrfMsgWL sufCheck (S.typedS (optRandU oR) pkSeedDist g) = (Amsg S oR pkSeedDist).inst g := by
  have h1 := bPrfMsgWL_setPrf_S (R₀ (thG g) (hmG g)) (prfG g) (pmG g) codec₀ (optRand₀ oR)
    (optRandU oR g) (fun _ => rfl) pkSeedDist (fun pk => simulateQ (instImpl g) (S.main pk))
  refine h1.trans ?_
  have h2 := (lazyRun_msgOpenWV_sufCheck (prims := R₀ (thG g) (hmG g))
    (bytesToTypedS (vp := Link.vp) (prims := R₀ (thG g) (hmG g)) (codec := codec₀)
      (optRand := optRand₀ oR) (pkSeedDist := pkSeedDist)
      ⟨fun pk => simulateQ (instImpl g) (S.main pk)⟩).toUnforgeableAdversary).symm
  refine h2.trans ?_
  have h3 := bytesToTypedS_inst (prims := R₀ (thG g) (hmG g)) (optRand := optRand₀ oR)
    (pkSeedDist := pkSeedDist) codec₀ g S.main
  rw [h3]
  have h4 := msgOpenWVP_fusion (prims := R₀ (thG g) (hmG g)) (optRand₀ oR) pkSeedDist g sufCheckO
    (typedC codec₀ default S.main)
  rw [← h4]
  have h5 := msgOpenWVP_withTH (prims := Rd) (optRand₀ oR) pkSeedDist (thG g) (hmG g) (mainC S)
  have h5' : msgOpenWVP (prims := R₀ (thG g) (hmG g)) (optRand₀ oR) pkSeedDist sufCheckO
      (typedC codec₀ default S.main) = P₀ S oR pkSeedDist := h5
  rw [h5']
  have h6 := lazyRun_portR (G := msgG Rd) g (PublicHash.impl (R₀ (thG g) (hmG g))) hashC
    (fun q => by rw [impl_R₀]; exact hashC_inst g q) (P₀ S oR pkSeedDist)
  exact h6
end Ideal.Realize.Msg
#print axioms Ideal.Realize.Msg.eq_msg
