import Ideal.Realize.Port
import Ideal.Transport.AdvMsg
import Ideal.Transport.AdvPrf
import Ideal.ComposeFinal

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize.Msg
open Reduction Ideal.Transport

theorem primsG_eq (g : CF St Blk) :
    primsG (liftC g) = setPrf (R₀ (thG g) (hmG g)) (prfG g) (pmG g) := rfl

def codec₀ : CoreWireCodec Link.vp.params core₀ where
  pkSeed := WireCodec.bytes Link.vp.params.n
  skSeed := WireCodec.bytes Link.vp.params.n
  skPrf := WireCodec.bytes Link.vp.params.n
  y := WireCodec.bytes Link.vp.params.n
  y_toBytes := fun _ => rfl

def optRand₀ (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (pk : PublicKeyCore core₀) :
    ProbComp core₀.Y := oR pk.pkSeed pk.pkRoot

noncomputable def B₀ (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    Forger Link.vp (R₀ (thG g) (hmG g)) (optRand₀ oR) pkSeedDist :=
  (bytesToTypedS (vp := Link.vp) (prims := R₀ (thG g) (hmG g)) (codec := codec₀)
    (optRand := optRand₀ oR) (pkSeedDist := pkSeedDist)
    ⟨fun pk => simulateQ (instImpl g) (S.main pk)⟩).toUnforgeableAdversary

theorem step1 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    Lazy.bPrfMsgWL sufCheck (S.typedS (optRandU oR) pkSeedDist g) =
      Lazy.bPrfMsgWL sufCheck (B₀ S oR pkSeedDist g) :=
  bPrfMsgWL_setPrf_S (R₀ (thG g) (hmG g)) (prfG g) (pmG g) codec₀ (optRand₀ oR)
    (optRandU oR g) (fun _ => rfl) pkSeedDist (fun pk => simulateQ (instImpl g) (S.main pk))

theorem step1E (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    Lazy.bPrfMsgL (S.typedE (optRandU oR) pkSeedDist g) =
      Lazy.bPrfMsgL (B₀ S oR pkSeedDist g) :=
  bPrfMsgL_setPrf (R₀ (thG g) (hmG g)) (prfG g) (pmG g) codec₀ (optRand₀ oR)
    (optRandU oR g) (fun _ => rfl) pkSeedDist (fun pk => simulateQ (instImpl g) (S.main pk))

end Ideal.Realize.Msg
#print axioms Ideal.Realize.Msg.step1
#print axioms Ideal.Realize.Msg.step1E
example : (1:Nat) = 2 := rfl
