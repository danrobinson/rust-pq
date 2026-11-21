import Ideal.Realize.PrfReal
open OracleComp OracleSpec SLHDSA SLHDSA.Security
open Ideal Ideal.Realize

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

noncomputable example (R : SufRealizers S (optRandU oR) pkSeedDist) :
    SufRealizers S (optRandU oR) pkSeedDist :=
  { R with q := Prf.qPrf qf qs ℓ, qO := Prf.qOPrf qs, qm := Msg.qMsg qf qs ℓ, qOm := qs, mlen := ℓ,
           prf := Prf.realizesPrfSuf S oR pkSeedDist hqf hqs hlong hout,
           msg := Msg.realizesMsgSuf S oR pkSeedDist hqf hqs hlong hout }

noncomputable example (R : EufRealizers S (optRandU oR) pkSeedDist) :
    EufRealizers S (optRandU oR) pkSeedDist :=
  { R with q := Prf.qPrf qf qs ℓ, qO := Prf.qOPrf qs, qm := Msg.qMsg qf qs ℓ, qOm := qs, mlen := ℓ,
           prf := Prf.realizesPrfEuf S oR pkSeedDist hqf hqs hlong hout,
           msg := Msg.realizesMsgEuf S oR pkSeedDist hqf hqs hlong hout }
