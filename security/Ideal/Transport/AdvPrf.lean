import Ideal.Transport.AdvCommon
import Reduction.SufPrfV2

/-!
# Core-invariance (in `PRF` only) of the `PRF` distinguishers `bPrfC A`, `bPrfWC sufCheck A`

These distinguishers evaluate `prims.PRFmsg` themselves (the randomizer of every signature is
`prims.PRFmsg skPrf addrnd m`), so they are invariant only under a change of `PRF`:
the statements are for `setPrf prims prf prims.PRFmsg`.  `prims.PRF` is not used anywhere in
them (the secret values are obtained from the game's function oracle).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Transport

open Reduction

set_option linter.unusedSectionVars false

theorem bind_congr_k {m : Type → Type} [Monad m] {α β : Type} {x x' : m α} {f g : α → m β}
    (hx : x = x') (h : ∀ a, f a = g a) : x >>= f = x' >>= g := by
  subst hx
  exact bind_congr h

section Prf

variable {vp : ValidatedParams} (prims : Primitives vp.params)
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable (codec : CoreWireCodec vp.params prims.core)
  (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (optRand' : PublicKeyCore (setPrfC prims.core prf prims.PRFmsg) → ProbComp prims.Y)
  (hopt : ∀ pk, optRand' (trPk _ prf prims.PRFmsg pk) = optRand pk)
  (pkSeedDist : ProbComp prims.PkSeed)
  (S : List Byte → OracleComp (unifSpec + (List Byte →ₒ List Byte)) (List Byte × List Byte))

set_option quotPrecheck false in
/-- The typed forger over `prims` built from the byte-level main `S`. -/
local notation "Abase" =>
  (bytesToTyped (prims := prims) (codec := codec) (optRand := optRand) (pkSeedDist := pkSeedDist)
    ⟨S⟩)

set_option quotPrecheck false in
/-- The typed forger over `setPrf prims prf prims.PRFmsg` built from the same main `S`. -/
local notation "Aset" =>
  (bytesToTyped (prims := setPrf prims prf prims.PRFmsg)
    (codec := trCodec _ prf prims.PRFmsg codec)
    (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩)

include hopt in
/-- The signing procedure of `bPrf`. -/
theorem bSignC_tr (pk : PublicKeyCore prims.core) (skPrf : prims.SkPrf) (m : List Byte) :
    bSignC (prims := setPrf prims prf prims.PRFmsg) optRand' (trPk _ prf prims.PRFmsg pk) skPrf m =
      trSig _ prf prims.PRFmsg <$> bSignC (prims := prims) optRand pk skPrf m := by
  unfold bSignC
  rw [hopt, map_bind]
  refine bind_congr fun addrnd => ?_
  kexact signInternalWithSecretRandomizerM_tr (vp := vp) prims.core prf prims.PRFmsg
    (m := OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y))
    ⟨fun q => pure (PublicHash.impl prims q)⟩
    ⟨fun q => pure (PublicHash.impl (setPrf prims prf prims.PRFmsg) q)⟩
    (fun _ _ _ => by krfl) (fun _ _ _ _ => by krfl)
    (fun a => PRFScheme.functionQuery (pk.pkSeed, a)) m pk.pkSeed pk.pkRoot
    (prims.PRFmsg skPrf addrnd m)

include hopt in
/-- Everything `bPrf A` does after sampling `PK.seed`. -/
theorem bRestC_setPrf (pkSeed : prims.PkSeed) :
    bRestC (prims := setPrf prims prf prims.PRFmsg) Aset pkSeed = bRestC Abase pkSeed := by
  unfold bRestC
  refine bind_congr fun skPrf => ?_
  refine bind_congr_k (by krfl) fun root => ?_
  have h := runForger_bytesToTyped_tr prf prims.PRFmsg codec optRand optRand' pkSeedDist S
    ⟨pkSeed, root⟩ (bSignC optRand ⟨pkSeed, root⟩ skPrf) _
    (fun m => bSignC_tr prims prf optRand optRand' hopt ⟨pkSeed, root⟩ skPrf m)
  have hv := harnessValid_setPrf prims prf prims.PRFmsg ⟨pkSeed, root⟩
  simp only [trPk_mk] at h hv
  rw [h, bind_map_left]
  simp only [hv]

include hopt in
/-- The signing procedure of `bPrfW`. -/
theorem bSignW_tr (pk : PublicKeyCore prims.core) (skPrf : prims.SkPrf) (m : List Byte) :
    bSignW (prims := setPrf prims prf prims.PRFmsg) optRand' (trPk _ prf prims.PRFmsg pk) skPrf m =
      trSig _ prf prims.PRFmsg <$> bSignW (prims := prims) optRand pk skPrf m := by
  unfold bSignW
  rw [hopt, map_bind]
  refine bind_congr fun addrnd => ?_
  kexact signInternalWithSecretRandomizerM_tr (vp := vp) prims.core prf prims.PRFmsg
    (m := OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y))
    ⟨fun q => pure (PublicHash.impl prims q)⟩
    ⟨fun q => pure (PublicHash.impl (setPrf prims prf prims.PRFmsg) q)⟩
    (fun _ _ _ => by krfl) (fun _ _ _ _ => by krfl)
    (fun a => PRFScheme.functionQuery (pk.pkSeed, a)) m pk.pkSeed pk.pkRoot
    (prims.PRFmsg skPrf addrnd m)

include hopt in
/-- Everything `bPrfW sufCheck A` does after sampling `PK.seed`. -/
theorem bRestW_setPrf (pkSeed : prims.PkSeed) :
    bRestW (prims := setPrf prims prf prims.PRFmsg)
        (sufCheck (prims := setPrf prims prf prims.PRFmsg)) Aset pkSeed =
      bRestW sufCheck Abase pkSeed := by
  unfold bRestW
  refine bind_congr fun skPrf => ?_
  refine bind_congr_k (by krfl) fun root => ?_
  have h := runForgerSig_bytesToTyped_tr prf prims.PRFmsg codec optRand optRand' pkSeedDist S
    ⟨pkSeed, root⟩ (bSignW optRand ⟨pkSeed, root⟩ skPrf) _
    (fun m => bSignW_tr prims prf optRand optRand' hopt ⟨pkSeed, root⟩ skPrf m)
  have hv := sufCheck_setPrf prims prf prims.PRFmsg ⟨pkSeed, root⟩
  simp only [trPk_mk] at h hv
  rw [h, bind_map_left]
  simp only [hv]

include hopt in
/-- The EUF `PRF` distinguisher before the domain restriction. -/
theorem bPrf_setPrf : bPrf (prims := setPrf prims prf prims.PRFmsg) Aset = bPrf Abase := by
  rw [bPrf_eq_bRestC, bPrf_eq_bRestC]
  exact bind_congr fun pkSeed =>
    bRestC_setPrf prims prf codec optRand optRand' hopt pkSeedDist S pkSeed

include hopt in
/-- The SUF `PRF` distinguisher before the domain restriction. -/
theorem bPrfW_setPrf :
    bPrfW (prims := setPrf prims prf prims.PRFmsg)
        (sufCheck (prims := setPrf prims prf prims.PRFmsg)) Aset =
      bPrfW sufCheck Abase := by
  rw [bPrfW_eq_bRestW, bPrfW_eq_bRestW]
  exact bind_congr fun pkSeed =>
    bRestW_setPrf prims prf codec optRand optRand' hopt pkSeedDist S pkSeed

include hopt in
/-- **The EUF `PRF` distinguisher over `setPrf prims prf prims.PRFmsg` is the one over `prims`.** -/
theorem bPrfC_setPrf : bPrfC (prims := setPrf prims prf prims.PRFmsg) Aset = bPrfC Abase := by
  unfold bPrfC
  rw [bPrf_setPrf prims prf codec optRand optRand' hopt pkSeedDist S]
  rfl

include hopt in
/-- **The SUF `PRF` distinguisher over `setPrf prims prf prims.PRFmsg` is the one over `prims`.** -/
theorem bPrfWC_setPrf :
    bPrfWC (prims := setPrf prims prf prims.PRFmsg)
        (sufCheck (prims := setPrf prims prf prims.PRFmsg)) Aset =
      bPrfWC sufCheck Abase := by
  unfold bPrfWC
  rw [bPrfW_setPrf prims prf codec optRand optRand' hopt pkSeedDist S]
  rfl

include hopt in
/-- The SUF distinguisher at the strong forger wrapper. -/
theorem bPrfWC_setPrf_S :
    bPrfWC (prims := setPrf prims prf prims.PRFmsg)
        (sufCheck (prims := setPrf prims prf prims.PRFmsg))
        (bytesToTypedS (prims := setPrf prims prf prims.PRFmsg)
          (codec := trCodec _ prf prims.PRFmsg codec) (optRand := optRand')
          (pkSeedDist := pkSeedDist) ⟨S⟩).toUnforgeableAdversary =
      bPrfWC sufCheck (bytesToTypedS (prims := prims) (codec := codec) (optRand := optRand)
        (pkSeedDist := pkSeedDist) ⟨S⟩).toUnforgeableAdversary :=
  bPrfWC_setPrf prims prf codec optRand optRand' hopt pkSeedDist S

include hopt in
/-- Real experiment of the EUF distinguisher against any `PRF` candidate `P` on the secret-key
address domain (in particular `skPrfC vp (setPrf prims prf prims.PRFmsg)`, whose `eval` is
`prf`). -/
theorem bPrfC_real_setPrf {K : Type} (P : PRFScheme K (prims.PkSeed × SkAdrs vp) prims.Y) :
    P.prfRealExperiment (bPrfC (prims := setPrf prims prf prims.PRFmsg) Aset) =
      P.prfRealExperiment (bPrfC Abase) :=
  congrArg P.prfRealExperiment
    (bPrfC_setPrf prims prf codec optRand optRand' hopt pkSeedDist S)

include hopt in
/-- Ideal experiment of the EUF distinguisher. -/
theorem bPrfC_ideal_setPrf :
    PRFScheme.prfIdealExperiment (bPrfC (prims := setPrf prims prf prims.PRFmsg) Aset) =
      PRFScheme.prfIdealExperiment (bPrfC Abase) :=
  congrArg PRFScheme.prfIdealExperiment
    (bPrfC_setPrf prims prf codec optRand optRand' hopt pkSeedDist S)

include hopt in
/-- Real experiment of the SUF distinguisher against any `PRF` candidate `P`. -/
theorem bPrfWC_real_setPrf {K : Type} (P : PRFScheme K (prims.PkSeed × SkAdrs vp) prims.Y) :
    P.prfRealExperiment (bPrfWC (prims := setPrf prims prf prims.PRFmsg)
        (sufCheck (prims := setPrf prims prf prims.PRFmsg)) Aset) =
      P.prfRealExperiment (bPrfWC sufCheck Abase) :=
  congrArg P.prfRealExperiment
    (bPrfWC_setPrf prims prf codec optRand optRand' hopt pkSeedDist S)

include hopt in
/-- Ideal experiment of the SUF distinguisher. -/
theorem bPrfWC_ideal_setPrf :
    PRFScheme.prfIdealExperiment (bPrfWC (prims := setPrf prims prf prims.PRFmsg)
        (sufCheck (prims := setPrf prims prf prims.PRFmsg)) Aset) =
      PRFScheme.prfIdealExperiment (bPrfWC sufCheck Abase) :=
  congrArg PRFScheme.prfIdealExperiment
    (bPrfWC_setPrf prims prf codec optRand optRand' hopt pkSeedDist S)

end Prf

end Ideal.Transport

section AxiomCheck
open Ideal.Transport
#print axioms bSignC_tr
#print axioms bRestC_setPrf
#print axioms bRestW_setPrf
#print axioms bPrf_setPrf
#print axioms bPrfW_setPrf
#print axioms bPrfC_setPrf
#print axioms bPrfWC_setPrf
#print axioms bPrfWC_setPrf_S
#print axioms bPrfC_real_setPrf
#print axioms bPrfC_ideal_setPrf
#print axioms bPrfWC_real_setPrf
#print axioms bPrfWC_ideal_setPrf
end AxiomCheck
