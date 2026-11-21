import Reduction.Linear
import Reduction.Bytes

/-!
# Byte-level linear headlines (package W7)

The linear (signed-pair) headline theorems of `Reduction/Linear.lean` for the byte-level schemes
`bytesAlg` / `pureBytesAlg` of `Reduction/Bytes.lean`.  The transfer only changes the left
`Adv` (`Adv_bytes(S) ≤ Adv_typed(bytesToTypedS S)` etc.), so both sides of the linear bound are
those of the typed theorem at the typed forger built from the byte-level one.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

open TweakableHash

set_option linter.unusedSectionVars false

section

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {codec : CoreWireCodec vp.params prims.core}
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-- **SUF-CMA of SLH-DSA on byte strings (internal algorithms), linear form.** -/
theorem slhdsa_bytes_suf_cma_linear (hS : Structural vp prims)
    (S : BytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S +
        linIdealSuf (bytesToTypedS S).toUnforgeableAdversary ≤
      linRealSuf (bytesToTypedS S).toUnforgeableAdversary :=
  (add_le_add_left (bytes_strong_advantage_le S) _).trans
    (slhdsa_suf_cma_final_linear hS (bytesToTypedS S))

/-- **EUF-CMA of SLH-DSA on byte strings (internal algorithms), linear form.** -/
theorem slhdsa_bytes_euf_cma_linear (hS : Structural vp prims)
    (A : BytesForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A +
        linIdealEuf (bytesToTyped A) ≤ linRealEuf (bytesToTyped A) :=
  (add_le_add_left (bytes_advantage_le A) _).trans
    (slhdsa_euf_cma_final_linear hS (bytesToTyped A))

/-- **SUF-CMA of the external pure interface on byte strings, linear form.** -/
theorem slhdsa_pure_bytes_suf_cma_linear (hS : Structural vp prims)
    (S : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S +
        linIdealSuf (toInternal (pureBytesToTyped S.toUnforgeableAdversary)) ≤
      linRealSuf (toInternal (pureBytesToTyped S.toUnforgeableAdversary)) :=
  (add_le_add_left (pure_bytes_strong_advantage_le S) _).trans
    (slhdsa_pure_suf_cma_final_linear hS (pureBytesToTypedS S))

/-- **EUF-CMA of the external pure interface on byte strings, linear form.** -/
theorem slhdsa_pure_bytes_euf_cma_linear (hS : Structural vp prims)
    (A : PureBytesForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A +
        linIdealEuf (toInternal (pureBytesToTyped A)) ≤
      linRealEuf (toInternal (pureBytesToTyped A)) :=
  (add_le_add_left (pure_bytes_advantage_le A) _).trans
    (slhdsa_pure_euf_cma_final_linear hS (pureBytesToTyped A))

/-- The byte-level absolute-value bounds (final adversaries, tight caps) follow from the linear
ones. -/
theorem slhdsa_bytes_suf_cma_memo_of_linear (hS : Structural vp prims)
    (S : BytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo (bytesToTypedS S).toUnforgeableAdversary :=
  boundFinalTight_of_linear _ _ _ _ _ _ _ _ _ _ _ _ (slhdsa_bytes_suf_cma_linear hS S)

theorem slhdsa_bytes_euf_cma_memo_of_linear (hS : Structural vp prims)
    (A : BytesForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo (bytesToTyped A) :=
  boundFinalTight_of_linear _ _ _ _ _ _ _ _ _ _ _ _ (slhdsa_bytes_euf_cma_linear hS A)

theorem slhdsa_pure_bytes_suf_cma_memo_of_linear (hS : Structural vp prims)
    (S : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo (toInternal (pureBytesToTyped S.toUnforgeableAdversary)) :=
  boundFinalTight_of_linear _ _ _ _ _ _ _ _ _ _ _ _ (slhdsa_pure_bytes_suf_cma_linear hS S)

theorem slhdsa_pure_bytes_euf_cma_memo_of_linear (hS : Structural vp prims)
    (A : PureBytesForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo (toInternal (pureBytesToTyped A)) :=
  boundFinalTight_of_linear _ _ _ _ _ _ _ _ _ _ _ _ (slhdsa_pure_bytes_euf_cma_linear hS A)

end

/-! ## SLH-DSA-SHA2-128s -/

theorem slhdsa_bytes_suf_cma_linear_128s
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (S : BytesStrongForger Link.vp Link.prims codec128s optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S +
        linIdealSuf (bytesToTypedS S).toUnforgeableAdversary ≤
      linRealSuf (bytesToTypedS S).toUnforgeableAdversary :=
  slhdsa_bytes_suf_cma_linear structural_128s S

theorem slhdsa_bytes_euf_cma_linear_128s
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : BytesForger Link.vp Link.prims codec128s optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A +
        linIdealEuf (bytesToTyped A) ≤ linRealEuf (bytesToTyped A) :=
  slhdsa_bytes_euf_cma_linear structural_128s A

theorem slhdsa_pure_bytes_suf_cma_linear_128s
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (S : PureBytesStrongForger Link.vp Link.prims codec128s optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S +
        linIdealSuf (toInternal (pureBytesToTyped S.toUnforgeableAdversary)) ≤
      linRealSuf (toInternal (pureBytesToTyped S.toUnforgeableAdversary)) :=
  slhdsa_pure_bytes_suf_cma_linear structural_128s S

theorem slhdsa_pure_bytes_euf_cma_linear_128s
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : PureBytesForger Link.vp Link.prims codec128s optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A +
        linIdealEuf (toInternal (pureBytesToTyped A)) ≤
      linRealEuf (toInternal (pureBytesToTyped A)) :=
  slhdsa_pure_bytes_euf_cma_linear structural_128s A

#print axioms slhdsa_bytes_suf_cma_linear
#print axioms slhdsa_bytes_euf_cma_linear
#print axioms slhdsa_pure_bytes_suf_cma_linear
#print axioms slhdsa_pure_bytes_euf_cma_linear
#print axioms slhdsa_bytes_suf_cma_memo_of_linear
#print axioms slhdsa_bytes_euf_cma_memo_of_linear
#print axioms slhdsa_pure_bytes_suf_cma_memo_of_linear
#print axioms slhdsa_pure_bytes_euf_cma_memo_of_linear
#print axioms slhdsa_bytes_suf_cma_linear_128s
#print axioms slhdsa_bytes_euf_cma_linear_128s
#print axioms slhdsa_pure_bytes_suf_cma_linear_128s
#print axioms slhdsa_pure_bytes_euf_cma_linear_128s

end Reduction
