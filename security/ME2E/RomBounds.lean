import ME2E.PureRom
import HashSig.SLHDSA.Security.RangeBound

namespace ME2E

open MLink SLHDSA SLHDSA.Security SignatureAlg OracleComp OracleSpec ENNReal

/-- Uniform three-oracle bound at all six SHA-2 sets, for up to 2^64 signatures. -/
theorem pure_bytes_rom_range (S : Sha2Set)
    (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed)
    (F : StrongUnforgeableAdversary (pureBytesRomScheme S optRand pkSeedDist))
    {qh qs : ℕ} (hF : F.RomQueryBound qh qs) (hlo : 2^32 ≤ qh)
    (hhi : qh ≤ 2^64) (hs : qs ≤ 2^64) :
    strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec S.prims.core)) F ≤
      (qh : ℝ≥0∞) / 2 ^ (8 * S.vp.params.n - 2) := by
  apply (pure_bytes_security_sha2 S optRand pkSeedDist F hF).trans
  apply securityBound_le_div_pow_of_coefficient _ (by positivity) (by decide) hlo hhi hs
  cases S <;> decide +kernel

/-- The same budget range for existential forgery at the pure byte interface. -/
theorem pure_bytes_rom_range_euf (S : Sha2Set)
    (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed)
    (A : UnforgeableAdversary (pureBytesRomScheme S optRand pkSeedDist))
    {qh qs : ℕ} (hA : A.RomQueryBound qh qs) (hlo : 2^32 ≤ qh)
    (hhi : qh ≤ 2^64) (hs : qs ≤ 2^64) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec S.prims.core)) A ≤
      (qh : ℝ≥0∞) / 2 ^ (8 * S.vp.params.n - 2) :=
  (unforgeableAdvantage_le_strongUnforgeableAdvantage _ A).trans
    (pure_bytes_rom_range S optRand pkSeedDist ⟨A.main⟩ hA hlo hhi hs)

end ME2E

#print axioms ME2E.pure_bytes_rom_range
#print axioms ME2E.pure_bytes_rom_range_euf
