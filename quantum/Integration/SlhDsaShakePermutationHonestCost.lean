import Integration.SlhDsaShakePermutationHonestRaw

namespace Reduction.ShakePermutation.Honest
open SLHDSA SLHDSA.Security MLink OracleComp OracleSpec PQ.Interactive Quantum
open ShakeApi (Xof)
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
variable (S : Sha2Set) (N : ℕ) (base : Xof S)
local notation "P₀" => ShakeApi.primitives S base
local notation "ROM" => unifSpec + hashSpec (Primitives.core (ShakeApi.primitives S base))
private abbrev fee {α : Type} : ℕ ⊕ α → Prop := fun t => t.isRight = true

private theorem single {t : (ROM).Domain} : IsQueryBoundP (liftM ((ROM).query t) : OracleComp ROM _) fee 1 :=
  (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.zero_lt_one

def keyCharge (S : Sha2Set) := Lazy.keygenB S.vp 1 1
def signCharge (S : Sha2Set) := 1 + Lazy.signB S.vp 1 1
def verifyCharge (S : Sha2Set) := 1 + Resources2.verifyHashes S.vp

private theorem keyRoot (pk sk : S.Node) :
    IsQueryBoundP (GeneralScheme.keygenInternalWithSecretM (vp := S.vp) (P₀).core
      (oracleSecret (P₀).core (Equiv.refl _) pk sk) pk : OracleComp ROM S.Node) fee (keyCharge S) := by
  apply Lazy.qb_xmssNode fee (P₀).core 1 1 1 1
    (hash := PublicHash.f (P₀).core pk) (compress := PublicHash.tl (P₀).core pk)
    (nodeHash := PublicHash.h (P₀).core pk) (secret := oracleSecret (P₀).core (Equiv.refl _) pk sk)
  all_goals intros; exact single S base

private theorem signCore (sk : SecretKeyCore (P₀).core) (r : S.Node) (m : List SLHDSA.Byte) :
    IsQueryBoundP (GeneralScheme.signInternalWithSecretRandomizerM (P₀).core
      (oracleSecret (P₀).core (Equiv.refl _) sk.pkSeed sk.skSeed) m sk.pkSeed sk.pkRoot r :
        OracleComp ROM (GeneralScheme.SignatureCore S.vp (P₀).core)) fee (Lazy.signB S.vp 1 1) := by
  let sec := oracleSecret (m := OracleComp ROM) (P₀).core (Equiv.refl _) sk.pkSeed sk.skSeed
  have hf (a : Adrs) (z : S.Node) : IsQueryBoundP (PublicHash.f (P₀).core sk.pkSeed a z : OracleComp ROM _) fee 1 := single S base
  have ht (a : Adrs) (z : List S.Node) : IsQueryBoundP (PublicHash.tl (P₀).core sk.pkSeed a z : OracleComp ROM _) fee 1 := single S base
  have hh (a : Adrs) (x y : S.Node) : IsQueryBoundP (PublicHash.h (P₀).core sk.pkSeed a x y : OracleComp ROM _) fee 1 := single S base
  have hs (a) : IsQueryBoundP (sec a) fee 1 := single S base
  have hm : IsQueryBoundP (PublicHash.hmsg (P₀).core r sk.pkSeed sk.pkRoot m : OracleComp ROM _) fee 1 := single S base
  unfold GeneralScheme.signInternalWithSecretRandomizerM
  refine (Lazy.qb_bind fee hm fun digest =>
    Lazy.qb_bind fee (Lazy.qb_forsSign fee (P₀).core 1 1 1 hf hh hs _ _) fun forsSig =>
      Lazy.qb_bind fee (Lazy.qb_forsPk fee (P₀).core 1 1 1 hf ht hh forsSig _ _) fun forsPk =>
        Lazy.qb_bind fee (m := 0) (Lazy.qb_signFromPos fee (P₀).core 1 1 1 1 hf ht hh hs _ _ _ _ _)
          fun htSig => isQueryBoundP_pure _ _ _).mono ?_
  unfold Lazy.signB
  omega

private theorem verifyCore (pk : PublicKeyCore (P₀).core) (s : GeneralScheme.SignatureCore S.vp (P₀).core)
    (m : List SLHDSA.Byte) : IsQueryBoundP (GeneralScheme.verifyInternalM S.vp (P₀).core m s pk : OracleComp ROM Bool) fee
      (verifyCharge S) := by
  have hf (a : Adrs) (z : S.Node) : IsQueryBoundP (PublicHash.f (P₀).core pk.pkSeed a z : OracleComp ROM _) fee 1 := single S base
  have ht (a : Adrs) (z : List S.Node) : IsQueryBoundP (PublicHash.tl (P₀).core pk.pkSeed a z : OracleComp ROM _) fee 1 := single S base
  have hh (a : Adrs) (x y : S.Node) : IsQueryBoundP (PublicHash.h (P₀).core pk.pkSeed a x y : OracleComp ROM _) fee 1 := single S base
  have hm : IsQueryBoundP (PublicHash.hmsg (P₀).core s.randomness pk.pkSeed pk.pkRoot m : OracleComp ROM _) fee 1 := single S base
  unfold GeneralScheme.verifyInternalM GeneralHypertree.verifyM GeneralHypertree.pkFromSigM
    GeneralHypertree.recoverFromPositionM forsPkFromSigM
  refine (Lazy.qb_bind fee hm fun digest =>
    Lazy.qb_bind fee (Lazy.qb_forsPk fee (P₀).core 1 1 1 hf ht hh _ _ _) fun forsPk =>
      Lazy.qb_bind fee (m := 0)
        (Resources2.qb_recover fee (P₀).core 1 1 1 hf ht hh pk.pkSeed S.vp.params.d _ _ _ _)
        fun root => isQueryBoundP_pure _ _ _).mono ?_
  unfold verifyCharge Resources2.verifyHashes Lazy.xmssPkB
  simp only [Nat.mul_one]
  omega

variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
local notation "A" => pureBytesRomScheme S base (ShakeApi.signRand S rand base) seeds

theorem keygen_bound : IsQueryBoundP (A).keygen fee (keyCharge S) := by
  change IsQueryBoundP (_ <$> ((romScheme (vp := S.vp) (P₀).core (Equiv.refl _) (ShakeApi.signRand S rand base) seeds).keygen)) _ _
  rw [isQueryBoundP_map_iff,romScheme_keygen]
  refine (Lazy.qb_bind fee (isQueryBoundP_liftM_isRight seeds) fun pk =>
    Lazy.qb_bind fee (isQueryBoundP_liftM_isRight ($ᵗ S.Node : ProbComp S.Node)) fun sk =>
      Lazy.qb_bind fee (isQueryBoundP_liftM_isRight ($ᵗ S.Node : ProbComp S.Node)) fun prf =>
        Lazy.qb_bind fee (m := 0) (keyRoot S base pk sk) fun root => isQueryBoundP_pure _ _ _).mono ?_
  omega

theorem sign_bound (pk sk : List SLHDSA.Byte) (mc : ByteMessage) :
    IsQueryBoundP ((A).sign pk sk mc) fee (signCharge S) := by
  dsimp only [pureBytesRomScheme]
  split
  · split
    · refine (Lazy.qb_bind fee (isQueryBoundP_liftM_isRight _) fun r => ?_).mono (Nat.zero_add _).le
      unfold romSignPureBytes
      split
      · split
        · rw [isQueryBoundP_map_iff]
          unfold romSignAt
          exact Lazy.qb_bind fee (single S base) (fun R => signCore S base _ R _)
        · exact isQueryBoundP_pure _ _ _
      · exact isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_pure _ _ _

theorem verify_bound (pk : List SLHDSA.Byte) (mc : ByteMessage) (sig : ByteSig) :
    IsQueryBoundP ((A).verify pk mc sig) fee (verifyCharge S) := by
  dsimp only [pureBytesRomScheme]
  split
  · split
    · dsimp only [pureRomScheme,E2E.GuardedRom.scheme]
      split
      · exact verifyCore S base _ _ _
      · exact isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_pure _ _ _

end Reduction.ShakePermutation.Honest
#print axioms Reduction.ShakePermutation.Honest.keygen_bound
#print axioms Reduction.ShakePermutation.Honest.sign_bound
#print axioms Reduction.ShakePermutation.Honest.verify_bound
