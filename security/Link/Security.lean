import Link.Basic
import HashSigTest.SLHDSA.CoverageBound
import HashSig.SLHDSA.Security.RomConformance
import HashSig.SLHDSA.AddressDiscipline
import HashSig.SLHDSA.Security.NodeGraph
import HashSig.SLHDSA.Security.ReachableTargets
import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.QueryBound
import HashSig.SLHDSA.Security.KeyDiscipline
import HashSig.SLHDSA.Security.SecretTraces
import HashSig.SLHDSA.Security.WeakKeyBound

/-!
# The security theorem for SLH-DSA-SHA2-128s, and its link to the executable verifier

* `security_128s`, `security_128s_euf`: VCVio's SUF-CMA / EUF-CMA bound, specialised to
  SLH-DSA-SHA2-128s.  The scheme bounded is `romScheme prims.core e optRand pkSeedDist`, in which the
  tweakable hash (`F`, `H`, `T_l`, and `PRF` as `F` at a PRF address), `H_msg` and `PRF_msg` are
  three independent random oracles.  SHA-256 is not modelled.
* `romScheme_verify_eq`, `verifyInternalM_impl_eq`: verification of that scheme, with its oracle
  queries answered by the SHA-2 functions of `prims`, is the executable
  `GeneralScheme.verifyInternal vp prims`.
* `hprf_dom`, `not_hprf`: the hypothesis `hprf` of the library bridge `romScheme_map_romAnswer`
  holds for `prims` on the checked `ADRSc` domain `Dom`, and is false without that restriction.
* `romScheme_map_romAnswer_128s`: nevertheless the whole scheme (key generation, signing,
  verification), with its oracles answered by the SHA-2 functions, is FIPS 205's internal
  algorithms at `prims`, because honest key generation and signing read secrets only at in-domain
  addresses.
-/

namespace Link
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg
open scoped ENNReal

/-- **SUF-CMA security of SLH-DSA-SHA2-128s in the three-oracle model.**  Any adversary against
`romScheme prims.core e optRand pkSeedDist` making at most `qh` hash queries and `qs` signing
queries outputs a valid (message, signature) pair that the signing oracle never returned with
probability at most `securityBound vp.params (256 ^ 16) 2 1 qh qs`, for every reading `e` of
`SK.seed` as a node, every `opt_rand` source (hedged or deterministic) and every distribution of
`PK.seed`.

What this does *not* say: the scheme is the one over `unifSpec + hashSpec prims.core`, where the
tweakable hash, `H_msg` and `PRF_msg` are three independent lazily-sampled random oracles
(`ProbCompRuntime.rom`).  Only the *types* and the address encoding `sha2AdrsKey` of `prims` enter;
SHA-256, HMAC and MGF1 do not occur, and nothing is claimed about them.  It is a statement about the
internal algorithms (FIPS 205 Algorithms 18-20) on an internal message `M'`. -/
theorem security_128s (e : prims.SkSeed ≃ prims.Y)
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed)
    (adv : StrongUnforgeableAdversary (romScheme (vp := vp) prims.core e optRand pkSeedDist))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec prims.core)) adv ≤
      securityBound vp.params (256 ^ 16) 2 1 qh qs :=
  SLHDSA.CoverageBoundTest.strongUnforgeableAdvantage_sha2_le vp (fipsApprovedAddressBounds S128)
    e optRand pkSeedDist adv hadv

/-- **EUF-CMA security of SLH-DSA-SHA2-128s in the three-oracle model**: the same bound for a
forgery on a message never signed.  Same model and same caveats as `security_128s`. -/
theorem security_128s_euf (e : prims.SkSeed ≃ prims.Y)
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed)
    (adv : UnforgeableAdversary (romScheme (vp := vp) prims.core e optRand pkSeedDist))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec prims.core)) adv ≤
      securityBound vp.params (256 ^ 16) 2 1 qh qs :=
  (unforgeableAdvantage_le_strongUnforgeableAdvantage _ adv).trans
    (security_128s e optRand pkSeedDist ⟨adv.main⟩ hadv)

/-- The executable verifier is, by definition, the verification program of the proof's scheme with
its public-hash queries (`F`, `H`, `T_l`, `H_msg`) answered by the SHA-2 functions of `prims`.
This only names the definition; it says nothing about SHA-2 behaving like a random oracle. -/
theorem verifyInternalM_impl_eq (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    simulateQ (PublicHash.impl prims) (GeneralScheme.verifyInternalM vp prims.core msg sig pk) =
      GeneralScheme.verifyInternal vp prims msg sig pk := rfl

/-- **The verifier of the security theorem is the executable verifier.**  Run the `verify` of the
scheme bounded in `security_128s` with its three oracles answered by `romAnswer prims` (the SHA-2
tweakable hash, `H_msg` and `PRF_msg` of the bundle; the uniform-sampling oracle left alone): the
result is the deterministic value `GeneralScheme.verifyInternal vp prims msg sig pk`, for every
public key, message and signature, honest or not.

This is an identity of programs.  It does not transfer the probability bound from random oracles to
SHA-2; that step is the (unproven, heuristic) random-oracle methodology. -/
theorem romScheme_verify_eq (e : prims.SkSeed ≃ prims.Y)
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    simulateQ (unifFwdAnswerImpl (romAnswer prims))
        ((romScheme (vp := vp) prims.core e optRand pkSeedDist).verify pk msg sig) =
      (pure (GeneralScheme.verifyInternal vp prims msg sig pk) : ProbComp Bool) := by
  let _ : HasQuery (publicHashSpec prims.core) ProbComp :=
    ⟨fun q => liftM (PublicHash.impl prims q)⟩
  let F : HasQuery.QueryHom (publicHashSpec prims.core)
      (OracleComp (unifSpec + hashSpec prims.core)) ProbComp :=
    { toMonadHom := simulateQ' (unifFwdAnswerImpl (romAnswer prims))
      map_query' := fun q => by
        simp [unifFwdAnswerImpl, romAnswer] }
  have hFree : ∀ {α : Type} (oa : OracleComp (publicHashSpec prims.core) α),
      (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core)
        (m := ProbComp)).toMonadHom oa = pure (simulateQ (PublicHash.impl prims) oa) := by
    intro α oa
    have hImpl : HasQuery.toQueryImpl (spec := publicHashSpec prims.core) (m := ProbComp) =
        (PublicHash.impl prims).liftTarget ProbComp := by
      funext q
      rfl
    rw [HasQuery.QueryHom.ofSimulateQ_apply, hImpl, simulateQ_liftTarget]
    rfl
  change F.toMonadHom (GeneralScheme.verifyInternalM vp prims.core msg sig pk) = _
  rw [GeneralScheme.verifyInternalM_natural vp prims.core F,
    ← GeneralScheme.verifyInternalM_natural vp prims.core
      (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := ProbComp)),
    hFree]
  rfl

/-- **`hprf` on the checked domain.**  For every address in the checked `ADRSc` domain (secret-key
type or not), the bundle's tweakable hash at that address applied to the one-element list
`[SK.seed]` is the bundle's `PRF`: both are `Trunc_16(SHA-256(PK.seed ‖ 0^48 ‖ ADRSc ‖ SK.seed))`.
This is the hypothesis `hprf` of `romScheme_map_romAnswer` (at `e := Equiv.refl _`) restricted to
`Dom`.  Outside `Dom` it fails: see `not_hprf`. -/
theorem hprf_dom (pkSeed skSeed : Node) (a : SLHDSA.Adrs) (h : Dom a) :
    prims.Thash pkSeed (prims.adrsToKey a) [skSeed] = prims.PRF pkSeed skSeed a := by
  obtain ⟨hc, hl, ht⟩ := h
  show sha2Thash vp.params pkSeed (sha2AdrsKey a) [skSeed] =
    checkedNodeOrZero (sha2PRFChecked pkSeed skSeed a)
  simp [sha2Thash, sha2PRFChecked, Sha2Address.ofAdrs, hc, hl, ht, sha2AdrsKey_eq_compressed,
    byteArrayPrefixOrZero, checkedNodeOrZero, sha2Prefix256, Sha2Address.bytes, concatBytes]
  rfl

/-- A secret-key address outside the checked domain: layer `256` does not fit one byte. -/
def badAdrs : SLHDSA.Adrs := ⟨256, 0, 5, 0, 0, 0⟩

/-- **`hprf` is false for `prims` as the library states it.**  At the secret-key address `badAdrs`
(type `WOTS_PRF`, layer `256`), which is outside the checked domain, `prims.PRF` is the all-zero
node (`checkedNodeOrZero` of an error) while the tweakable hash is the SHA-256 of the fallback key,
which at all-zero seeds is not zero.  Checked by kernel evaluation of that one SHA-256 (`decide
+kernel`; no `native_decide`).  Hence the generic lemma `romScheme_map_romAnswer` cannot be
*applied* at `prims` (its hypothesis is false); its *conclusion* at `prims` is nevertheless true:
`romScheme_map_romAnswer_128s` below proves it another way, and that equation is the field
`EndToEnd.instantiation` (`E2E/Main.lean`). -/
theorem not_hprf : ¬ ∀ (pkSeed skSeed : Node) (a : SLHDSA.Adrs), a.IsSecretKey →
    prims.Thash pkSeed (prims.adrsToKey a) [skSeed] = prims.PRF pkSeed skSeed a := by
  intro h
  have h0 := h (zeroBytes 16) (zeroBytes 16) badAdrs (Or.inl rfl)
  revert h0
  decide +kernel

/-- Every secret child of a ledger address (the `WOTS_PRF` address of a reachable WOTS+ chain, the
`FORS_PRF` address of a reachable FORS leaf) is in the checked `ADRSc` domain.  These are the only
addresses at which honest key generation and signing read a secret. -/
theorem dom_of_secretChild {a b : SLHDSA.Adrs} (hb : b ∈ constructionAddresses vp)
    (h : .inl a ∈ childAdrs vp b) : Dom a := by
  have hA := fipsApprovedAddressBounds S128
  have hC := hA.toCanonicalAddressBounds
  rcases List.mem_append.1 (mem_secretChildren_of_inl_mem_childAdrs hb h) with h1 | h2
  · obtain ⟨⟨pos, i⟩, -, rfl⟩ := List.mem_map.1 h1
    exact sha2Domain_of_addressFacts hA (addressFacts_wotsSkAdrs hC pos i)
  · obtain ⟨b', hb', rfl⟩ := List.mem_map.1 h2
    obtain ⟨hc, hl, ht⟩ := sha2Domain_of_addressFacts hA (addressFacts_forsLeafAddresses vp hC b' hb')
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := Adrs.fits_of_isCanonical b' hc
    refine ⟨?_, hl, ht⟩
    simp [Adrs.isCanonical, forsSkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress, Adrs.setTreeIndex, Adrs.getKeyPairAddress, f1, f2, f4, f6]
    exact ⟨by decide, by decide⟩

/-! ### Honest programs depend on the secret provider only at in-domain addresses -/

/-- The public-hash interface beside an abstract secret-value oracle indexed by address. -/
abbrev SecSpec := publicHashSpec prims.core + (SLHDSA.Adrs →ₒ prims.Y)

/-- `ProbComp` answers public-hash queries by the SHA-2 functions of `prims`. -/
@[reducible] def probQ : HasQuery (publicHashSpec prims.core) ProbComp :=
  ⟨fun q => liftM (PublicHash.impl prims q)⟩

/-- Answer public-hash queries by `prims` and the secret oracle by `f`. -/
def secImpl (f : SLHDSA.Adrs → prims.core.Y) : QueryImpl SecSpec ProbComp
  | .inl q => pure (PublicHash.impl prims q)
  | .inr a => pure (f a)

attribute [local instance] probQ

/-- `secImpl f` as a query-preserving monad morphism. -/
noncomputable def secHom (f : SLHDSA.Adrs → prims.core.Y) :
    HasQuery.QueryHom (publicHashSpec prims.core) (OracleComp SecSpec) ProbComp :=
  { toMonadHom := simulateQ' (secImpl f)
    map_query' := fun q => by
      simp
      rfl }

theorem secHom_query (f : SLHDSA.Adrs → prims.core.Y) (a : SLHDSA.Adrs) :
    (secHom f).toMonadHom
        (query (spec := (SLHDSA.Adrs →ₒ prims.Y)) a : OracleComp SecSpec prims.Y) =
      pure (f a) := by
  change simulateQ (secImpl f) _ = _
  simp
  rfl

section Congr
variable {f g : SLHDSA.Adrs → prims.core.Y}
  (hfg : ∀ a b, b ∈ constructionAddresses vp → .inl a ∈ childAdrs vp b → f a = g a)
include hfg

/-- Key generation with secrets supplied by `f` or by `g` is the same program when `f` and `g` agree
at the secret children of ledger addresses. -/
theorem keygenWithSecret_congr (pkSeed : prims.core.PkSeed) :
    (GeneralScheme.keygenInternalWithSecretM prims.core (fun a => pure (f a)) pkSeed :
        ProbComp prims.core.Y) =
      GeneralScheme.keygenInternalWithSecretM prims.core (fun a => pure (g a)) pkSeed := by
  rw [← GeneralScheme.keygenInternalWithSecretM_natural prims.core (secHom f)
      (fun a => (query (spec := (SLHDSA.Adrs →ₒ prims.Y)) a : OracleComp SecSpec prims.Y))
      _ (fun a _ => secHom_query f a),
    ← GeneralScheme.keygenInternalWithSecretM_natural prims.core (secHom g)
      (fun a => (query (spec := (SLHDSA.Adrs →ₒ prims.Y)) a : OracleComp SecSpec prims.Y))
      _ (fun a _ => secHom_query g a)]
  refine keygenInternalWithSecretM_pred_of_ledger (m := OracleComp SecSpec)
    (fun {α} oa => (secHom f).toMonadHom oa = (secHom g).toMonadHom oa)
    (fun x => by simp) (fun oa ob h1 h2 => by
      rw [(secHom f).toMonadHom.mmap_bind, (secHom g).toMonadHom.mmap_bind, h1]
      exact bind_congr fun x => h2 x)
    prims.core (fun a b hb hab => by rw [secHom_query, secHom_query, hfg a b hb hab]) pkSeed
    (fun a _ xs => by rw [PublicHash.tl_natural, PublicHash.tl_natural])

/-- Signing with secrets supplied by `f` or by `g` is the same program when `f` and `g` agree at the
secret children of ledger addresses. -/
theorem signWithSecret_congr (msg : List Byte) (pkSeed : prims.core.PkSeed) (pkRoot R : prims.core.Y) :
    (GeneralScheme.signInternalWithSecretRandomizerM prims.core (fun a => pure (f a)) msg pkSeed
        pkRoot R : ProbComp (GeneralScheme.SignatureCore vp prims.core)) =
      GeneralScheme.signInternalWithSecretRandomizerM prims.core (fun a => pure (g a)) msg pkSeed
        pkRoot R := by
  rw [← GeneralScheme.signInternalWithSecretRandomizerM_natural prims.core (secHom f)
      (fun a => (query (spec := (SLHDSA.Adrs →ₒ prims.Y)) a : OracleComp SecSpec prims.Y))
      _ (fun a _ => secHom_query f a),
    ← GeneralScheme.signInternalWithSecretRandomizerM_natural prims.core (secHom g)
      (fun a => (query (spec := (SLHDSA.Adrs →ₒ prims.Y)) a : OracleComp SecSpec prims.Y))
      _ (fun a _ => secHom_query g a)]
  refine signInternalWithSecretRandomizerM_pred_of_ledger (m := OracleComp SecSpec)
    (fun {α} oa => (secHom f).toMonadHom oa = (secHom g).toMonadHom oa)
    (fun x => by simp) (fun oa ob h1 h2 => by
      rw [(secHom f).toMonadHom.mmap_bind, (secHom g).toMonadHom.mmap_bind, h1]
      exact bind_congr fun x => h2 x)
    prims.core (fun a b hb hab => by rw [secHom_query, secHom_query, hfg a b hb hab]) msg pkSeed
    pkRoot R
    (fun a _ xs => by rw [PublicHash.tl_natural, PublicHash.tl_natural])
    (by rw [PublicHash.hmsg_natural, PublicHash.hmsg_natural])

end Congr

/-- **The scheme of the security theorem, instantiated with SHA-2, is FIPS 205's internal
algorithms.**  Answering the three oracles of `romScheme prims.core (Equiv.refl _) optRand
pkSeedDist` by `romAnswer prims` (SHA-2 tweakable hash and `H_msg`, HMAC `PRF_msg`), and keeping its
uniform draws, gives exactly `internalAlg vp prims optRand pkSeedDist`: key generation is
`GeneralScheme.keygenInternal`, signing is `GeneralScheme.signInternal`, verification is
`GeneralScheme.verifyInternal`, all at `prims`.

This is the conclusion of the library's `romScheme_map_romAnswer`, whose hypothesis `hprf` is false
for `prims` (`not_hprf`).  The proof here uses `hprf_dom` only at the secret children of ledger
addresses (`dom_of_secretChild`), which are the only addresses honest key generation and signing
read a secret at (`*_pred_of_ledger`).

It is an identity of programs: it says the object bounded in `security_128s` *is* SLH-DSA-SHA2-128s
once the oracles are replaced by SHA-2.  It does not say the bound survives that replacement. -/
theorem romScheme_map_romAnswer_128s
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    (romScheme (vp := vp) prims.core (Equiv.refl _) optRand pkSeedDist).map
        (simulateQ' (unifFwdAnswerImpl (romAnswer prims))) =
      internalAlg vp prims optRand pkSeedDist := by
  let e : prims.SkSeed ≃ prims.Y := Equiv.refl _
  let F : HasQuery.QueryHom (publicHashSpec prims.core)
      (OracleComp (unifSpec + hashSpec prims.core)) ProbComp :=
    { toMonadHom := simulateQ' (unifFwdAnswerImpl (romAnswer prims))
      map_query' := fun q => by
        simp [unifFwdAnswerImpl, romAnswer] }
  have hLift : ∀ {α : Type} (oa : ProbComp α),
      F.toMonadHom (liftM oa : OracleComp (unifSpec + hashSpec prims.core) α) = oa := by
    intro α oa
    change simulateQ (unifFwdAnswerImpl (romAnswer prims)) _ = oa
    rw [unifFwdAnswerImpl, QueryImpl.passthrough_add, QueryImpl.simulateQ_add_liftM_left,
      QueryImpl.liftTarget_self, simulateQ_id']
  have hFree : ∀ {α : Type} (oa : OracleComp (publicHashSpec prims.core) α),
      (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core)
        (m := ProbComp)).toMonadHom oa = pure (simulateQ (PublicHash.impl prims) oa) := by
    intro α oa
    have hImpl : HasQuery.toQueryImpl (spec := publicHashSpec prims.core) (m := ProbComp) =
        (PublicHash.impl prims).liftTarget ProbComp := by
      funext q
      rfl
    rw [HasQuery.QueryHom.ofSimulateQ_apply, hImpl, simulateQ_liftTarget]
    rfl
  have hSecret : ∀ (pkSeed : prims.core.PkSeed) (skSeed : prims.core.SkSeed) (a : SLHDSA.Adrs),
      a.IsSecretKey → F.toMonadHom (oracleSecret prims.core e pkSeed skSeed a) =
        (pure (prims.Thash pkSeed (prims.adrsToKey a) [e skSeed]) : ProbComp prims.core.Y) := by
    intro pkSeed skSeed a ha
    rw [oracleSecret_natural prims.core F e pkSeed skSeed a]
    rfl
  have hDom : ∀ (pkSeed : prims.core.PkSeed) (skSeed : prims.core.SkSeed) (a b : SLHDSA.Adrs),
      b ∈ constructionAddresses vp → .inl a ∈ childAdrs vp b →
      prims.Thash pkSeed (prims.adrsToKey a) [e skSeed] = prims.core.PRF pkSeed skSeed a :=
    fun pkSeed skSeed a b hb hab => hprf_dom pkSeed skSeed a (dom_of_secretChild hb hab)
  apply SignatureAlg.ext
  · change F.toMonadHom (liftM pkSeedDist >>= romKeygenAt prims.core e) = _
    rw [F.toMonadHom.mmap_bind, hLift]
    refine bind_congr fun pkSeed => ?_
    rw [romKeygenAt, F.toMonadHom.mmap_bind, hLift]
    refine bind_congr fun skSeed => ?_
    rw [F.toMonadHom.mmap_bind, hLift]
    refine bind_congr fun skPrf => ?_
    rw [F.toMonadHom.mmap_bind, GeneralScheme.keygenInternalWithSecretM_natural prims.core F _ _
      (hSecret pkSeed skSeed), keygenWithSecret_congr (hDom pkSeed skSeed),
      GeneralScheme.keygenInternalWithSecretM,
      GeneralHypertree.rootWithSecretM_eq_rootM,
      ← GeneralHypertree.rootM_natural vp prims.core
        (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := ProbComp)),
      hFree, pure_bind, F.toMonadHom.mmap_pure]
    congr 1
    exact Prod.ext (GeneralScheme.keygenInternal_fst vp prims skSeed skPrf pkSeed).symm
      (GeneralScheme.keygenInternal_snd vp prims skSeed skPrf pkSeed).symm
  · funext pk sk msg
    change F.toMonadHom ((romScheme prims.core e optRand pkSeedDist).sign pk sk msg) = _
    rw [romScheme_sign, F.toMonadHom.mmap_bind, hLift]
    refine bind_congr fun addrnd => ?_
    have hR : F.toMonadHom (query (spec := prfMsgSpec prims.core) ⟨sk.skPrf, addrnd, msg⟩ :
        OracleComp (unifSpec + hashSpec prims.core) prims.Y) =
          pure (prims.PRFmsg sk.skPrf addrnd msg) := by
      simp [F, unifFwdAnswerImpl, romAnswer]
      rfl
    rw [F.toMonadHom.mmap_bind, hR, pure_bind,
      GeneralScheme.signInternalWithSecretRandomizerM_natural prims.core F _ _
        (hSecret sk.pkSeed sk.skSeed), signWithSecret_congr (hDom sk.pkSeed sk.skSeed),
      GeneralScheme.signInternalWithSecretRandomizerM_eq_signInternalWithRandomizerM,
      ← GeneralScheme.signInternalM_eq_signInternalWithRandomizerM,
      ← GeneralScheme.signInternalM_natural vp prims.core
        (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := ProbComp)),
      hFree]
    rfl
  · funext pk msg sig
    exact romScheme_verify_eq e optRand pkSeedDist pk msg sig

#print axioms security_128s
#print axioms security_128s_euf
#print axioms verifyInternalM_impl_eq
#print axioms romScheme_verify_eq
#print axioms hprf_dom
#print axioms not_hprf
#print axioms dom_of_secretChild
#print axioms romScheme_map_romAnswer_128s
end Link
