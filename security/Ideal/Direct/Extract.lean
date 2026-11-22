import Reduction.Suf

/-!
# Deterministic extraction (D3 of `status/DIRECT.md`), first part

Over the abstract scheme (any `Primitives`, any secret table `tbl`, `G2`-level objects of
`Reduction/Suf.lean`): a strong forgery is

* `evItsr` (every FORS leaf the forged digest opens was opened by a signing query: **Cover**), or
* `evColl` (a verification call of the forgery collides with a call of the honest structure at
  the same tweak on a different input: **Hit**), or
* `evHidF` (the forged FORS secret at an unopened leaf *equals* the honest one: **HiddenEq**,
  FORS part), or
* `evWots` (some hypertree layer recovers the honest WOTS+ chain ends from a different message).

`suf_extract` (`sufWin ⇒ evItsr ∨ evColl ∨ evHidF ∨ evWots`) refines the existing
`freshWin_cases`/`sameWin_cases` by splitting `evOpen` into `evHidF ∨ evColl`
(`evOpen_cases`; a new verification-call membership lemma for the FORS leaf, `fors_leaf_mem`).

The WOTS+ part (`evWots ⇒ evHidW ∨ evColl`, the first-match walk) is NOT done here; its abstract
core, the walk down a chain to the first matching position, is `chain_walk`.  What is missing for
it is stated in `status/DIRECT.md` §8: the membership of the forged and honest chain calls of a
layer in `verifyCalls` / `honestCalls`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

namespace Direct

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

set_option linter.unusedSectionVars false

/-! ## FORS leaf calls are verification calls -/

/-- The leaf call of FORS tree `i` is a call of the FORS recovery program. -/
theorem fors_leaf_mem (pk : prims.PkSeed) (s : ForsSigCore vp.params prims.core) (md : List Byte)
    (adrs : Adrs) (i : Fin vp.params.k) :
    (prims.adrsToKey (forsNodeAdrs adrs 0 (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val)),
        [(s[i.val]).sk]) ∈
      col_calls (forsPkFromSigM prims.core s md pk adrs :
        OracleComp (publicHashSpec prims.core) prims.Y) := by
  let tree : Fin vp.params.k → OracleComp (publicHashSpec prims.core) prims.Y := fun i => do
    let leaf ← PublicHash.f prims.core pk
      (forsNodeAdrs adrs 0 (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val)) (s[i.val]).sk
    PerfectMerkleTree.climbM (forsNodeHashWith (PublicHash.h prims.core pk) adrs)
      (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val) leaf (s[i.val]).auth.toList
  have hprog : (forsPkFromSigM prims.core s md pk adrs :
      OracleComp (publicHashSpec prims.core) prims.Y) =
        Vector.ofFnM tree >>= fun roots =>
          PublicHash.tl prims.core pk (forsPkAdrs adrs) roots.toList := rfl
  rw [hprog]
  refine col_mem_bind_left _ (col_mem_ofFnM tree i ?_)
  refine col_mem_bind_left _ ?_
  rw [col_calls_f]
  exact List.mem_singleton_self _

/-- The leaf call of FORS tree `i` is a verification call. -/
theorem fors_leaf_verify_mem (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) (i : Fin vp.params.k) :
    (prims.adrsToKey (forsNodeAdrs (digestParts pk sig.randomness msg).forsAdrs 0
        (leafIndex (digestParts pk sig.randomness msg) i)), [(sig.fors[i.val]).sk]) ∈
      verifyCalls pk msg sig := by
  rw [col_verifyCalls_eq]
  exact List.mem_append_left _ (fors_leaf_mem _ _ _ _ i)

/-! ## The open-preimage class -/

/-- **HiddenEq, FORS part**: at some FORS tree whose opened leaf was never opened by a signing
query, the forged secret equals the honest (reference) secret. -/
def evHidF (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims) (z : G2Out vp prims) : Prop :=
  ∃ i : Fin vp.params.k,
    ((digestParts (idealPk vp prims tbl pkSeed) z.1.2.randomness z.1.1).forsAdrs,
        leafIndex (digestParts (idealPk vp prims tbl pkSeed) z.1.2.randomness z.1.1) i) ∉
      openedLeaves (idealPk vp prims tbl pkSeed) (G2Log.signed z.2) ∧
    (z.1.2.fors[i.val]).sk = ((refSig pkSeed tbl z).fors[i.val]).sk

theorem openTree_some {pk : PublicKeyCore prims.core} {parts : DigestParts vp.params}
    {opened : List (Adrs × ℕ)} {forged ref : GeneralScheme.SignatureCore vp prims.core}
    (h : (openTree? pk parts opened forged ref).isSome = true) :
    ∃ i : Fin vp.params.k, (parts.forsAdrs, leafIndex parts i) ∉ opened ∧
      prims.F pk.pkSeed (forsNodeAdrs parts.forsAdrs 0 (leafIndex parts i)) (forged.fors[i.val]).sk =
        prims.F pk.pkSeed (forsNodeAdrs parts.forsAdrs 0 (leafIndex parts i)) (ref.fors[i.val]).sk := by
  unfold openTree? at h
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp h
  have hp := List.find?_some hi
  exact ⟨i, of_decide_eq_true hp⟩

/-- **The open-preimage class splits into HiddenEq and Hit.** -/
theorem evOpen_cases (hS : Structural vp prims) (pkSeed : prims.PkSeed)
    (tbl : SecretTable vp prims) (z : G2Out vp prims) (h : evOpen pkSeed tbl z = true) :
    evHidF pkSeed tbl z ∨ evColl pkSeed tbl z = true := by
  unfold evOpen g2ClassOf classify at h
  dsimp only at h
  split_ifs at h with h1 h2 h3
  · obtain ⟨i, hun, hF⟩ := openTree_some h3
    by_cases heq : (z.1.2.fors[i.val]).sk = ((refSig pkSeed tbl z).fors[i.val]).sk
    · exact .inl ⟨i, hun, heq⟩
    · right
      refine evColl_of_coll hS pkSeed tbl z ?_
      have hR := col_idealSign_randomness tbl pkSeed z.1.1 z.1.2.randomness
      have hm' := fors_leaf_verify_mem (idealPk vp prims tbl pkSeed) z.1.1 (refSig pkSeed tbl z) i
      rw [show (refSig pkSeed tbl z).randomness = z.1.2.randomness from hR] at hm'
      refine ⟨_, fors_leaf_verify_mem _ z.1.1 z.1.2 i, _, hm', rfl, ?_, hF⟩
      intro e
      exact heq (List.cons.inj e).1

/-! ## The combined statement -/

/-- **Deterministic extraction (FORS-refined).**  A strong forgery in `G2` is Cover, Hit,
HiddenEq at a FORS leaf, or the WOTS+ event. -/
theorem suf_extract (hS : Structural vp prims) (pkSeed : prims.PkSeed)
    (tbl : SecretTable vp prims) (z : G2Out vp prims) (h : sufWin pkSeed tbl z = true) :
    evItsr pkSeed tbl z = true ∨ evColl pkSeed tbl z = true ∨ evHidF pkSeed tbl z ∨
      evWots pkSeed tbl z = true := by
  have h4 := (sufWin_cases pkSeed tbl z h).elim (freshWin_cases hS pkSeed tbl z)
    (sameWin_cases hS pkSeed tbl z)
  rcases h4 with h | h | h | h
  · exact .inl h
  · rcases evOpen_cases hS pkSeed tbl z h with h' | h'
    · exact .inr (.inr (.inl h'))
    · exact .inr (.inl h')
  · exact .inr (.inl h)
  · exact .inr (.inr (.inr h))

/-- **EUF form**: every EUF forgery (`g2ValidWin`) is a fresh-randomizer forgery, hence the same
four events. -/
theorem fresh_extract (hS : Structural vp prims) (pkSeed : prims.PkSeed)
    (tbl : SecretTable vp prims) (z : G2Out vp prims) (h : freshWin pkSeed tbl z = true) :
    evItsr pkSeed tbl z = true ∨ evColl pkSeed tbl z = true ∨ evHidF pkSeed tbl z ∨
      evWots pkSeed tbl z = true := by
  rcases freshWin_cases hS pkSeed tbl z h with h | h | h | h
  · exact .inl h
  · rcases evOpen_cases hS pkSeed tbl z h with h' | h'
    · exact .inr (.inr (.inl h'))
    · exact .inr (.inl h')
  · exact .inr (.inl h)
  · exact .inr (.inr (.inr h))

/-! ## The first-match walk (abstract core of the WOTS+ refinement) -/

/-- **First-match walk.**  Two chains `v`, `y` stepped by the same functions `F p` from position
`a` to `b` that agree at `b` either agree at `a` or collide at some position in `[a, b)`. -/
theorem chain_walk {Y : Type} (F : ℕ → Y → Y) (v y : ℕ → Y) (a : ℕ) :
    ∀ n, (∀ p, a ≤ p → p < a + n → v (p + 1) = F p (v p) ∧ y (p + 1) = F p (y p)) →
      v (a + n) = y (a + n) →
      v a = y a ∨ ∃ p, a ≤ p ∧ p < a + n ∧ v p ≠ y p ∧ F p (v p) = F p (y p) := by
  intro n
  induction n with
  | zero => intro _ h; exact .inl h
  | succ n ih =>
    intro hstep htop
    by_cases h : v (a + n) = y (a + n)
    · rcases ih (fun p hp hp' => hstep p hp (by omega)) h with h' | ⟨p, hp, hp', hne, hc⟩
      · exact .inl h'
      · exact .inr ⟨p, hp, by omega, hne, hc⟩
    · obtain ⟨e1, e2⟩ := hstep (a + n) (by omega) (by omega)
      refine .inr ⟨a + n, by omega, by omega, h, ?_⟩
      rw [← e1, ← e2]
      exact htop

end Direct

end Reduction

#print axioms Reduction.Direct.fors_leaf_verify_mem
#print axioms Reduction.Direct.evOpen_cases
#print axioms Reduction.Direct.suf_extract
#print axioms Reduction.Direct.fresh_extract
#print axioms Reduction.Direct.chain_walk
