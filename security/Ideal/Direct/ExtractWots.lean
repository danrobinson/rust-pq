import Ideal.Direct.Extract

/-!
# Deterministic extraction (D3 of `status/DIRECT.md`), WOTS+ part

Over the abstract scheme (any `Primitives`, any secret table `tbl`): the WOTS+ event `evWots` of
`Reduction/Suf.lean` (some hypertree layer recovers the honest chain ends from a different
message) splits into

* `evHidW`: at some layer `j` and chain `i` whose forged digit `a` is below the honest digit `b`,
  the forged chain value *equals* the honest (hidden) chain value at position `a`
  (**HiddenEq**, WOTS+ part), or
* `evColl` (a verification call of the forgery collides with a call of the honest structure at
  the same tweak on a different input: **Hit**).

`evWots_cases` is the first-match walk: VCVio's `wotsPkFromSigTops_cases` gives a chain with
`a < b` carrying either an `F`-preimage of the honest value at `b` (then `chain_walk` walks the
forged chain down from `b` to `a`: either the start values agree, or some position in `[a, b)`
is a collision of a forged verification call with an honest call) or a collision at some
position `t ≥ b` between the verification calls of the forgery and of the reference signature.

Membership lemmas (new): `col_chain_mem` (a chain program makes the call of each of its steps),
`wots_chain_verify_mem` (each step of the forged chain at a layer is a verification call),
`sub_chain_mem`, `wots_chain_honest_mem` (each step of every honest chain on the path is a call of
the honest structure).

Combined: `suf_extract_full`, `fresh_extract_full` (`sufWin ⇒ evItsr ∨ evColl ∨ evHidF ∨ evHidW`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

namespace Direct

variable {vp : ValidatedParams} {prims : Primitives vp.params}

set_option linter.unusedSectionVars false

/-! ## A chain program makes the call of each of its steps -/

/-- Step `q < n` of the chain from `x` at index `i` is a call of the chain program. -/
theorem col_chain_mem (pk : prims.PkSeed) (adrs : Adrs) (x : prims.Y) (i : ℕ) :
    ∀ n q, q < n →
      (prims.adrsToKey (adrs.setHashAddress (i + q)), [chain prims pk adrs x i q]) ∈
        col_calls (chainWith (PublicHash.f prims.core pk) adrs x i n :
          OracleComp (publicHashSpec prims.core) prims.Y)
  | 0, q, hq => absurd hq (Nat.not_lt_zero q)
  | n + 1, q, hq => by
    rw [chainWith_succ, col_calls_bind]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hq with h | rfl
    · exact List.mem_append_left _ (col_chain_mem pk adrs x i n q h)
    · refine List.mem_append_right _ ?_
      rw [col_calls_f]
      exact List.mem_singleton_self _

/-! ## The forged chain steps are verification calls -/

/-- Every step at position `t ∈ [a, w − 1)` of the chain recovered at layer `j`, chain `i`, is a
verification call (`a` the digit of the recovered layer message). -/
theorem wots_chain_verify_mem (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) (j : Fin vp.params.d)
    (i : Fin vp.params.len) (t : ℕ)
    (ht1 : chainStepsCore prims.core
      (layerMsg pk.pkSeed (digestParts pk sig.randomness msg) sig.hypertree
        (forsPkFromSig prims sig.fors (digestParts pk sig.randomness msg).md.toList pk.pkSeed
          (digestParts pk sig.randomness msg).forsAdrs) j.val) i.val ≤ t)
    (ht2 : t < vp.params.w - 1) :
    (prims.adrsToKey ((wotsChainAdrs (layerWotsAdrs (digestParts pk sig.randomness msg) j)
        i.val).setHashAddress t),
      [chain prims pk.pkSeed (wotsChainAdrs (layerWotsAdrs (digestParts pk sig.randomness msg) j)
          i.val) ((sig.hypertree[j.val]).wots[i.val])
        (chainStepsCore prims.core
          (layerMsg pk.pkSeed (digestParts pk sig.randomness msg) sig.hypertree
            (forsPkFromSig prims sig.fors (digestParts pk sig.randomness msg).md.toList pk.pkSeed
              (digestParts pk sig.randomness msg).forsAdrs) j.val) i.val)
        (t - chainStepsCore prims.core
          (layerMsg pk.pkSeed (digestParts pk sig.randomness msg) sig.hypertree
            (forsPkFromSig prims sig.fors (digestParts pk sig.randomness msg).md.toList pk.pkSeed
              (digestParts pk sig.randomness msg).forsAdrs) j.val) i.val)]) ∈
      verifyCalls pk msg sig := by
  rw [col_verifyCalls_eq]
  refine List.mem_append_right _ ((col_pkFromSig pk.pkSeed _ sig.hypertree _).2 j _ ?_)
  set parts := digestParts pk sig.randomness msg
  set m := layerMsg pk.pkSeed parts sig.hypertree
    (forsPkFromSig prims sig.fors parts.md.toList pk.pkSeed parts.forsAdrs) j.val
  set a := chainStepsCore prims.core m i.val
  have hprog : col_layerProg pk.pkSeed parts sig.hypertree
      (forsPkFromSig prims sig.fors parts.md.toList pk.pkSeed parts.forsAdrs) j =
      ((wotsPkFromSigTopsM prims.core (sig.hypertree[j.val]).wots m pk.pkSeed
          (layerWotsAdrs parts j) :
          OracleComp (publicHashSpec prims.core) (Vector prims.Y vp.params.len)) >>= fun tops =>
        PublicHash.tl prims.core pk.pkSeed (wotsPkAdrs (layerWotsAdrs parts j)) tops.toList) >>=
      fun leaf => PerfectMerkleTree.climbM
        (fun z t l r => PublicHash.h prims.core pk.pkSeed
          (xmssNodeAdrs (LayerPosition.atLayer vp parts j).toAdrs z t) l r)
        (LayerPosition.atLayer vp parts j).leaf.val leaf (sig.hypertree[j.val]).auth.toList := rfl
  rw [hprog]
  refine col_mem_bind_left _ (col_mem_bind_left _ ?_)
  refine col_mem_ofFnM _ i ?_
  have h := col_chain_mem pk.pkSeed (wotsChainAdrs (layerWotsAdrs parts j) i.val)
    ((sig.hypertree[j.val]).wots[i.val]) a (vp.params.w - 1 - a) (t - a) (by omega)
  rw [show a + (t - a) = t by omega] at h
  exact h

/-! ## The honest chain steps are honest calls -/

section Honest

open sub_W

/-- Writer-monad chain step membership, with the value of the chain. -/
theorem sub_chain_mem (pk : prims.PkSeed) (adrs : Adrs) (x : prims.Y) (i : ℕ) :
    ∀ n, val (chainWith (fun a y => sub_wTh (prims := prims) pk (prims.adrsToKey a) [y])
        adrs x i n) = chain prims pk adrs x i n ∧
      ∀ q, q < n →
        (prims.adrsToKey (adrs.setHashAddress (i + q)), [chain prims pk adrs x i q]) ∈
          calls (chainWith (fun a y => sub_wTh (prims := prims) pk (prims.adrsToKey a) [y])
            adrs x i n)
  | 0 => ⟨rfl, fun q hq => absurd hq (Nat.not_lt_zero q)⟩
  | n + 1 => by
    obtain ⟨hv, hc⟩ := sub_chain_mem pk adrs x i n
    rw [chainWith_succ, val_bind, calls_bind, hv, chain_succ]
    refine ⟨rfl, fun q hq => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hq with h | rfl
    · exact List.mem_append_left _ (hc q h)
    · exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Every step at position `p < w − 1` of every honest chain of the WOTS+ instance on the path of
`parts` at layer `j` is a call of the honest structure. -/
theorem wots_chain_honest_mem (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed)
    (parts : DigestParts vp.params) (j : Fin vp.params.d) (i : Fin vp.params.len) (p : ℕ)
    (hp : p < vp.params.w - 1) :
    (prims.adrsToKey ((wotsChainAdrs (layerWotsAdrs parts j) i.val).setHashAddress p),
      [chain prims pkSeed (wotsChainAdrs (layerWotsAdrs parts j) i.val)
        (secretOf vp prims tbl (wotsSkAdrs (layerWotsAdrs parts j) i.val)) 0 p]) ∈
      honestCalls tbl pkSeed := by
  rw [sub_honestCalls_eq]
  unfold structureVia
  rw [calls_bind]
  refine List.mem_append_right _ ?_
  rw [mem_calls_forM]
  refine ⟨LayerTreeCoord.ofPosition (LayerPosition.atLayer vp parts j),
    mem_allXmssTrees vp _, ?_⟩
  rw [calls_bind]
  refine List.mem_append_left _ ?_
  set pos := LayerPosition.atLayer vp parts j
  have hidx := pos.leaf.isLt
  obtain ⟨-, -, ml⟩ := merkle_spec
    (xmssLeafWithSecret prims.core (fun a y => sub_wTh (prims := prims) pkSeed (prims.adrsToKey a) [y])
      (fun a xs => sub_wTh pkSeed (prims.adrsToKey a) xs) (fun a => pure (secretOf vp prims tbl a))
      pos.toAdrs)
    (xmssNodeHashWith (fun a l r => sub_wTh pkSeed (prims.adrsToKey a) [l, r]) pos.toAdrs)
    pos.leaf.val vp.params.hp
  rw [Nat.div_eq_of_lt hidx] at ml
  refine ml _ ?_
  show _ ∈ calls (wotsPkGenWithSecret prims.core _ _ _ (layerWotsAdrs parts j))
  unfold wotsPkGenWithSecret
  rw [calls_bind]
  refine List.mem_append_left _ ?_
  unfold wotsPkGenTopsWithSecret
  rw [mem_calls_ofFnM]
  refine ⟨i, ?_⟩
  rw [calls_bind, calls_pure, List.nil_append, val_pure]
  have h := (sub_chain_mem pkSeed (wotsChainAdrs (layerWotsAdrs parts j) i.val)
    (secretOf vp prims tbl (wotsSkAdrs (layerWotsAdrs parts j) i.val)) 0 (vp.params.w - 1)).2 p hp
  rw [Nat.zero_add] at h
  exact h

end Honest

/-! ## HiddenEq, WOTS+ part, and the case split -/

variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

/-- The layer-`j` message the forgery's verification WOTS+-recovers. -/
def fLayerMsg (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims) (z : G2Out vp prims)
    (j : ℕ) : prims.Y :=
  layerMsg pkSeed (digestParts (idealPk vp prims tbl pkSeed) z.1.2.randomness z.1.1) z.1.2.hypertree
    (forsPkFromSig prims z.1.2.fors
      (digestParts (idealPk vp prims tbl pkSeed) z.1.2.randomness z.1.1).md.toList pkSeed
      (digestParts (idealPk vp prims tbl pkSeed) z.1.2.randomness z.1.1).forsAdrs) j

/-- **HiddenEq, WOTS+ part**: at some layer `j` and chain `i` whose forged digit is below the
honest digit, the forged chain value equals the honest chain value at the forged digit. -/
def evHidW (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims) (z : G2Out vp prims) : Prop :=
  ∃ (j : Fin vp.params.d) (i : Fin vp.params.len),
    chainStepsCore prims.core (fLayerMsg pkSeed tbl z j.val) i.val <
      chainStepsCore prims.core (hMsgA tbl pkSeed
        (layerWotsAdrs (digestParts (idealPk vp prims tbl pkSeed) z.1.2.randomness z.1.1) j)) i.val ∧
    (z.1.2.hypertree[j.val]).wots[i.val] =
      chain prims pkSeed
        (wotsChainAdrs (layerWotsAdrs (digestParts (idealPk vp prims tbl pkSeed) z.1.2.randomness z.1.1) j) i.val)
        (secretOf vp prims tbl
          (wotsSkAdrs (layerWotsAdrs (digestParts (idealPk vp prims tbl pkSeed) z.1.2.randomness z.1.1) j) i.val))
        0 (chainStepsCore prims.core (fLayerMsg pkSeed tbl z j.val) i.val)

/-- A verification call of the forgery colliding with an honest call is `evColl`. -/
theorem evColl_of_honest (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims) (z : G2Out vp prims)
    (c c' : prims.AdrsKey × List prims.Y)
    (hc : c ∈ verifyCalls (idealPk vp prims tbl pkSeed) z.1.1 z.1.2)
    (hc' : c' ∈ honestCalls tbl pkSeed) (hkey : c.1 = c'.1) (hne : c.2 ≠ c'.2)
    (hcol : prims.Thash pkSeed c.1 c.2 = prims.Thash pkSeed c'.1 c'.2) :
    evColl pkSeed tbl z = true := by
  unfold evColl findCollision
  rw [List.findSome?_isSome_iff]
  refine ⟨c, hc, ?_⟩
  have hlt : (honestCalls tbl pkSeed).findIdx (fun t =>
      decide (t.1 = c.1 ∧ c.2 ≠ t.2 ∧ prims.Thash pkSeed c.1 c.2 = prims.Thash pkSeed t.1 t.2)) <
      (honestCalls tbl pkSeed).length :=
    List.findIdx_lt_length_of_exists ⟨c', hc', decide_eq_true ⟨hkey.symm, hne, hcol⟩⟩
  simp only [hlt, ↓reduceIte]
  rfl

/-- **The WOTS+ event splits into HiddenEq and Hit** (the first-match walk). -/
theorem evWots_cases (hS : Structural vp prims) (pkSeed : prims.PkSeed)
    (tbl : SecretTable vp prims) (z : G2Out vp prims) (h : evWots pkSeed tbl z = true) :
    evHidW pkSeed tbl z ∨ evColl pkSeed tbl z = true := by
  set pk := idealPk vp prims tbl pkSeed with hpk
  set parts := digestParts pk z.1.2.randomness z.1.1 with hparts
  set ref := refSig pkSeed tbl z with href
  have hR : ref.randomness = z.1.2.randomness := col_idealSign_randomness tbl pkSeed z.1.1 _
  have hpks : pk.pkSeed = pkSeed := rfl
  unfold evWots at h
  rw [Bool.and_eq_true] at h
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp h.2
  unfold wotsLayer? at hj
  dsimp only at hj
  have hjd := List.find?_some hj
  simp only [decide_eq_true_eq] at hjd
  obtain ⟨hne, htops⟩ := hjd
  -- the reference layer: honest signature on the honest message
  obtain ⟨hrsig, hrmsg⟩ := y_idealSign_layer tbl z.1.1 pk z.1.2.randomness j
  change (ref.hypertree[j.val]) = _ at hrsig
  change layerMsg pkSeed parts ref.hypertree
    (forsPkFromSig prims ref.fors parts.md.toList pkSeed parts.forsAdrs) j.val =
      hMsgA tbl pkSeed (layerWotsAdrs parts j) at hrmsg
  set A := layerWotsAdrs parts j with hA
  set mF := layerMsg pkSeed parts z.1.2.hypertree
    (forsPkFromSig prims z.1.2.fors parts.md.toList pkSeed parts.forsAdrs) j.val with hmF
  set mH := hMsgA tbl pkSeed A with hmH
  have hne' : mF ≠ mH := fun e => hne (e.trans hrmsg.symm)
  have htops' : wotsPkFromSigTops prims (z.1.2.hypertree[j.val]).wots mF pkSeed A =
      wotsPkFromSigTops prims (ref.hypertree[j.val]).wots mH pkSeed A := by
    have := htops
    unfold layerTops at this
    exact this.trans (congrArg (fun m => wotsPkFromSigTops prims (ref.hypertree[j.val]).wots m
      pkSeed A) hrmsg)
  obtain ⟨i, hab, hcase⟩ := wotsPkFromSigTops_cases vp.valid prims hS.byteLaws
    (z.1.2.hypertree[j.val]).wots (ref.hypertree[j.val]).wots mF mH pkSeed A hne' htops'
  set a := chainStepsCore prims.core mF i.val with ha
  set b := chainStepsCore prims.core mH i.val with hb
  have hbw : b ≤ vp.params.w - 1 := chainStepsCore_le prims.core mH i.val
  -- the honest value at chain `i` of the reference signature
  have hrho : (ref.hypertree[j.val]).wots[i.val] =
      chain prims pkSeed (wotsChainAdrs A i.val) (secretOf vp prims tbl (wotsSkAdrs A i.val)) 0 b := by
    rw [hrsig]
    show (Vector.ofFn fun i : Fin vp.params.len => _)[i.val] = _
    rw [Vector.getElem_ofFn]; rfl
  set σ := (z.1.2.hypertree[j.val]).wots[i.val] with hσ
  set s0 := secretOf vp prims tbl (wotsSkAdrs A i.val) with hs0
  let F : ℕ → prims.Y → prims.Y := fun p y => prims.F pkSeed ((wotsChainAdrs A i.val).setHashAddress p) y
  let v : ℕ → prims.Y := fun p => chain prims pkSeed (wotsChainAdrs A i.val) σ a (p - a)
  let y : ℕ → prims.Y := fun p => chain prims pkSeed (wotsChainAdrs A i.val) s0 0 p
  have hvmem : ∀ p, a ≤ p → p < vp.params.w - 1 →
      (prims.adrsToKey ((wotsChainAdrs A i.val).setHashAddress p), [v p]) ∈
        verifyCalls pk z.1.1 z.1.2 := fun p hp1 hp2 =>
    wots_chain_verify_mem pk z.1.1 z.1.2 j i p hp1 hp2
  have hymem : ∀ p, p < vp.params.w - 1 →
      (prims.adrsToKey ((wotsChainAdrs A i.val).setHashAddress p), [y p]) ∈
        honestCalls tbl pkSeed := fun p hp => wots_chain_honest_mem tbl pkSeed parts j i p hp
  rcases hcase with hpre | ⟨t, ht1, ht2, htne, htcol⟩
  · -- preimage of the honest value at `b`: walk down to `a`
    have hstep : ∀ p, a ≤ p → p < a + (b - a) → v (p + 1) = F p (v p) ∧ y (p + 1) = F p (y p) := by
      intro p hp _
      refine ⟨?_, ?_⟩
      · show chain prims pkSeed _ σ a (p + 1 - a) = _
        rw [show p + 1 - a = (p - a) + 1 by omega, chain_succ, show a + (p - a) = p by omega]
      · show chain prims pkSeed _ s0 0 (p + 1) = _
        rw [chain_succ, Nat.zero_add]
    have htop : v (a + (b - a)) = y (a + (b - a)) := by
      rw [show a + (b - a) = b by omega]
      show chain prims pkSeed _ σ a (b - a) = chain prims pkSeed _ s0 0 b
      rw [← hrho, ← hpre, show b - a = (b - 1 - a) + 1 by omega, chain_succ,
        show a + (b - 1 - a) = b - 1 by omega]
    rcases Reduction.Direct.chain_walk F v y a (b - a) hstep htop with heq | ⟨p, hp1, hp2, hpne, hpcol⟩
    · left
      refine ⟨j, i, hab, ?_⟩
      have : v a = σ := by show chain prims pkSeed _ σ a (a - a) = σ; rw [Nat.sub_self]; rfl
      exact this.symm.trans heq
    · right
      exact evColl_of_honest pkSeed tbl z _ _ (hvmem p hp1 (by omega)) (hymem p (by omega)) rfl
        (fun e => hpne (List.cons.inj e).1) hpcol
  · -- collision above `b` between the forged and the reference chains
    right
    have hm := wots_chain_verify_mem pk z.1.1 ref j i t
    refine evColl_of_coll hS pkSeed tbl z ⟨_, hvmem t (by omega) ht2,
      (prims.adrsToKey ((wotsChainAdrs A i.val).setHashAddress t),
        [chain prims pkSeed (wotsChainAdrs A i.val) ((ref.hypertree[j.val]).wots[i.val]) b (t - b)]),
      ?_, rfl, fun e => htne (List.cons.inj e).1, htcol⟩
    rw [hR] at hm
    rw [show layerMsg pk.pkSeed (digestParts pk z.1.2.randomness z.1.1) ref.hypertree
      (forsPkFromSig prims ref.fors (digestParts pk z.1.2.randomness z.1.1).md.toList pk.pkSeed
        (digestParts pk z.1.2.randomness z.1.1).forsAdrs) j.val = mH from hrmsg] at hm
    exact hm ht1 ht2

/-! ## The combined statement -/

/-- **Deterministic extraction (full).**  A strong forgery in `G2` is Cover, Hit, or HiddenEq
(at a FORS leaf or at a WOTS+ chain). -/
theorem suf_extract_full (hS : Structural vp prims) (pkSeed : prims.PkSeed)
    (tbl : SecretTable vp prims) (z : G2Out vp prims) (h : sufWin pkSeed tbl z = true) :
    evItsr pkSeed tbl z = true ∨ evColl pkSeed tbl z = true ∨ evHidF pkSeed tbl z ∨
      evHidW pkSeed tbl z := by
  rcases suf_extract hS pkSeed tbl z h with h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · rcases evWots_cases hS pkSeed tbl z h with h' | h'
    · exact .inr (.inr (.inr h'))
    · exact .inr (.inl h')

/-- **Deterministic extraction (full), EUF form.** -/
theorem fresh_extract_full (hS : Structural vp prims) (pkSeed : prims.PkSeed)
    (tbl : SecretTable vp prims) (z : G2Out vp prims) (h : freshWin pkSeed tbl z = true) :
    evItsr pkSeed tbl z = true ∨ evColl pkSeed tbl z = true ∨ evHidF pkSeed tbl z ∨
      evHidW pkSeed tbl z := by
  rcases fresh_extract hS pkSeed tbl z h with h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · rcases evWots_cases hS pkSeed tbl z h with h' | h'
    · exact .inr (.inr (.inr h'))
    · exact .inr (.inl h')

end Direct

end Reduction

#print axioms Reduction.Direct.wots_chain_verify_mem
#print axioms Reduction.Direct.wots_chain_honest_mem
#print axioms Reduction.Direct.evWots_cases
#print axioms Reduction.Direct.suf_extract_full
#print axioms Reduction.Direct.fresh_extract_full
