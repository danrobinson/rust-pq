import Ideal.Games.Itsr
import Ideal.Sha.HmsgShape
import Ideal.Inst.WotsPre128
import HashSig.SLHDSA.Security.DigestTransport

/-!
# ITSR of `H_msg` at SLH-DSA-SHA2-128s in the ideal-compression model
-/

open OracleComp OracleSpec ENNReal KeyedHash

namespace Ideal

open SLHDSA SLHDSA.DigestTransport KeyedHash.Covering AnswerTape Ideal.HP Ideal.Itsr

/-! ## From index coverage to the abstract covering model -/

section Cover

variable (vp : ValidatedParams)

/-- The index map of the Reduction's ITSR problem. -/
def idxOf (d : Bytes vp.params.m) : List (Adrs × ℕ) :=
  Reduction.forsIndices vp (splitDigest vp.params d)

theorem match_of_mem_idxOf (y z : Bytes vp.params.m) (i : Fin vp.params.k)
    (h : ((splitDigest vp.params y).forsAdrs,
        i.val * 2 ^ vp.params.a + forsIdx vp.params (splitDigest vp.params y).md.toList i.val) ∈
      idxOf vp z) :
    (coveringDigest vp z).1 = (coveringDigest vp y).1 ∧
      (coveringDigest vp z).2 i = (coveringDigest vp y).2 i := by
  simp only [idxOf, Reduction.forsIndices, List.mem_map, List.mem_range] at h
  obtain ⟨j, hj, he⟩ := h
  obtain ⟨hadr, hnum⟩ := Prod.mk.inj he
  have ht : (splitDigest vp.params z).idxTree.val = (splitDigest vp.params y).idxTree.val := by
    have := congrArg Adrs.tree hadr
    simpa using this
  have hl : (splitDigest vp.params z).idxLeaf.val = (splitDigest vp.params y).idxLeaf.val := by
    have := congrArg Adrs.getKeyPairAddress hadr
    simpa using this
  have hz := forsIdx_lt vp.params (splitDigest vp.params z).md.toList j
  have hy := forsIdx_lt vp.params (splitDigest vp.params y).md.toList i.val
  have key : ∀ j i fz fy A : ℕ, 0 < A → fz < A → fy < A → j * A + fz = i * A + fy →
      j = i ∧ fz = fy := by
    intro j i fz fy A hA hz hy h
    have h1 := congrArg (· / A) h
    simp only [Nat.mul_comm _ A, Nat.mul_add_div hA, Nat.div_eq_of_lt hz,
      Nat.div_eq_of_lt hy, Nat.add_zero] at h1
    subst h1
    exact ⟨rfl, by omega⟩
  obtain ⟨hji, hf⟩ := key _ _ _ _ _ (Nat.two_pow_pos _) hz hy hnum
  subst hji
  refine ⟨(coveringDigest_fst_eq_iff vp z y).2 ⟨Fin.ext ht, Fin.ext hl⟩, Fin.ext ?_⟩
  rw [coveringDigest_snd_val, coveringDigest_snd_val, hf]

/-- Index coverage of a tuple of digests is coverage of the decoded tuple in VCVio's abstract
model. -/
theorem tapeCoveredReuse_of_covP (n : ℕ) (w : Fin n → Bytes vp.params.m)
    (h : CovP (idxOf vp) (List.ofFn w)) :
    TapeCoveredReuse vp.params.h vp.params.a vp.params.k n fun i => coveringDigest vp (w i) := by
  obtain ⟨pre, y, post, hl, hcov⟩ := h
  have hn : n = pre.length + (post.length + 1) := by
    have := congrArg List.length hl
    simpa using this
  have hget : ∀ j : Fin n, (pre ++ y :: post)[j.val]? = some (w j) := by
    intro j
    rw [← hl]
    simp
  have hy : w ⟨pre.length, by omega⟩ = y := by
    have := hget ⟨pre.length, by omega⟩
    simpa using this.symm
  have hex : ∀ z ∈ pre ++ post, ∃ j : Fin n, j ≠ ⟨pre.length, by omega⟩ ∧ w j = z := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hz
      refine ⟨⟨m, by omega⟩, fun e => ?_, ?_⟩
      · have := congrArg Fin.val e
        simp at this
        omega
      · have := hget ⟨m, by omega⟩
        rw [List.getElem?_append_left hm, List.getElem?_eq_getElem hm] at this
        exact (Option.some.inj this).symm
    · obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hz
      refine ⟨⟨pre.length + (m + 1), by omega⟩, fun e => ?_, ?_⟩
      · have := congrArg Fin.val e
        simp at this
      · have := hget ⟨pre.length + (m + 1), by omega⟩
        rw [List.getElem?_append_right (by simp)] at this
        simp only [Nat.add_sub_cancel_left, List.getElem?_cons_succ,
          List.getElem?_eq_getElem hm] at this
        exact (Option.some.inj this).symm
  have hstep : ∀ i : Fin vp.params.k, ∃ j : Fin n, j ≠ ⟨pre.length, by omega⟩ ∧
      (coveringDigest vp (w j)).1 = (coveringDigest vp y).1 ∧
        (coveringDigest vp (w j)).2 i = (coveringDigest vp y).2 i := by
    intro i
    obtain ⟨z, hz, hiz⟩ := hcov ((splitDigest vp.params y).forsAdrs,
        i.val * 2 ^ vp.params.a + forsIdx vp.params (splitDigest vp.params y).md.toList i.val)
      (by
        simp only [idxOf, Reduction.forsIndices, List.mem_map, List.mem_range]
        exact ⟨i.val, i.isLt, rfl⟩)
    obtain ⟨j, hj, rfl⟩ := hex z hz
    exact ⟨j, hj, match_of_mem_idxOf vp y (w j) i hiz⟩
  choose f hf1 hf2 using hstep
  refine ⟨⟨pre.length, by omega⟩, f, hf1, fun i => ?_⟩
  dsimp only
  rw [hy]
  exact hf2 i

/-- The explicit sum bounding tuple coverage (`evalDist_answerTape_tapeCoveredReuse_le`). -/
noncomputable def reuseSum (h a k n : ℕ) : ℝ≥0∞ :=
  ∑ c ∈ Finset.univ.filter (fun c : Fin n × (Fin k → Fin n) => ∀ i, c.2 i ≠ c.1),
    (((2 : ℝ≥0∞) ^ h)⁻¹) ^ (Finset.univ.image c.2).card * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k

/-- The explicit sum is at most `n` times VCVio's per-target coverage bound at `n` coverers. -/
theorem reuseSum_le (h a k n : ℕ) : reuseSum h a k n ≤ n * targetCoverBound h a k n := by
  classical
  rw [← closedForm_eq_mul_targetCoverBound, ← sum_pow_card_image_eq_closedForm]
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- **Coverage of a tape of independent uniform `H_msg` digests.** -/
theorem prT_tape_cov_le (n : ℕ) :
    prT (tapeList (Bytes vp.params.m) n >>= fun r => pure (covB (idxOf vp) r)) ≤
      reuseSum vp.params.h vp.params.a vp.params.k n := by
  let _ : MeasurableSpace (Bytes vp.params.m) := ⊤
  have _ : DiscreteMeasurableSpace (Bytes vp.params.m) := ⟨fun _ => trivial⟩
  rw [prT_bind_pure, tapeList_eq_map_answerTape, prEvent_map]
  refine (prEvent_mono _ _ (fun v : Fin n → Bytes vp.params.m =>
    TapeCoveredReuse vp.params.h vp.params.a vp.params.k n fun i => coveringDigest vp (v i))
    fun v hv => ?_).trans ?_
  · simp only [covB, decide_eq_true_eq] at hv
    exact tapeCoveredReuse_of_covP vp n v hv
  · rw [prEvent_eq_evalDist_of_discrete]
    exact (evalDist_answerTape_preimage_coveringDigest vp n
      {v | TapeCoveredReuse vp.params.h vp.params.a vp.params.k n v}).trans_le
      (evalDist_answerTape_tapeCoveredReuse_le _ _ _ n)

end Cover

/-! ## The instance at SLH-DSA-SHA2-128s -/

/-- `H_msg` inputs `(PK.seed, PK.root, M)`. -/
abbrev X128 := Bytes 16 × Bytes 16 × List UInt8

/-- The inner blocks of `H_msg(R, pk, root, M)`. -/
def ibH (kx : Bytes 16 × X128) : List Blk := iblocksH kx.1 kx.2.1 kx.2.2.1 kx.2.2.2

/-- The outer blocks of `H_msg(R, pk, root, M)` at the inner digest `s`. -/
def obH (kx : Bytes 16 × X128) (s : St) : List Blk := oblocksH kx.1 kx.2.1 s

theorem ibH_injective : Function.Injective ibH := by
  rintro ⟨R, pk, root, M⟩ ⟨R', pk', root', M'⟩ h
  obtain ⟨h1, h2, h3, h4⟩ := iblocksH_injective h
  exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))

theorem obH_inj (kx kx' : Bytes 16 × X128) (s s' : St) (h : obH kx s = obH kx' s') : s = s' :=
  (oblocksH_injective h).2.2

theorem obH_ne_nil (kx : Bytes 16 × X128) (s : St) : obH kx s ≠ [] := by
  intro h
  have := oblocksH_length kx.1 kx.2.1 s
  rw [show oblocksH kx.1 kx.2.1 s = [] from h] at this
  simp at this

/-- The FORS index map of the Reduction's ITSR problem at 128s. -/
abbrev idx128 : Bytes 30 → List (Adrs × ℕ) := idxOf Link.vp

/-- Ideal-model ITSR adversaries against `H_msg` at 128s. -/
abbrev ItsrAdv128 := ItsrAdvI St Blk (Bytes 16) X128

/-- The Reduction's ITSR problem at the generic primitives over the table `g` is the ITSR problem
of the two-level Merkle–Damgård hash `hashG IV128 ibH obH dig30 g`. -/
theorem itsrProblem_eq_probI (g : CF St Blk) :
    Reduction.itsrProblem Link.vp (primsG (liftC g)) =
      @probI St Blk (Bytes 16) X128 (Bytes 30) (Adrs × ℕ) sampY128 IV128 ibH obH dig30 idx128 g := by
  have h : (fun (R : Bytes 16) (x : X128) => (primsG (liftC g)).Hmsg R x.1 x.2.1 x.2.2) =
      fun k x => hashG IV128 ibH obH dig30 g (k, x) := by
    funext R x
    exact hmsg_shape g R x.1 x.2.1 x.2.2
  show ({ khf := { keygen := @uniformSample (Bytes 16) sampY128,
                   hash := fun (R : Bytes 16) (x : X128) =>
                     (primsG (liftC g)).Hmsg R x.1 x.2.1 x.2.2 },
          indices := idx128 } : ITSRProblem (Bytes 16) X128 (Bytes 30) (Adrs × ℕ)) = _
  rw [h]
  rfl

/-- The adversary against the Reduction's ITSR problem at the table `g`. -/
def instItsr (A : ItsrAdv128) (g : CF St Blk) :
    ITSRAdversary (Reduction.itsrProblem Link.vp (primsG (liftC g))) where
  main := simulateQ (instImpl g) A

/-- ITSR advantage against `H_msg` at 128s in the ideal-compression model: the Reduction's ITSR
experiment at the primitives built from `g`, the adversary's compression queries answered by `g`,
for a uniformly random table `g`. -/
noncomputable def itsrI (A : ItsrAdv128) : ℝ≥0∞ :=
  cfAdvantage fun g => ITSRExperiment (instItsr A g)

/-- The whole ITSR experiment for `H_msg` at 128s (adversary, target oracle, final check) as one
program over the compression oracle; its compression calls are what `Q` bounds in
`itsr_bound_128s`. -/
noncomputable def itsrProg128 (A : ItsrAdv128) : OracleComp (unifSpec + hS St Blk) Bool :=
  @gameProg St Blk (Bytes 16) X128 (Bytes 30) (Adrs × ℕ) sampY128 _ _ _ IV128 ibH obH dig30 idx128 A

theorem cfAdvantage_eq_prT {St Blk : Type} [SampleableType (CF St Blk)]
    (X : CF St Blk → ProbComp Bool) : cfAdvantage X = prT ($ᵗ (CF St Blk) >>= X) := by
  rw [prT_eq]
  rfl

theorem ITSRExperiment_congr {K X Y Index : Type} {iK iK' : DecidableEq K}
    {iX iX' : DecidableEq X} {iI iI' : DecidableEq Index} {prob prob' : ITSRProblem K X Y Index}
    (h : prob = prob') (m : OracleComp (unifSpec + ITSRTargetSpec X K) (K × X)) :
    @ITSRExperiment K X Y Index iK iX iI prob ⟨m⟩ =
      @ITSRExperiment K X Y Index iK' iX' iI' prob' ⟨m⟩ := by
  subst h
  obtain rfl := Subsingleton.elim iK iK'
  obtain rfl := Subsingleton.elim iX iX'
  obtain rfl := Subsingleton.elim iI iI'
  rfl

theorem itsrI_eq (A : ItsrAdv128) :
    itsrI A = prT ($ᵗ (CF St Blk) >>= fun g =>
      @ITSRExperiment (Bytes 16) X128 (Bytes 30) (Adrs × ℕ) _ _ _ _
        (ItsrAdvI.inst A (@probI St Blk (Bytes 16) X128 (Bytes 30) (Adrs × ℕ) sampY128
          IV128 ibH obH dig30 idx128 g) g)) := by
  rw [← cfAdvantage_eq_prT]
  refine congrArg cfAdvantage (funext fun g => ?_)
  exact ITSRExperiment_congr (itsrProblem_eq_probI g) _

private theorem card_St_inv'' : (Fintype.card St : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  rw [card_St, Nat.cast_pow, Nat.cast_ofNat]

/-- **ITSR of `H_msg` at SLH-DSA-SHA2-128s in the ideal-compression model.**  `Q` bounds the
compression calls of the whole experiment `itsrProg128 A`: the adversary's own and those of the
final check (which hashes the targets and the candidate).  The advantage is at most the
probability bound `reuseSum 63 12 14 Q` of VCVio's coverage model for a tuple of `Q` independent
uniform digests (some coordinate has all its `k = 14` FORS indices covered, at its hypertree
leaf, by other coordinates), plus `Q² / 2^256`. -/
theorem itsr_bound_128s (A : ItsrAdv128) (Q : ℕ)
    (hQ : IsQueryBoundP (itsrProg128 A) (fun i => i.isRight = true) Q) :
    itsrI A ≤ reuseSum 63 12 14 Q + ((Q ^ 2 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  rw [itsrI_eq, ← card_St_inv'']
  refine (@itsr_le St Blk (Bytes 16) X128 (Bytes 30) (Adrs × ℕ) _ _ _ _ _ _ _ sampY128 _ _ _
    IV128 ibH obH dig30 idx128 ibH_injective obH_inj obH_ne_nil prEvent_dig30 A Q hQ).trans
    (add_le_add ?_ le_rfl)
  exact prT_tape_cov_le Link.vp Q

/-- `itsr_bound_128s` with VCVio's closed form `targetCoverBound`
(`∑ r ≤ k, C(Q, r) · #{surjections Fin k → Fin r} · 2^(-h r) · 2^(-a k)`). -/
theorem itsr_bound_128s_closed (A : ItsrAdv128) (Q : ℕ)
    (hQ : IsQueryBoundP (itsrProg128 A) (fun i => i.isRight = true) Q) :
    itsrI A ≤ Q * targetCoverBound 63 12 14 Q + ((Q ^ 2 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 256)⁻¹ :=
  (itsr_bound_128s A Q hQ).trans (add_le_add (reuseSum_le 63 12 14 Q) le_rfl)

end Ideal

#print axioms Ideal.tapeCoveredReuse_of_covP
#print axioms Ideal.prT_tape_cov_le
#print axioms Ideal.itsrProblem_eq_probI
#print axioms Ideal.itsrI_eq
#print axioms Ideal.itsr_bound_128s
#print axioms Ideal.itsr_bound_128s_closed
