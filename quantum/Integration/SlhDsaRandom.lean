import Integration.SlhDsaAll128s

/-!
# SLH-DSA with its hash functions given by an arbitrary function tuple; the averaged headline

NOT part of the default target; checked by `scripts/check-integration.sh`.

Part-1 side of the QROM composition.

* `RandFns p`: a choice of the four hash components of SLH-DSA with the carrier types and
  encodings of the SHA-2 instantiation (`n`-byte nodes, 22-byte compressed addresses): the
  tweakable hash `Thash` (`F`, `H`, `T_ℓ` are its arities), `H_msg`, `PRF`, `PRF_msg`.  The four
  fields are independent components: a (random) element of `RandFns p` is four independent
  (random) functions, i.e. one function on the disjoint union of the four domains.
* `randPrims f : Primitives p`: the primitive bundle with these functions and the non-cryptographic
  encodings of `sha2Primitives p` (`adrsToKey = sha2AdrsKey`, `yToBytes = id`).
* `structural_randPrims`: `Structural vp (randPrims f)` for EVERY `f` (the structural hypothesis
  concerns the encodings only).
* `…_random`: the unconditional linear quantum headlines at `randPrims f`, for every `f`.
* `…_random_avg`: the AVERAGED linear headlines: for any finite index set `Ω`, weights `w`, family
  `fn : Ω → RandFns p`, and any family of quantum forgers `Q ω` (one machine per `ω`, arbitrary
  dependence on `ω`: in particular machines applying the unitary of `fn ω` as an instrument),
  `∑ w·qAdv + ∑ w·(ideal side) ≤ ∑ w·(real side)`.

The function space `RandFns p` is infinite (`Thash`, `H_msg`, `PRF_msg` take lists of unbounded
length), so there is no uniform distribution on it; the averaged theorems are therefore stated for
an arbitrary finite family with arbitrary weights (`Ω`, `w`, `fn`), which covers the uniform
distribution on any finite set of function tuples — e.g. all functions on inputs of bounded
length, extended by a fixed value.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive

namespace Reduction

/-- The four hash components of SLH-DSA over the SHA-2 carrier types. -/
structure RandFns (p : Params) where
  /-- the tweakable hash collection (`F`, `H`, `T_ℓ`) -/
  thash : Bytes p.n → Bytes 22 → List (Bytes p.n) → Bytes p.n
  /-- `H_msg(R, PK.seed, PK.root, M)` -/
  hmsg : Bytes p.n → Bytes p.n → Bytes p.n → List Byte → Bytes p.m
  /-- `PRF(PK.seed, SK.seed, ADRS)` -/
  prf : Bytes p.n → Bytes p.n → Adrs → Bytes p.n
  /-- `PRF_msg(SK.prf, opt_rand, M)` -/
  prfMsg : Bytes p.n → Bytes p.n → List Byte → Bytes p.n

/-- The primitive bundle whose hash components are `f`, with the carrier types and encodings of
`sha2Primitives p`. -/
@[reducible] def randPrims {p : Params} (f : RandFns p) : Primitives p where
  PkSeed := Bytes p.n
  SkSeed := Bytes p.n
  SkPrf := Bytes p.n
  Y := Bytes p.n
  AdrsKey := Bytes 22
  adrsToKey := Concrete.sha2AdrsKey
  Thash := f.thash
  PRF := f.prf
  PRFmsg := f.prfMsg
  Hmsg := f.hmsg
  yToBytes := id

/-- **The structural hypothesis holds for every choice of the hash functions.** -/
theorem structural_randPrims (vp : ValidatedParams) (hb : ApprovedAddressBounds vp.params)
    (f : RandFns vp.params) : Structural vp (randPrims f) :=
  ⟨⟨fun _ _ h => h⟩, Concrete.keyInjective_sha2Primitives vp hb, hb.toCanonicalAddressBounds⟩

theorem structural_randPrims_128s (f : RandFns Link.vp.params) :
    Structural Link.vp (randPrims f) :=
  structural_randPrims Link.vp (fipsApprovedAddressBounds Link.S128) f

/-- The wire codec of SLH-DSA-SHA2-128s for the bundle `randPrims f` (the codec only involves
the carrier types and `yToBytes`, which are those of `Link.prims`). -/
abbrev codecR (f : RandFns Link.vp.params) : CoreWireCodec Link.vp.params (randPrims f).core :=
  ⟨codec128s.pkSeed, codec128s.skSeed, codec128s.skPrf, codec128s.y, codec128s.y_toBytes⟩

/-- Averaging a pointwise linear inequality with arbitrary weights. -/
theorem avg_of_pointwise {Ω : Type} [Fintype Ω] (w a i r : Ω → ℝ≥0∞)
    (h : ∀ ω, a ω + i ω ≤ r ω) :
    ∑ ω, w ω * a ω + ∑ ω, w ω * i ω ≤ ∑ ω, w ω * r ω := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ω _ ↦ ?_
  rw [← mul_add]
  gcongr
  exact h ω

variable {W : Type} [Fintype W]

/-! ## The linear headlines at `randPrims f`, for every `f`, and their averages

`Ω` is any finite index set, `w` any weights, `fn ω` the hash functions of world `ω`; the scheme
parameters `optRand`, `pkSeedDist` and the quantum forger `Q ω` may depend on `ω` arbitrarily. -/

/-- EUF-CMA (internal algorithms, typed), linear form, hash functions `f`: for every `f` and every
quantum forger. -/
theorem slhdsa_sha2_128s_euf_cma_linear_quantum_random (f : RandFns Link.vp.params)
    (optRand : PublicKeyCore (randPrims f).core → ProbComp (randPrims f).Y)
    (pkSeedDist : ProbComp (randPrims f).PkSeed)
    (Q : QForger W (internalAlg Link.vp (randPrims f) optRand pkSeedDist)) :
    qUnforgeableAdvantage Q + qLinIdealEuf Q ≤ qLinRealEuf Q :=
  slhdsa_euf_cma_final_linear_quantum_all (structural_randPrims_128s f) Q

/-- **Averaged EUF-CMA linear headline (internal algorithms, typed)**: average over the hash functions,
one quantum forger per function tuple. -/
theorem slhdsa_sha2_128s_euf_cma_linear_quantum_random_avg {Ω : Type} [Fintype Ω] (w : Ω → ℝ≥0∞)
    (fn : Ω → RandFns Link.vp.params)
    (optRand : ∀ ω, PublicKeyCore (randPrims (fn ω)).core → ProbComp (randPrims (fn ω)).Y)
    (pkSeedDist : ∀ ω, ProbComp (randPrims (fn ω)).PkSeed)
    (Q : ∀ ω, QForger W (internalAlg Link.vp (randPrims (fn ω)) (optRand ω) (pkSeedDist ω))) :
    ∑ ω, w ω * qUnforgeableAdvantage (Q ω) + ∑ ω, w ω * qLinIdealEuf (Q ω) ≤
      ∑ ω, w ω * qLinRealEuf (Q ω) :=
  avg_of_pointwise w _ _ _ fun ω ↦
    slhdsa_sha2_128s_euf_cma_linear_quantum_random (fn ω) (optRand ω) (pkSeedDist ω) (Q ω)

/-- SUF-CMA (internal algorithms, typed), linear form, hash functions `f`: for every `f` and every
quantum forger. -/
theorem slhdsa_sha2_128s_suf_cma_linear_quantum_random (f : RandFns Link.vp.params)
    (optRand : PublicKeyCore (randPrims f).core → ProbComp (randPrims f).Y)
    (pkSeedDist : ProbComp (randPrims f).PkSeed)
    (Q : QForger W (internalAlg Link.vp (randPrims f) optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q + qLinIdealSuf Q ≤ qLinRealSuf Q :=
  slhdsa_suf_cma_final_linear_quantum_all (structural_randPrims_128s f) Q

/-- **Averaged SUF-CMA linear headline (internal algorithms, typed)**: average over the hash functions,
one quantum forger per function tuple. -/
theorem slhdsa_sha2_128s_suf_cma_linear_quantum_random_avg {Ω : Type} [Fintype Ω] (w : Ω → ℝ≥0∞)
    (fn : Ω → RandFns Link.vp.params)
    (optRand : ∀ ω, PublicKeyCore (randPrims (fn ω)).core → ProbComp (randPrims (fn ω)).Y)
    (pkSeedDist : ∀ ω, ProbComp (randPrims (fn ω)).PkSeed)
    (Q : ∀ ω, QForger W (internalAlg Link.vp (randPrims (fn ω)) (optRand ω) (pkSeedDist ω))) :
    ∑ ω, w ω * qStrongUnforgeableAdvantage (Q ω) + ∑ ω, w ω * qLinIdealSuf (Q ω) ≤
      ∑ ω, w ω * qLinRealSuf (Q ω) :=
  avg_of_pointwise w _ _ _ fun ω ↦
    slhdsa_sha2_128s_suf_cma_linear_quantum_random (fn ω) (optRand ω) (pkSeedDist ω) (Q ω)

/-- EUF-CMA (external pure interface, typed), linear form, hash functions `f`: for every `f` and every
quantum forger. -/
theorem slhdsa_sha2_128s_pure_euf_cma_linear_quantum_random (f : RandFns Link.vp.params)
    (optRand : PublicKeyCore (randPrims f).core → ProbComp (randPrims f).Y)
    (pkSeedDist : ProbComp (randPrims f).PkSeed)
    (Q : QForger W (externalAlg Link.vp (randPrims f) optRand pkSeedDist)) :
    qUnforgeableAdvantage Q + qLinIdealEuf (qToInternal Q) ≤ qLinRealEuf (qToInternal Q) :=
  slhdsa_pure_euf_cma_final_linear_quantum_all (structural_randPrims_128s f) Q

/-- **Averaged EUF-CMA linear headline (external pure interface, typed)**: average over the hash functions,
one quantum forger per function tuple. -/
theorem slhdsa_sha2_128s_pure_euf_cma_linear_quantum_random_avg {Ω : Type} [Fintype Ω] (w : Ω → ℝ≥0∞)
    (fn : Ω → RandFns Link.vp.params)
    (optRand : ∀ ω, PublicKeyCore (randPrims (fn ω)).core → ProbComp (randPrims (fn ω)).Y)
    (pkSeedDist : ∀ ω, ProbComp (randPrims (fn ω)).PkSeed)
    (Q : ∀ ω, QForger W (externalAlg Link.vp (randPrims (fn ω)) (optRand ω) (pkSeedDist ω))) :
    ∑ ω, w ω * qUnforgeableAdvantage (Q ω) + ∑ ω, w ω * qLinIdealEuf (qToInternal (Q ω)) ≤
      ∑ ω, w ω * qLinRealEuf (qToInternal (Q ω)) :=
  avg_of_pointwise w _ _ _ fun ω ↦
    slhdsa_sha2_128s_pure_euf_cma_linear_quantum_random (fn ω) (optRand ω) (pkSeedDist ω) (Q ω)

/-- SUF-CMA (external pure interface, typed), linear form, hash functions `f`: for every `f` and every
quantum forger. -/
theorem slhdsa_sha2_128s_pure_suf_cma_linear_quantum_random (f : RandFns Link.vp.params)
    (optRand : PublicKeyCore (randPrims f).core → ProbComp (randPrims f).Y)
    (pkSeedDist : ProbComp (randPrims f).PkSeed)
    (Q : QForger W (externalAlg Link.vp (randPrims f) optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q + qLinIdealSuf (qToInternal Q) ≤ qLinRealSuf (qToInternal Q) :=
  slhdsa_pure_suf_cma_final_linear_quantum_all (structural_randPrims_128s f) Q

/-- **Averaged SUF-CMA linear headline (external pure interface, typed)**: average over the hash functions,
one quantum forger per function tuple. -/
theorem slhdsa_sha2_128s_pure_suf_cma_linear_quantum_random_avg {Ω : Type} [Fintype Ω] (w : Ω → ℝ≥0∞)
    (fn : Ω → RandFns Link.vp.params)
    (optRand : ∀ ω, PublicKeyCore (randPrims (fn ω)).core → ProbComp (randPrims (fn ω)).Y)
    (pkSeedDist : ∀ ω, ProbComp (randPrims (fn ω)).PkSeed)
    (Q : ∀ ω, QForger W (externalAlg Link.vp (randPrims (fn ω)) (optRand ω) (pkSeedDist ω))) :
    ∑ ω, w ω * qStrongUnforgeableAdvantage (Q ω) + ∑ ω, w ω * qLinIdealSuf (qToInternal (Q ω)) ≤
      ∑ ω, w ω * qLinRealSuf (qToInternal (Q ω)) :=
  avg_of_pointwise w _ _ _ fun ω ↦
    slhdsa_sha2_128s_pure_suf_cma_linear_quantum_random (fn ω) (optRand ω) (pkSeedDist ω) (Q ω)

/-- EUF-CMA (internal algorithms on byte strings), linear form, hash functions `f`: for every `f` and every
quantum forger. -/
theorem slhdsa_sha2_128s_bytes_euf_cma_linear_quantum_random (f : RandFns Link.vp.params)
    (optRand : PublicKeyCore (randPrims f).core → ProbComp (randPrims f).Y)
    (pkSeedDist : ProbComp (randPrims f).PkSeed)
    (Q : QForger W (bytesAlg Link.vp (randPrims f) (codecR f) optRand pkSeedDist)) :
    qUnforgeableAdvantage Q + qLinIdealEuf (qBytesToTyped Q) ≤ qLinRealEuf (qBytesToTyped Q) :=
  slhdsa_bytes_euf_cma_final_linear_quantum_all (structural_randPrims_128s f) Q

/-- **Averaged EUF-CMA linear headline (internal algorithms on byte strings)**: average over the hash functions,
one quantum forger per function tuple. -/
theorem slhdsa_sha2_128s_bytes_euf_cma_linear_quantum_random_avg {Ω : Type} [Fintype Ω] (w : Ω → ℝ≥0∞)
    (fn : Ω → RandFns Link.vp.params)
    (optRand : ∀ ω, PublicKeyCore (randPrims (fn ω)).core → ProbComp (randPrims (fn ω)).Y)
    (pkSeedDist : ∀ ω, ProbComp (randPrims (fn ω)).PkSeed)
    (Q : ∀ ω, QForger W (bytesAlg Link.vp (randPrims (fn ω)) (codecR (fn ω)) (optRand ω) (pkSeedDist ω))) :
    ∑ ω, w ω * qUnforgeableAdvantage (Q ω) + ∑ ω, w ω * qLinIdealEuf (qBytesToTyped (Q ω)) ≤
      ∑ ω, w ω * qLinRealEuf (qBytesToTyped (Q ω)) :=
  avg_of_pointwise w _ _ _ fun ω ↦
    slhdsa_sha2_128s_bytes_euf_cma_linear_quantum_random (fn ω) (optRand ω) (pkSeedDist ω) (Q ω)

/-- SUF-CMA (internal algorithms on byte strings), linear form, hash functions `f`: for every `f` and every
quantum forger. -/
theorem slhdsa_sha2_128s_bytes_suf_cma_linear_quantum_random (f : RandFns Link.vp.params)
    (optRand : PublicKeyCore (randPrims f).core → ProbComp (randPrims f).Y)
    (pkSeedDist : ProbComp (randPrims f).PkSeed)
    (Q : QForger W (bytesAlg Link.vp (randPrims f) (codecR f) optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q + qLinIdealSuf (qBytesToTyped Q) ≤ qLinRealSuf (qBytesToTyped Q) :=
  slhdsa_bytes_suf_cma_final_linear_quantum_all (structural_randPrims_128s f) Q

/-- **Averaged SUF-CMA linear headline (internal algorithms on byte strings)**: average over the hash functions,
one quantum forger per function tuple. -/
theorem slhdsa_sha2_128s_bytes_suf_cma_linear_quantum_random_avg {Ω : Type} [Fintype Ω] (w : Ω → ℝ≥0∞)
    (fn : Ω → RandFns Link.vp.params)
    (optRand : ∀ ω, PublicKeyCore (randPrims (fn ω)).core → ProbComp (randPrims (fn ω)).Y)
    (pkSeedDist : ∀ ω, ProbComp (randPrims (fn ω)).PkSeed)
    (Q : ∀ ω, QForger W (bytesAlg Link.vp (randPrims (fn ω)) (codecR (fn ω)) (optRand ω) (pkSeedDist ω))) :
    ∑ ω, w ω * qStrongUnforgeableAdvantage (Q ω) + ∑ ω, w ω * qLinIdealSuf (qBytesToTyped (Q ω)) ≤
      ∑ ω, w ω * qLinRealSuf (qBytesToTyped (Q ω)) :=
  avg_of_pointwise w _ _ _ fun ω ↦
    slhdsa_sha2_128s_bytes_suf_cma_linear_quantum_random (fn ω) (optRand ω) (pkSeedDist ω) (Q ω)

/-- EUF-CMA (external pure interface on byte strings), linear form, hash functions `f`: for every `f` and every
quantum forger. -/
theorem slhdsa_sha2_128s_pure_bytes_euf_cma_linear_quantum_random (f : RandFns Link.vp.params)
    (optRand : PublicKeyCore (randPrims f).core → ProbComp (randPrims f).Y)
    (pkSeedDist : ProbComp (randPrims f).PkSeed)
    (Q : QForger W (pureBytesAlg Link.vp (randPrims f) (codecR f) optRand pkSeedDist)) :
    qUnforgeableAdvantage Q + qLinIdealEuf (qPureBytesToInternal Q) ≤ qLinRealEuf (qPureBytesToInternal Q) :=
  slhdsa_pure_bytes_euf_cma_final_linear_quantum_all (structural_randPrims_128s f) Q

/-- **Averaged EUF-CMA linear headline (external pure interface on byte strings)**: average over the hash functions,
one quantum forger per function tuple. -/
theorem slhdsa_sha2_128s_pure_bytes_euf_cma_linear_quantum_random_avg {Ω : Type} [Fintype Ω] (w : Ω → ℝ≥0∞)
    (fn : Ω → RandFns Link.vp.params)
    (optRand : ∀ ω, PublicKeyCore (randPrims (fn ω)).core → ProbComp (randPrims (fn ω)).Y)
    (pkSeedDist : ∀ ω, ProbComp (randPrims (fn ω)).PkSeed)
    (Q : ∀ ω, QForger W (pureBytesAlg Link.vp (randPrims (fn ω)) (codecR (fn ω)) (optRand ω) (pkSeedDist ω))) :
    ∑ ω, w ω * qUnforgeableAdvantage (Q ω) + ∑ ω, w ω * qLinIdealEuf (qPureBytesToInternal (Q ω)) ≤
      ∑ ω, w ω * qLinRealEuf (qPureBytesToInternal (Q ω)) :=
  avg_of_pointwise w _ _ _ fun ω ↦
    slhdsa_sha2_128s_pure_bytes_euf_cma_linear_quantum_random (fn ω) (optRand ω) (pkSeedDist ω) (Q ω)

/-- SUF-CMA (external pure interface on byte strings), linear form, hash functions `f`: for every `f` and every
quantum forger. -/
theorem slhdsa_sha2_128s_pure_bytes_suf_cma_linear_quantum_random (f : RandFns Link.vp.params)
    (optRand : PublicKeyCore (randPrims f).core → ProbComp (randPrims f).Y)
    (pkSeedDist : ProbComp (randPrims f).PkSeed)
    (Q : QForger W (pureBytesAlg Link.vp (randPrims f) (codecR f) optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q + qLinIdealSuf (qPureBytesToInternal Q) ≤ qLinRealSuf (qPureBytesToInternal Q) :=
  slhdsa_pure_bytes_suf_cma_final_linear_quantum_all (structural_randPrims_128s f) Q

/-- **Averaged SUF-CMA linear headline (external pure interface on byte strings)**: average over the hash functions,
one quantum forger per function tuple. -/
theorem slhdsa_sha2_128s_pure_bytes_suf_cma_linear_quantum_random_avg {Ω : Type} [Fintype Ω] (w : Ω → ℝ≥0∞)
    (fn : Ω → RandFns Link.vp.params)
    (optRand : ∀ ω, PublicKeyCore (randPrims (fn ω)).core → ProbComp (randPrims (fn ω)).Y)
    (pkSeedDist : ∀ ω, ProbComp (randPrims (fn ω)).PkSeed)
    (Q : ∀ ω, QForger W (pureBytesAlg Link.vp (randPrims (fn ω)) (codecR (fn ω)) (optRand ω) (pkSeedDist ω))) :
    ∑ ω, w ω * qStrongUnforgeableAdvantage (Q ω) + ∑ ω, w ω * qLinIdealSuf (qPureBytesToInternal (Q ω)) ≤
      ∑ ω, w ω * qLinRealSuf (qPureBytesToInternal (Q ω)) :=
  avg_of_pointwise w _ _ _ fun ω ↦
    slhdsa_sha2_128s_pure_bytes_suf_cma_linear_quantum_random (fn ω) (optRand ω) (pkSeedDist ω) (Q ω)

end Reduction

#print axioms Reduction.structural_randPrims
#print axioms Reduction.slhdsa_sha2_128s_euf_cma_linear_quantum_random
#print axioms Reduction.slhdsa_sha2_128s_euf_cma_linear_quantum_random_avg
#print axioms Reduction.slhdsa_sha2_128s_suf_cma_linear_quantum_random
#print axioms Reduction.slhdsa_sha2_128s_suf_cma_linear_quantum_random_avg
#print axioms Reduction.slhdsa_sha2_128s_pure_euf_cma_linear_quantum_random
#print axioms Reduction.slhdsa_sha2_128s_pure_euf_cma_linear_quantum_random_avg
#print axioms Reduction.slhdsa_sha2_128s_pure_suf_cma_linear_quantum_random
#print axioms Reduction.slhdsa_sha2_128s_pure_suf_cma_linear_quantum_random_avg
#print axioms Reduction.slhdsa_sha2_128s_bytes_euf_cma_linear_quantum_random
#print axioms Reduction.slhdsa_sha2_128s_bytes_euf_cma_linear_quantum_random_avg
#print axioms Reduction.slhdsa_sha2_128s_bytes_suf_cma_linear_quantum_random
#print axioms Reduction.slhdsa_sha2_128s_bytes_suf_cma_linear_quantum_random_avg
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_euf_cma_linear_quantum_random
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_euf_cma_linear_quantum_random_avg
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_linear_quantum_random
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_linear_quantum_random_avg
