import Integration.SlhDsaRandom

/-!
# A finite space of hash-function tuples and the uniform average of the linear headlines

NOT part of the default target; checked by `scripts/check-integration.sh`.

`RandFns p` is infinite (lists of unbounded length, addresses with unbounded fields).  Here:

* `Caps`: two length caps — `tl` for the list argument of `Thash`, `ml` for the message argument of
  `H_msg` and `PRF_msg`.
* `BList α L`: lists over `α` of length `≤ L` (as `Σ k : Fin (L+1), Fin k → α`), a finite type.
* `FinFns p c`: the four hash components on the bounded domain; `PRF` takes the 22-byte
  COMPRESSED address (`sha2AdrsKey`), so its domain is finite without any cap.  `FinFns p c` is a
  finite type (`Fintype`), i.e. the uniform distribution on it is "four independent uniformly
  random functions on the bounded domains".
* `FinFns.toRand ω : RandFns p`: the extension by the default value outside the bounded domain
  (`PRF` is precomposed with `sha2AdrsKey`).
* `RandFns.AgreeOn c f g`: `f` and `g` agree on all inputs within the caps; `toRand_restrict`:
  every `f` whose `PRF` factors through the compressed address agrees within the caps with the
  extension of its restriction.
* `…_uniform`: the linear headlines averaged UNIFORMLY over `FinFns Link.vp.params c`, for every
  choice of caps `c` — unconditional (they are instances of `…_random_avg`).

## What the caps mean (side condition for reading `toRand ω` as a random oracle)

The theorems below hold for every `c` with the hash functions `toRand ω`, which are uniformly
random on the bounded domain and CONSTANT (default) outside.  They express security for random
oracles exactly when the experiment never evaluates a hash outside the bounded domain.  From the
code of the scheme this is the case when:

* `c.tl ≥` the largest `Thash` arity of the parameter set: `max(len, k, 2)` (`T_len` for WOTS
  public keys, `T_k` for the FORS root, `H`, `F`) — `35` for SLH-DSA-SHA2-128s; and
* `c.ml ≥` the length of every message on which `H_msg`/`PRF_msg` is evaluated: the messages `M'`
  of the forger's signing queries and of its forgery.  For the internal interface `M' = M`; for
  the external pure interface `M' = 0 ‖ |ctx| ‖ ctx ‖ M`, i.e. `|M| + |ctx| + 2 ≤ c.ml`
  (`|ctx| ≤ 255`).  So the forger must be restricted to signing queries and a forgery with
  messages of length `≤ c.ml` (minus `257` for the pure interface).
* `PRF` is only evaluated at canonical addresses, on which `sha2AdrsKey` is injective
  (`Concrete.keyInjective_sha2Primitives`), so precomposition with it loses nothing.

This side condition is NOT formalised as a theorem here (the predicate `RandFns.AgreeOn` is the
notion of "agree on the bounded domain" with which it would be stated: "the experiment for `f`
and for `g` coincide whenever `AgreeOn c f g`").
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive

namespace Reduction

/-- Length caps: `tl` for the list argument of `Thash`, `ml` for messages. -/
structure Caps where
  tl : ℕ
  ml : ℕ

/-- Lists of length at most `L`. -/
abbrev BList (α : Type) (L : ℕ) : Type := Σ k : Fin (L + 1), (Fin k → α)

/-- A list of length `≤ L` as a bounded list. -/
def BList.ofList {α : Type} {L : ℕ} (xs : List α) (h : xs.length ≤ L) : BList α L :=
  ⟨⟨xs.length, Nat.lt_succ_of_le h⟩, xs.get⟩

/-- The hash components on the bounded domain. -/
structure FinFns (p : Params) (c : Caps) where
  thash : Bytes p.n → Bytes 22 → BList (Bytes p.n) c.tl → Bytes p.n
  hmsg : Bytes p.n → Bytes p.n → Bytes p.n → BList Byte c.ml → Bytes p.m
  prf : Bytes p.n → Bytes p.n → Bytes 22 → Bytes p.n
  prfMsg : Bytes p.n → Bytes p.n → BList Byte c.ml → Bytes p.n

/-- `FinFns` as a product of four function spaces. -/
def FinFns.equivProd (p : Params) (c : Caps) :
    FinFns p c ≃
      (Bytes p.n → Bytes 22 → BList (Bytes p.n) c.tl → Bytes p.n) ×
      (Bytes p.n → Bytes p.n → Bytes p.n → BList Byte c.ml → Bytes p.m) ×
      (Bytes p.n → Bytes p.n → Bytes 22 → Bytes p.n) ×
      (Bytes p.n → Bytes p.n → BList Byte c.ml → Bytes p.n) where
  toFun f := (f.thash, f.hmsg, f.prf, f.prfMsg)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

open Classical in
/-- The bounded function space is finite. -/
noncomputable instance (p : Params) (c : Caps) : Fintype (FinFns p c) :=
  haveI : Fintype (BList (Bytes p.n) c.tl) := inferInstance
  haveI : Fintype (BList Byte c.ml) := inferInstance
  haveI h1 : Fintype (Bytes p.n → Bytes 22 → BList (Bytes p.n) c.tl → Bytes p.n) := inferInstance
  haveI h2a : Fintype (Bytes p.n → BList Byte c.ml → Bytes p.m) := inferInstance
  haveI h2 : Fintype (Bytes p.n → Bytes p.n → Bytes p.n → BList Byte c.ml → Bytes p.m) :=
    inferInstance
  haveI h3 : Fintype (Bytes p.n → Bytes p.n → Bytes 22 → Bytes p.n) := inferInstance
  haveI h4 : Fintype (Bytes p.n → Bytes p.n → BList Byte c.ml → Bytes p.n) := inferInstance
  Fintype.ofEquiv _ (FinFns.equivProd p c).symm

instance (p : Params) (c : Caps) : Nonempty (FinFns p c) :=
  ⟨⟨fun _ _ _ => default, fun _ _ _ _ => default, fun _ _ _ => default, fun _ _ _ => default⟩⟩

/-- Extension to all inputs: the default value outside the caps; `PRF` through the compressed
address. -/
def FinFns.toRand {p : Params} {c : Caps} (ω : FinFns p c) : RandFns p where
  thash pk a xs := if h : xs.length ≤ c.tl then ω.thash pk a (BList.ofList xs h) else default
  hmsg r pk root m := if h : m.length ≤ c.ml then ω.hmsg r pk root (BList.ofList m h) else default
  prf pk sk a := ω.prf pk sk (Concrete.sha2AdrsKey a)
  prfMsg sk r m := if h : m.length ≤ c.ml then ω.prfMsg sk r (BList.ofList m h) else default

/-- Agreement of two function tuples on the bounded domain. -/
structure RandFns.AgreeOn {p : Params} (c : Caps) (f g : RandFns p) : Prop where
  thash : ∀ pk a xs, xs.length ≤ c.tl → f.thash pk a xs = g.thash pk a xs
  hmsg : ∀ r pk root m, m.length ≤ c.ml → f.hmsg r pk root m = g.hmsg r pk root m
  prf : ∀ pk sk a, f.prf pk sk a = g.prf pk sk a
  prfMsg : ∀ sk r m, m.length ≤ c.ml → f.prfMsg sk r m = g.prfMsg sk r m

/-- Restriction of a function tuple whose `PRF` is `prfK ∘ sha2AdrsKey`. -/
def RandFns.restrict {p : Params} (c : Caps) (f : RandFns p)
    (prfK : Bytes p.n → Bytes p.n → Bytes 22 → Bytes p.n) : FinFns p c where
  thash pk a xs := f.thash pk a (List.ofFn xs.2)
  hmsg r pk root m := f.hmsg r pk root (List.ofFn m.2)
  prf := prfK
  prfMsg sk r m := f.prfMsg sk r (List.ofFn m.2)

lemma BList.ofFn_ofList {α : Type} {L : ℕ} (xs : List α) (h : xs.length ≤ L) :
    List.ofFn (BList.ofList (L := L) xs h).2 = xs := List.ofFn_get xs

/-- Every tuple whose `PRF` factors through the compressed address agrees, within the caps, with
the extension of its restriction. -/
theorem toRand_restrict {p : Params} (c : Caps) (f : RandFns p)
    (prfK : Bytes p.n → Bytes p.n → Bytes 22 → Bytes p.n)
    (hK : ∀ pk sk a, f.prf pk sk a = prfK pk sk (Concrete.sha2AdrsKey a)) :
    RandFns.AgreeOn c f (f.restrict c prfK).toRand where
  thash pk a xs h := by
    simp only [FinFns.toRand, dite_true, h, RandFns.restrict, BList.ofFn_ofList]
  hmsg r pk root m h := by
    simp only [FinFns.toRand, dite_true, h, RandFns.restrict, BList.ofFn_ofList]
  prf pk sk a := hK pk sk a
  prfMsg sk r m h := by
    simp only [FinFns.toRand, dite_true, h, RandFns.restrict, BList.ofFn_ofList]

/-- The uniform weight on a finite type. -/
noncomputable def unifW (Ω : Type) [Fintype Ω] : Ω → ℝ≥0∞ := fun _ ↦ (Fintype.card Ω : ℝ≥0∞)⁻¹

lemma sum_unifW (Ω : Type) [Fintype Ω] [Nonempty Ω] : ∑ ω, unifW Ω ω = 1 := by
  simp only [unifW, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by simp) (by simp)

variable {W : Type} [Fintype W]

/-- The hash functions of SLH-DSA-SHA2-128s with caps `c`: the finite space. -/
abbrev Ω128 (c : Caps) : Type := FinFns Link.vp.params c

/-- The primitives in world `ω`. -/
abbrev primsΩ {c : Caps} (ω : Ω128 c) : Primitives Link.vp.params := randPrims ω.toRand

section
variable (c : Caps)
  (optRand : ∀ ω : Ω128 c, PublicKeyCore (primsΩ ω).core → ProbComp (primsΩ ω).Y)
  (pkSeedDist : ∀ ω : Ω128 c, ProbComp (primsΩ ω).PkSeed)

/-- **Uniformly averaged EUF-CMA linear headline (internal, typed).** -/
theorem slhdsa_sha2_128s_euf_cma_linear_quantum_uniform
    (Q : ∀ ω, QForger W (internalAlg Link.vp (primsΩ ω) (optRand ω) (pkSeedDist ω))) :
    ∑ ω, unifW (Ω128 c) ω * qUnforgeableAdvantage (Q ω) + ∑ ω, unifW (Ω128 c) ω * qLinIdealEuf (Q ω) ≤
      ∑ ω, unifW (Ω128 c) ω * qLinRealEuf (Q ω) :=
  slhdsa_sha2_128s_euf_cma_linear_quantum_random_avg _ FinFns.toRand optRand pkSeedDist Q

/-- **Uniformly averaged SUF-CMA linear headline (internal, typed).** -/
theorem slhdsa_sha2_128s_suf_cma_linear_quantum_uniform
    (Q : ∀ ω, QForger W (internalAlg Link.vp (primsΩ ω) (optRand ω) (pkSeedDist ω))) :
    ∑ ω, unifW (Ω128 c) ω * qStrongUnforgeableAdvantage (Q ω) + ∑ ω, unifW (Ω128 c) ω * qLinIdealSuf (Q ω) ≤
      ∑ ω, unifW (Ω128 c) ω * qLinRealSuf (Q ω) :=
  slhdsa_sha2_128s_suf_cma_linear_quantum_random_avg _ FinFns.toRand optRand pkSeedDist Q

/-- **Uniformly averaged EUF-CMA linear headline (external pure, typed).** -/
theorem slhdsa_sha2_128s_pure_euf_cma_linear_quantum_uniform
    (Q : ∀ ω, QForger W (externalAlg Link.vp (primsΩ ω) (optRand ω) (pkSeedDist ω))) :
    ∑ ω, unifW (Ω128 c) ω * qUnforgeableAdvantage (Q ω) +
        ∑ ω, unifW (Ω128 c) ω * qLinIdealEuf (qToInternal (Q ω)) ≤
      ∑ ω, unifW (Ω128 c) ω * qLinRealEuf (qToInternal (Q ω)) :=
  slhdsa_sha2_128s_pure_euf_cma_linear_quantum_random_avg _ FinFns.toRand optRand pkSeedDist Q

/-- **Uniformly averaged SUF-CMA linear headline (external pure, typed).** -/
theorem slhdsa_sha2_128s_pure_suf_cma_linear_quantum_uniform
    (Q : ∀ ω, QForger W (externalAlg Link.vp (primsΩ ω) (optRand ω) (pkSeedDist ω))) :
    ∑ ω, unifW (Ω128 c) ω * qStrongUnforgeableAdvantage (Q ω) +
        ∑ ω, unifW (Ω128 c) ω * qLinIdealSuf (qToInternal (Q ω)) ≤
      ∑ ω, unifW (Ω128 c) ω * qLinRealSuf (qToInternal (Q ω)) :=
  slhdsa_sha2_128s_pure_suf_cma_linear_quantum_random_avg _ FinFns.toRand optRand pkSeedDist Q

/-- **Uniformly averaged EUF-CMA linear headline (internal, byte strings).** -/
theorem slhdsa_sha2_128s_bytes_euf_cma_linear_quantum_uniform
    (Q : ∀ ω, QForger W (bytesAlg Link.vp (primsΩ ω) (codecR ω.toRand) (optRand ω) (pkSeedDist ω))) :
    ∑ ω, unifW (Ω128 c) ω * qUnforgeableAdvantage (Q ω) +
        ∑ ω, unifW (Ω128 c) ω * qLinIdealEuf (qBytesToTyped (Q ω)) ≤
      ∑ ω, unifW (Ω128 c) ω * qLinRealEuf (qBytesToTyped (Q ω)) :=
  slhdsa_sha2_128s_bytes_euf_cma_linear_quantum_random_avg _ FinFns.toRand optRand pkSeedDist Q

/-- **Uniformly averaged SUF-CMA linear headline (internal, byte strings).** -/
theorem slhdsa_sha2_128s_bytes_suf_cma_linear_quantum_uniform
    (Q : ∀ ω, QForger W (bytesAlg Link.vp (primsΩ ω) (codecR ω.toRand) (optRand ω) (pkSeedDist ω))) :
    ∑ ω, unifW (Ω128 c) ω * qStrongUnforgeableAdvantage (Q ω) +
        ∑ ω, unifW (Ω128 c) ω * qLinIdealSuf (qBytesToTyped (Q ω)) ≤
      ∑ ω, unifW (Ω128 c) ω * qLinRealSuf (qBytesToTyped (Q ω)) :=
  slhdsa_sha2_128s_bytes_suf_cma_linear_quantum_random_avg _ FinFns.toRand optRand pkSeedDist Q

/-- **Uniformly averaged EUF-CMA linear headline (external pure, byte strings).** -/
theorem slhdsa_sha2_128s_pure_bytes_euf_cma_linear_quantum_uniform
    (Q : ∀ ω, QForger W (pureBytesAlg Link.vp (primsΩ ω) (codecR ω.toRand) (optRand ω) (pkSeedDist ω))) :
    ∑ ω, unifW (Ω128 c) ω * qUnforgeableAdvantage (Q ω) +
        ∑ ω, unifW (Ω128 c) ω * qLinIdealEuf (qPureBytesToInternal (Q ω)) ≤
      ∑ ω, unifW (Ω128 c) ω * qLinRealEuf (qPureBytesToInternal (Q ω)) :=
  slhdsa_sha2_128s_pure_bytes_euf_cma_linear_quantum_random_avg _ FinFns.toRand optRand pkSeedDist Q

/-- **Uniformly averaged SUF-CMA linear headline (external pure, byte strings).** -/
theorem slhdsa_sha2_128s_pure_bytes_suf_cma_linear_quantum_uniform
    (Q : ∀ ω, QForger W (pureBytesAlg Link.vp (primsΩ ω) (codecR ω.toRand) (optRand ω) (pkSeedDist ω))) :
    ∑ ω, unifW (Ω128 c) ω * qStrongUnforgeableAdvantage (Q ω) +
        ∑ ω, unifW (Ω128 c) ω * qLinIdealSuf (qPureBytesToInternal (Q ω)) ≤
      ∑ ω, unifW (Ω128 c) ω * qLinRealSuf (qPureBytesToInternal (Q ω)) :=
  slhdsa_sha2_128s_pure_bytes_suf_cma_linear_quantum_random_avg _ FinFns.toRand optRand pkSeedDist Q

end

end Reduction

#print axioms Reduction.toRand_restrict
#print axioms Reduction.sum_unifW
#print axioms Reduction.slhdsa_sha2_128s_euf_cma_linear_quantum_uniform
#print axioms Reduction.slhdsa_sha2_128s_suf_cma_linear_quantum_uniform
#print axioms Reduction.slhdsa_sha2_128s_pure_euf_cma_linear_quantum_uniform
#print axioms Reduction.slhdsa_sha2_128s_pure_suf_cma_linear_quantum_uniform
#print axioms Reduction.slhdsa_sha2_128s_bytes_euf_cma_linear_quantum_uniform
#print axioms Reduction.slhdsa_sha2_128s_bytes_suf_cma_linear_quantum_uniform
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_euf_cma_linear_quantum_uniform
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_linear_quantum_uniform
