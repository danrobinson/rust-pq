import Ideal.Realize.Final
import Ideal.Realize.PureReduce

/-!
# Ideal-model forgers against the external pure interface, and their internal counterparts

* `ForgerP`: an ideal-model forger against the byte-level **external pure** scheme
  `Reduction.pureBytesAlg` (FIPS 205 Alg. 21/22/24): given the public-key bytes, an oracle
  program with uniform sampling, compression-function queries and a signing oracle taking
  `(message, context)` pairs and answering `Option (List Byte)` (`none` for a context longer than
  255 bytes), returning a `(message, context)` pair and an `Option (List Byte)`.
* `sufP`, `eufP`: its SUF-CMA / EUF-CMA advantage for a uniformly random compression table (as
  `sufI`, `eufI` for internal forgers).
* `ForgerP.toI`: the internal ideal-model forger (`ForgerI`) that runs it once, forwards sampling
  and compression queries, answers a signing query `(M, ctx)` by `none` if `|ctx| > 255` (no
  query) and otherwise by `some` of one signing query `0x00 ‖ |ctx| ‖ ctx ‖ M`, and translates the
  output (`((M, ctx), some σ)` with `|ctx| ≤ 255` becomes `(0x00 ‖ |ctx| ‖ ctx ‖ M, σ)`, anything
  else `([], [])`).
* `sufP_le_sufI`, `eufP_le_eufI`: `sufP S ≤ sufI S.toI`, `eufP S ≤ eufI S.toI`.
* `toI_port`, `toI_sign`, `toI_long`, `toI_out`: the forger caps of `S.toI` — the same numbers
  of compression and signing queries as `S`, signed messages and output message at most `257`
  bytes longer than the message parts of `S`'s.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Ideal

open Ideal.Realize Ideal.Pure

set_option linter.unusedSectionVars false

/-- Interface of an external ideal-model forger: uniform bits, compression queries, signing
queries on `(message, context)` pairs. -/
abbrev PSpec := unifSpec + (hS St Blk + ((List Byte × List Byte) →ₒ Option (List Byte)))

/-- An ideal-model forger against the byte-level external pure scheme. -/
structure ForgerP where
  main : List Byte → OracleComp PSpec ((List Byte × List Byte) × Option (List Byte))

/-- A compression query of an external forger. -/
def isPortQP : PSpec.Domain → Bool
  | .inr (.inl _) => true
  | _ => false

/-- A signing query of an external forger. -/
def isSignQP : PSpec.Domain → Bool
  | .inr (.inr _) => true
  | _ => false

/-- A signing query of an external forger whose message part has more than `ℓ` bytes (the
context is not counted). -/
def isLongQP (ℓ : ℕ) : PSpec.Domain → Bool
  | .inr (.inr mc) => decide (ℓ < mc.1.length)
  | _ => false

section Forger

variable (S : ForgerP)
  (optRand : ∀ g : CF St Blk, PublicKeyCore (primsG (liftC g)).core → ProbComp (primsG (liftC g)).Y)
  (pkSeedDist : ProbComp (Bytes 16))

/-- The strong forger at the table `g`. -/
def ForgerP.sufInst (g : CF St Blk) :
    Reduction.PureBytesStrongForger Link.vp (primsG (liftC g)) (codecG g) (optRand g)
      pkSeedDist where
  main pk := simulateQ (instImpl g) (S.main pk)

/-- The (EUF) forger at the table `g`. -/
def ForgerP.eufInst (g : CF St Blk) :
    Reduction.PureBytesForger Link.vp (primsG (liftC g)) (codecG g) (optRand g) pkSeedDist where
  main pk := simulateQ (instImpl g) (S.main pk)

/-- **SUF-CMA advantage of an external forger in the ideal-compression model.** -/
noncomputable def sufP : ℝ≥0∞ :=
  cfAdvantage fun g => SignatureAlg.strongUnforgeableExperiment (S.sufInst optRand pkSeedDist g)

/-- **EUF-CMA advantage of an external forger in the ideal-compression model.** -/
noncomputable def eufP : ℝ≥0∞ :=
  cfAdvantage fun g => SignatureAlg.unforgeableExperiment (S.eufInst optRand pkSeedDist g)

theorem sufP_eq_cfAvg :
    sufP S optRand pkSeedDist = cfAvg fun g =>
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp
        (S.sufInst optRand pkSeedDist g) :=
  cfAdvantage_eq_cfAvg _

theorem eufP_eq_cfAvg :
    eufP S optRand pkSeedDist = cfAvg fun g =>
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp
        (S.eufInst optRand pkSeedDist g) :=
  cfAdvantage_eq_cfAvg _

end Forger

/-! ## The reduction to an internal forger -/

/-- How `toI` answers the external forger's queries. -/
def portImplP : QueryImpl PSpec (OracleComp (FSpecP (List Byte)))
  | .inl n => (FSpecP (List Byte)).query (.inl n)
  | .inr (.inl q) => (FSpecP (List Byte)).query (.inr (.inl q))
  | .inr (.inr e) => match Reduction.pureEncode e with
    | .error _ => pure none
    | .ok m => some <$> ((FSpecP (List Byte)).query (.inr (.inr m)) :
        OracleComp (FSpecP (List Byte)) (List Byte))

/-- **The internal ideal-model forger built from an external one.** -/
def ForgerP.toI (S : ForgerP) : ForgerI where
  main pk := OptGuard.readOut Reduction.pureEncode fallbackB <$> simulateQ portImplP (S.main pk)

theorem simulateQ_instImpl_portImplP (g : CF St Blk) {α : Type} (oa : OracleComp PSpec α) :
    simulateQ (instImpl g) (simulateQ portImplP oa) =
      simulateQ (OptGuard.signImpl (S := List Byte) Reduction.pureEncode)
        (simulateQ (instImpl g) oa) := by
  refine simulateQ_comm_of_step _ _ _ _ (fun t => ?_) oa
  rcases t with n | q | e
  · simp [portImplP, instImpl, OptGuard.signImpl]
  · simp [portImplP, instImpl]
  · cases he : Reduction.pureEncode e with
    | error x => simp [portImplP, instImpl, OptGuard.signImpl, he]
    | ok m => simp [portImplP, instImpl, OptGuard.signImpl, he]

section Forger

variable (S : ForgerP)
  (optRand : ∀ g : CF St Blk, PublicKeyCore (primsG (liftC g)).core → ProbComp (primsG (liftC g)).Y)
  (pkSeedDist : ProbComp (Bytes 16))

theorem toI_sufInst (g : CF St Blk) :
    S.toI.sufInst optRand pkSeedDist g =
      OptGuard.reduceS (alg := Reduction.bytesAlg Link.vp (primsG (liftC g)) (codecG g)
        (optRand g) pkSeedDist) Reduction.pureEncode fallbackB
        (S.sufInst optRand pkSeedDist g) := by
  simp only [ForgerI.sufInst, OptGuard.reduceS, ForgerP.sufInst, ForgerP.toI, simulateQ_map,
    simulateQ_instImpl_portImplP]

theorem toI_eufInst (g : CF St Blk) :
    S.toI.eufInst optRand pkSeedDist g =
      OptGuard.reduce (alg := Reduction.bytesAlg Link.vp (primsG (liftC g)) (codecG g)
        (optRand g) pkSeedDist) Reduction.pureEncode fallbackB
        (S.eufInst optRand pkSeedDist g) := by
  simp only [ForgerI.eufInst, OptGuard.reduce, ForgerP.eufInst, ForgerP.toI, simulateQ_map,
    simulateQ_instImpl_portImplP]

/-- **External SUF advantage ≤ internal SUF advantage of `toI`.** -/
theorem sufP_le_sufI : sufP S optRand pkSeedDist ≤ sufI S.toI optRand pkSeedDist := by
  rw [sufP_eq_cfAvg, sufI_eq_cfAvg]
  refine cfAvg_mono fun g => ?_
  rw [toI_sufInst]
  exact pure_bytes_strong_le_bytes _

/-- **External EUF advantage ≤ internal EUF advantage of `toI`.** -/
theorem eufP_le_eufI : eufP S optRand pkSeedDist ≤ eufI S.toI optRand pkSeedDist := by
  rw [eufP_eq_cfAvg, eufI_eq_cfAvg]
  refine cfAvg_mono fun g => ?_
  rw [toI_eufInst]
  exact pure_bytes_le_bytes _

end Forger

/-! ## The forger caps of `toI` -/

theorem length_of_pureEncode {e : List Byte × List Byte} {m : List Byte}
    (h : Reduction.pureEncode e = .ok m) : m.length = e.1.length + e.2.length + 2 ∧
      e.2.length ≤ 255 := by
  obtain ⟨hc, rfl⟩ := (Reduction.encodePureMessage_ok_iff _ _ _).1 h
  refine ⟨?_, hc⟩
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- Closes the per-step query-bound goals of the cap proofs. -/
local macro "qb" : tactic => `(tactic| first
  | exact isQueryBoundP_pure _ _ _
  | exact (isQueryBoundP_query_iff _ _ _).2 fun h' => by
      simp_all [isPortQ, isSignQ, isLongQ, isPortQP, isSignQP, isLongQP]
  | exact (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 fun h' => by
      simp_all [isPortQ, isSignQ, isLongQ, isPortQP, isSignQP, isLongQP]))

theorem toI_port (S : ForgerP) {qf : ℕ} (pk : List Byte)
    (h : IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf) :
    IsQueryBoundP (S.toI.main pk) (fun i => isPortQ (S := List Byte) i = true) qf := by
  simp only [ForgerP.toI, isQueryBoundP_map_iff]
  refine h.simulateQ_of_step (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | q | e
    · simp [isPortQP] at ht
    · simp only [portImplP]; qb
    · simp [isPortQP] at ht
  · rcases t with n | q | e
    · simp only [portImplP]; qb
    · simp [isPortQP] at ht
    · simp only [portImplP]
      cases Reduction.pureEncode e <;> (simp only; qb)

theorem toI_sign (S : ForgerP) {qs : ℕ} (pk : List Byte)
    (h : IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs) :
    IsQueryBoundP (S.toI.main pk) (fun i => isSignQ (S := List Byte) i = true) qs := by
  simp only [ForgerP.toI, isQueryBoundP_map_iff]
  refine h.simulateQ_of_step (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | q | e
    · simp [isSignQP] at ht
    · simp [isSignQP] at ht
    · simp only [portImplP]
      cases Reduction.pureEncode e <;> (simp only; qb)
  · rcases t with n | q | e
    · simp only [portImplP]; qb
    · simp only [portImplP]; qb
    · simp [isSignQP] at ht

theorem toI_long (S : ForgerP) {ℓ : ℕ} (pk : List Byte)
    (h : IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0) :
    IsQueryBoundP (S.toI.main pk) (fun i => isLongQ (S := List Byte) (ℓ + 257) i = true) 0 := by
  simp only [ForgerP.toI, isQueryBoundP_map_iff]
  refine h.simulateQ_of_step (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | q | e
    · simp [isLongQP] at ht
    · simp [isLongQP] at ht
    · simp only [portImplP]
      cases Reduction.pureEncode e <;> (simp only; qb)
  · rcases t with n | q | e
    · simp only [portImplP]; qb
    · simp only [portImplP]; qb
    · simp only [isLongQP, decide_eq_true_eq, not_lt] at ht
      simp only [portImplP]
      cases he : Reduction.pureEncode e with
      | error x => simp only; qb
      | ok m =>
        obtain ⟨hm, hc⟩ := length_of_pureEncode he
        simp only
        refine (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 fun h' => ?_)
        simp only [isLongQ, decide_eq_true_eq] at h'
        omega

theorem toI_out (S : ForgerP) {ℓ : ℕ} (pk : List Byte)
    (h : ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ) :
    ∀ z ∈ support (S.toI.main pk), z.1.length ≤ ℓ + 257 := by
  intro z hz
  simp only [ForgerP.toI, support_map, Set.mem_image] at hz
  obtain ⟨out, hout, rfl⟩ := hz
  have h1 := h out (support_simulateQ_subset portImplP (S.main pk) hout)
  obtain ⟨⟨M, ctx⟩, s⟩ := out
  simp only [OptGuard.readOut]
  cases he : Reduction.pureEncode (M, ctx) with
  | error x => simp [fallbackB]
  | ok m =>
    cases s with
    | none => simp [fallbackB]
    | some σ =>
      obtain ⟨hm, hc⟩ := length_of_pureEncode he
      simp only at hm hc h1 ⊢
      omega

end Ideal

#print axioms Ideal.sufP_le_sufI
#print axioms Ideal.eufP_le_eufI
#print axioms Ideal.toI_port
#print axioms Ideal.toI_sign
#print axioms Ideal.toI_long
#print axioms Ideal.toI_out
