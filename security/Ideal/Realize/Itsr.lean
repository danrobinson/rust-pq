import Ideal.Realize.ItsrBound
import Reduction.Instance128sV2

/-!
# The twelfth realiser: `RealizesItsrF` for the Reduction's ITSR adversary

For every ideal-model forger `S : ForgerI`, every table-independent `opt_rand` family
`optRandU oR` and every public-seed distribution `d`:

* `realizesItsrS S oR d hqf hqs hlong hout :
    RealizesItsrF (fun g => Lazy.bItsrL (S.typedS (optRandU oR) d g))
      qf (2 * qs) qf (itsrQc qs) (itsrLc ℓ) qs ℓ`
  and the EUF twin `realizesItsrE` (`S.typedE`), with the ONE program `itsrA S oR d`
  (`Ideal/Realize/ItsrReal.lean`);
* the parameters are closed-form functions of the forger's caps `qf` (compression queries), `qs`
  (signing queries), `ℓ` (message bytes):
  - `qP = qf`, `q = qf`: the raw compression queries are exactly the forger's own;
  - `cP = 2·qs`: chain queries with second block `cB` are only the two chains of the `qs`
    `H_msg` evaluations of the signing oracle (every `Thash` chain has a second block other than
    `cB`: `thBlocks_secondP`);
  - `qc = itsrQc qs = keygenHashes + qs·signHashes + qs` (`= 269824 + qs·2007386` at 128s,
    `itsrQc_eq`): one chain per `Thash` query, two per `H_msg` query (counts of
    `Reduction.Open.itsrOpen_hashes`);
  - `Lc = itsrLc ℓ = max (thashCost thMax) ((ℓ + 56)/64 + 1)` (`= max 11 ((ℓ + 56)/64 + 1)`,
    `itsrLc_eq`);
* closed corollaries `itsrSufI_le_optRandU`, `itsrEufI_le_optRandU` (via `itsrSufI_le_fine`,
  `itsrEufI_le_fine`), and the realisers at the parameters of the closed theorems of
  `Ideal/ComposeFinal.lean` (`realizesItsrS_2_60_2_20`, …), via `raiseItsr`.

Hypotheses: only the four query bounds on the forger (`hqf`, `hqs`, `hlong`, `hout`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security KeyedHash ENNReal

namespace Ideal.Realize.Itsr

open Reduction Reduction.Lazy Ideal.Realize Ideal.Itsr

/-- The number of chain queries of the realiser: one per `Thash` query and two per `H_msg`
query of the open ITSR program (`keygenHashes + qs·signHashes` hash queries, at most `qs` of them
`H_msg`). -/
def itsrQc (qs : ℕ) : ℕ := Lazy.keygenHashes Link.vp + qs * Lazy.signHashes Link.vp + qs

theorem itsrQc_eq (qs : ℕ) : itsrQc qs = 269824 + qs * 2007386 := by
  unfold itsrQc
  rw [keygenHashes_128s, signHashes_128s]
  ring

theorem thashCost_thMax : thashCost thMax = 11 := by decide

theorem itsrLc_eq (ℓ : ℕ) : itsrLc ℓ = max 11 ((ℓ + 56) / 64 + 1) := by
  rw [itsrLc, thashCost_thMax]

section Realiser

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (d : ProbComp (Bytes 16))
  {qf qs ℓ : ℕ}

/-- **The ITSR realiser for the SUF wrapper.** -/
noncomputable def realizesItsrS
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) :
    RealizesItsrF (fun g => Reduction.Lazy.bItsrL (S.typedS (optRandU oR) d g))
      qf (2 * qs) qf (itsrQc qs) (itsrLc ℓ) qs ℓ where
  A := itsrA S oR d
  eq g := itsrA_adv_eqS S oR d g
  hqP := itsrA_rawP S oR d hqf
  hcP := itsrA_chainP S oR d hqs
  hq := itsrA_raw S oR d hqf
  hqc := itsrA_chain S oR d hqs
  hLc := itsrA_chainLen S oR d hlong
  hqs := itsrA_tgt S oR d hqs
  htgt := itsrA_tgtOK S oR d hlong
  hout := itsrA_out S oR d hout

/-- **The ITSR realiser for the EUF wrapper** (the same program). -/
noncomputable def realizesItsrE
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) :
    RealizesItsrF (fun g => Reduction.Lazy.bItsrL (S.typedE (optRandU oR) d g))
      qf (2 * qs) qf (itsrQc qs) (itsrLc ℓ) qs ℓ where
  A := itsrA S oR d
  eq g := itsrA_adv_eqE S oR d g
  hqP := itsrA_rawP S oR d hqf
  hcP := itsrA_chainP S oR d hqs
  hq := itsrA_raw S oR d hqf
  hqc := itsrA_chain S oR d hqs
  hLc := itsrA_chainLen S oR d hlong
  hqs := itsrA_tgt S oR d hqs
  htgt := itsrA_tgtOK S oR d hlong
  hout := itsrA_out S oR d hout

/-- **Closed ITSR term (SUF).** -/
theorem itsrSufI_le_optRandU
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) :
    itsrSufI S (optRandU oR) d ≤ epsItsrF qf (2 * qs) qf (itsrQc qs) (itsrLc ℓ) qs ℓ :=
  itsrSufI_le_fine S (optRandU oR) d (realizesItsrS S oR d hqf hqs hlong hout)

/-- **Closed ITSR term (EUF).** -/
theorem itsrEufI_le_optRandU
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) :
    itsrEufI S (optRandU oR) d ≤ epsItsrF qf (2 * qs) qf (itsrQc qs) (itsrLc ℓ) qs ℓ :=
  itsrEufI_le_fine S (optRandU oR) d (realizesItsrE S oR d hqf hqs hlong hout)

end Realiser

/-! ## Raising the parameters -/

/-- A realiser at larger parameters (same program). -/
def raiseItsr
    {B : ∀ g : CF St Blk, ITSRAdversary (Reduction.itsrProblem Link.vp (primsG (liftC g)))}
    {qP cP q qc Lc qs ℓ qP' cP' q' qc' Lc' qs' ℓ' : ℕ} (R : RealizesItsrF B qP cP q qc Lc qs ℓ)
    (h1 : qP ≤ qP') (h2 : cP ≤ cP') (h3 : q ≤ q') (h4 : qc ≤ qc') (h5 : Lc ≤ Lc')
    (h6 : qs ≤ qs') (h7 : ℓ ≤ ℓ') : RealizesItsrF B qP' cP' q' qc' Lc' qs' ℓ' where
  A := R.A
  eq := R.eq
  hqP := R.hqP.mono h1
  hcP := R.hcP.mono h2
  hq := R.hq.mono h3
  hqc := R.hqc.mono h4
  hLc := R.hLc.mono fun t ht => by
    rcases t with n | ((c | bs) | x)
    · trivial
    · trivial
    · exact le_trans (show bs.length ≤ Lc from ht) h5
    · trivial
  hqs := R.hqs.mono h6
  htgt := R.htgt.mono fun t ht => by
    rcases t with n | ((c | bs) | x)
    · trivial
    · trivial
    · trivial
    · exact fun k => le_trans (show msgLe ℓ (k, x) from ht k) h7
  hout := fun kx hkx => le_trans (R.hout kx hkx) h7

/-! ## The realisers at the parameters of the closed theorems of `ComposeFinal` -/

section Closed

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (d : ProbComp (Bytes 16))
  {qf qs ℓ : ℕ}

theorem itsrLc_le_2_21 (hℓ : ℓ ≤ 2 ^ 26) : itsrLc ℓ ≤ 2 ^ 21 := by
  rw [itsrLc_eq]
  refine max_le (by norm_num) ?_
  have := Nat.div_le_div_right (c := 64) (Nat.add_le_add_right hℓ 56)
  have h2 : (2 ^ 26 + 56) / 64 = 2 ^ 20 := by norm_num
  omega

/-- At `qf ≤ 2^60`, `qs ≤ 2^20`, `ℓ ≤ 2^26`: the parameters of `suf_final_2_60_2_20`. -/
noncomputable def realizesItsrS_2_60_2_20
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20) (hℓ : ℓ ≤ 2 ^ 26) :
    RealizesItsrF (fun g => Reduction.Lazy.bItsrL (S.typedS (optRandU oR) d g))
      (2 ^ 60) (2 ^ 60) (2 ^ 60) (2 ^ 42) (2 ^ 21) (2 ^ 20) (2 ^ 26) :=
  raiseItsr (realizesItsrS S oR d hqf hqs hlong hout) hf (by omega) hf
    (by rw [itsrQc_eq]; nlinarith) (itsrLc_le_2_21 hℓ) hs hℓ

/-- EUF twin of `realizesItsrS_2_60_2_20`. -/
noncomputable def realizesItsrE_2_60_2_20
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20) (hℓ : ℓ ≤ 2 ^ 26) :
    RealizesItsrF (fun g => Reduction.Lazy.bItsrL (S.typedE (optRandU oR) d g))
      (2 ^ 60) (2 ^ 60) (2 ^ 60) (2 ^ 42) (2 ^ 21) (2 ^ 20) (2 ^ 26) :=
  raiseItsr (realizesItsrE S oR d hqf hqs hlong hout) hf (by omega) hf
    (by rw [itsrQc_eq]; nlinarith) (itsrLc_le_2_21 hℓ) hs hℓ

/-- At `qf ≤ 2^64`, `qs ≤ 2^40`, `ℓ ≤ 2^26`: the parameters of `suf_final_2_80_2_40`. -/
noncomputable def realizesItsrS_2_80_2_40
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40) (hℓ : ℓ ≤ 2 ^ 26) :
    RealizesItsrF (fun g => Reduction.Lazy.bItsrL (S.typedS (optRandU oR) d g))
      (2 ^ 64) (2 ^ 64) (2 ^ 80) (2 ^ 62) (2 ^ 21) (2 ^ 40) (2 ^ 26) :=
  raiseItsr (realizesItsrS S oR d hqf hqs hlong hout) hf (by omega) (by omega)
    (by rw [itsrQc_eq]; nlinarith) (itsrLc_le_2_21 hℓ) hs hℓ

/-- At `qf ≤ 2^64`, `qs ≤ 2^64`, `ℓ ≤ 2^26`: the parameters of `suf_final_2_90_2_64`. -/
noncomputable def realizesItsrS_2_90_2_64
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ ≤ 2 ^ 26) :
    RealizesItsrF (fun g => Reduction.Lazy.bItsrL (S.typedS (optRandU oR) d g))
      (2 ^ 64) (2 ^ 65) (2 ^ 90) (2 ^ 85) (2 ^ 21) (2 ^ 64) (2 ^ 26) :=
  raiseItsr (realizesItsrS S oR d hqf hqs hlong hout) hf (by omega) (by omega)
    (by rw [itsrQc_eq]; nlinarith) (itsrLc_le_2_21 hℓ) hs hℓ

/-- EUF twin of `realizesItsrS_2_90_2_64`. -/
noncomputable def realizesItsrE_2_90_2_64
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ ≤ 2 ^ 26) :
    RealizesItsrF (fun g => Reduction.Lazy.bItsrL (S.typedE (optRandU oR) d g))
      (2 ^ 64) (2 ^ 65) (2 ^ 90) (2 ^ 85) (2 ^ 21) (2 ^ 64) (2 ^ 26) :=
  raiseItsr (realizesItsrE S oR d hqf hqs hlong hout) hf (by omega) (by omega)
    (by rw [itsrQc_eq]; nlinarith) (itsrLc_le_2_21 hℓ) hs hℓ

end Closed

/-! ## Plugged into the composed theorems (the eleven other realisers still assumed) -/

section Composed

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}

/-- `suf_final_optRandU` with the twelfth realiser discharged. -/
theorem suf_final_optRandU_itsr
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (R : SufRealizers S (optRandU oR) ($ᵗ (Bytes 16))) {Qc N qs' ℓ' : ℕ}
    (h : R.Le Qc N qs' ℓ') (hQ : Qc ≤ 2 ^ 126) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (itsrQc qs) (itsrLc ℓ) qs ℓ + ((66 * Qc + 40 : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP Qc N qs' ℓ' : ℝ≥0∞) / 2 ^ 256 :=
  suf_final_optRandU oR (realizesItsrS S oR _ hqf hqs hlong hout) R h hQ

/-- `euf_final` at `optRandU oR` with the twelfth realiser discharged. -/
theorem euf_final_optRandU_itsr
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (R : EufRealizers S (optRandU oR) ($ᵗ (Bytes 16))) {Qc N qs' ℓ' : ℕ}
    (h : R.Le Qc N qs' ℓ') (hQ : Qc ≤ 2 ^ 126) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (itsrQc qs) (itsrLc ℓ) qs ℓ + ((66 * Qc + 40 : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP Qc N qs' ℓ' : ℝ≥0∞) / 2 ^ 256 :=
  euf_final (realizesItsrE S oR _ hqf hqs hlong hout) R h hQ

/-- `suf_final_2_60_2_20` at `optRandU oR` with the twelfth realiser discharged: forger with at
most `2^60` compression queries, `2^20` signing queries, messages of at most `2^26` bytes. -/
theorem suf_final_2_60_2_20_itsr
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20) (hℓ : ℓ ≤ 2 ^ 26)
    (R : SufRealizers S (optRandU oR) ($ᵗ (Bytes 16)))
    (h : R.Le (2 ^ 60) (2 ^ 81) (2 ^ 20) (2 ^ 20)) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 70)⁻¹ + ((2 : ℝ≥0∞) ^ 128)⁻¹ + ((2 : ℝ≥0∞) ^ 61)⁻¹ :=
  suf_final_2_60_2_20 (realizesItsrS_2_60_2_20 S oR _ hqf hqs hlong hout hf hs hℓ) R h

/-- EUF twin of `suf_final_2_60_2_20_itsr`. -/
theorem euf_final_2_60_2_20_itsr
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => Ideal.Realize.isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20) (hℓ : ℓ ≤ 2 ^ 26)
    (R : EufRealizers S (optRandU oR) ($ᵗ (Bytes 16)))
    (h : R.Le (2 ^ 60) (2 ^ 81) (2 ^ 20) (2 ^ 20)) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 70)⁻¹ + ((2 : ℝ≥0∞) ^ 128)⁻¹ + ((2 : ℝ≥0∞) ^ 61)⁻¹ :=
  euf_final_2_60_2_20 (realizesItsrE_2_60_2_20 S oR _ hqf hqs hlong hout hf hs hℓ) R h

end Composed

end Ideal.Realize.Itsr

#print axioms Ideal.Realize.Itsr.realizesItsrS
#print axioms Ideal.Realize.Itsr.realizesItsrE
#print axioms Ideal.Realize.Itsr.itsrSufI_le_optRandU
#print axioms Ideal.Realize.Itsr.itsrEufI_le_optRandU
#print axioms Ideal.Realize.Itsr.itsrQc_eq
#print axioms Ideal.Realize.Itsr.itsrLc_eq
#print axioms Ideal.Realize.Itsr.raiseItsr
#print axioms Ideal.Realize.Itsr.realizesItsrS_2_60_2_20
#print axioms Ideal.Realize.Itsr.realizesItsrE_2_60_2_20
#print axioms Ideal.Realize.Itsr.realizesItsrS_2_80_2_40
#print axioms Ideal.Realize.Itsr.realizesItsrS_2_90_2_64
#print axioms Ideal.Realize.Itsr.realizesItsrE_2_90_2_64
#print axioms Ideal.Realize.Itsr.suf_final_optRandU_itsr
#print axioms Ideal.Realize.Itsr.euf_final_optRandU_itsr
#print axioms Ideal.Realize.Itsr.suf_final_2_60_2_20_itsr
#print axioms Ideal.Realize.Itsr.euf_final_2_60_2_20_itsr
