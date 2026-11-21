import Ideal.Games.ItsrFine
import Ideal.Inst.ItsrNumeric

/-!
# ITSR of `H_msg` at SLH-DSA-SHA2-128s with fine accounting of the adversary's queries

The outer hash of `H_msg` is `SHA-256(R ‖ PK.seed ‖ digest ‖ 0^4)` (MGF1, counter 0): 68 bytes,
two blocks, and the SECOND block is the constant `cB = 0^4 ‖ 0x80 ‖ 0^51 ‖ len(544)`
(`oblocksH_eq`).  With `P128 b := (b = cB)`, `Ideal.Itsr.itsr_le_fine` gives

`itsrIF A ≤ reuseSum 63 12 14 (qP + cP + 2 (qs + 1)) + (q + qc·Lc + (qs + 1)((ℓ + 56)/64 + 3))² / 2^256`

for an adversary with chain queries (`ItsrAdvF`), where

* `qP` bounds its raw compression queries whose block is `cB`,
* `cP` bounds its chain queries whose second block is `cB`,
* `q` bounds all its raw compression queries, `qc` its chain queries, of at most `Lc` blocks each,
* `qs` its target queries, `ℓ` the message length in bytes.

Hash evaluations that the adversary performs as chain queries with a second block other than
`cB` (every `Thash`/`PRF` evaluation has the padding byte `0x80` or an address byte in a position
where `cB` is zero; this is a statement about the realising program and is not proved here)
enter only the `Q² / 2^256` term.
-/

open OracleComp OracleSpec ENNReal KeyedHash

namespace Ideal

open SLHDSA Ideal.HP Ideal.Itsr

/-- The blocks after the first of every outer `H_msg` input. -/
def cTail : List Blk := blocksOf ([0, 0, 0, 0] ++ tailL 68)

/-- The constant second block of the outer hash of `H_msg`. -/
def cB : Blk := cTail.headD (Vector.replicate 64 0)

theorem cTail_eq : cTail = [cB] := by
  have hl : cTail.length = 1 := by
    unfold cTail
    rw [blocksOf_length, List.length_append, tailL_length]
    rfl
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hl
  rw [cB, ha]
  rfl

/-- **The outer blocks of `H_msg` are a first block and the constant block `cB`.** -/
theorem oblocksH_eq (R pk : Bytes 16) (s : St) : ∃ b₀ : Blk, oblocksH R pk s = [b₀, cB] := by
  let b₀ : Blk := ⟨(R.toList ++ (pk.toList ++ s.toList)).toArray, by simp⟩
  refine ⟨b₀, ?_⟩
  have hb : b₀.toList = R.toList ++ (pk.toList ++ s.toList) := rfl
  have hlen : (hOuter R pk s).data.toList.length = 68 := by
    rw [hOuter_toList]; simp
  have hpad : padL (hOuter R pk s).data.toList = b₀.toList ++ ([0, 0, 0, 0] ++ tailL 68) := by
    unfold padL
    rw [hlen, hOuter_toList, hb]
    simp only [List.append_assoc]
  rw [oblocksH, padBlocks, hpad, blocksOf_cons, ← cTail_eq]
  rfl

/-- The block is the constant second outer block of `H_msg`. -/
def P128 (b : Blk) : Bool := decide (b = cB)

theorem obH_P (kx : Bytes 16 × X128) (s : St) (b₀ b₁ : Blk) (h : obH kx s = [b₀, b₁]) :
    P128 b₁ = true := by
  obtain ⟨b, hb⟩ := oblocksH_eq kx.1 kx.2.1 s
  rw [obH, hb] at h
  have : b₁ = cB := ((List.cons.inj (List.cons.inj h).2).1).symm
  simp [P128, this]

/-- Ideal-model ITSR adversaries with chain queries against `H_msg` at 128s. -/
abbrev ItsrAdvF128 := ItsrAdvF St Blk (Bytes 16) X128

/-- The adversary against the Reduction's ITSR problem at the table `g`: raw compression queries
are answered by `g`, chain queries by the Merkle–Damgård iteration of `g` from the SHA-256
initial value. -/
def instItsrF (A : ItsrAdvF128) (g : CF St Blk) :
    ITSRAdversary (Reduction.itsrProblem Link.vp (primsG (liftC g))) where
  main := simulateQ (instImplF IV128 g) A

/-- ITSR advantage against `H_msg` at 128s in the ideal-compression model, for an adversary with
chain queries. -/
noncomputable def itsrIF (A : ItsrAdvF128) : ℝ≥0∞ :=
  cfAdvantage fun g => ITSRExperiment (instItsrF A g)

/-- The experiment with the fine marking, as one program over the marked compression oracle. -/
noncomputable def itsrProgF128 (A : ItsrAdvF128) : OracleComp (unifSpec + mS St Blk) Bool :=
  @gameProgF St Blk (Bytes 16) X128 (Bytes 30) (Adrs × ℕ) sampY128 _ _ _ P128 IV128 ibH obH dig30
    idx128 A

theorem itsrIF_eq (A : ItsrAdvF128) :
    itsrIF A = prT ($ᵗ (CF St Blk) >>= fun g =>
      @ITSRExperiment (Bytes 16) X128 (Bytes 30) (Adrs × ℕ) _ _ _ _
        (ItsrAdvF.inst A IV128 (@probI St Blk (Bytes 16) X128 (Bytes 30) (Adrs × ℕ) sampY128
          IV128 ibH obH dig30 idx128 g) g)) := by
  rw [← cfAdvantage_eq_prT]
  refine congrArg cfAdvantage (funext fun g => ?_)
  exact ITSRExperiment_congr (itsrProblem_eq_probI g) _

private theorem card_St_invF : (Fintype.card St : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  rw [card_St, Nat.cast_pow, Nat.cast_ofNat]

/-- The bound in terms of the experiment's compression calls. -/
theorem itsr_bound_128s_fine_prog (A : ItsrAdvF128) (n Q : ℕ)
    (hn : IsQueryBoundP (itsrProgF128 A) (fun i => lgB Prod.snd i = true) n)
    (hQ : IsQueryBoundP (itsrProgF128 A) (fun i => i.isRight = true) Q) :
    itsrIF A ≤ reuseSum 63 12 14 n + ((Q ^ 2 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  rw [itsrIF_eq, ← card_St_invF]
  refine (@itsr_le_fine St Blk (Bytes 16) X128 (Bytes 30) (Adrs × ℕ) _ _ _ _ _ _ _ sampY128 _ _ _
    P128 IV128 ibH obH dig30 idx128 ibH_injective obH_inj obH_length obH_P prEvent_dig30 A n Q
    hn hQ).trans (add_le_add ?_ le_rfl)
  exact prT_tape_cov_le Link.vp n

/-- **ITSR of `H_msg` at SLH-DSA-SHA2-128s in the ideal-compression model, fine accounting.**
Only raw compression queries whose block is the constant block `cB` (`qP`), chain queries whose
second block is `cB` (`cP`), and `2 (qs + 1)` calls of the final check are coordinates of the
tuple of digests; all other compression work of the adversary (`q` raw queries, `qc` chain
queries of at most `Lc` blocks) enters only through `Q² / 2^256`. -/
theorem itsr_bound_128s_fine
    (A : OracleComp (unifSpec + (aS St Blk + ITSRTargetSpec X128 (Bytes 16))) (Bytes 16 × X128))
    (qP cP q qc Lc qs ℓ : ℕ)
    (hqP : IsQueryBoundP A (fun i => rawB (X := X128) (fun t : St × Blk => P128 t.2) i = true) qP)
    (hcP : IsQueryBoundP A (fun i => chB (St := St) (X := X128) (secondP P128) i = true) cP)
    (hq : IsQueryBoundP A (fun i => rawB (X := X128) (fun _ : St × Blk => true) i = true) q)
    (hqc : IsQueryBoundP A
      (fun i => chB (St := St) (X := X128) (fun _ : List Blk => true) i = true) qc)
    (hLc : AllQueriesSatisfy A (chOK (St := St) (X := X128) fun bs : List Blk => bs.length ≤ Lc))
    (hqs : IsQueryBoundP A (fun i => isTgtF (St := St) (Blk := Blk) (X := X128) i = true) qs)
    (htgt : AllQueriesSatisfy A (tgtOKF (St := St) (Blk := Blk) (msgLe ℓ)))
    (hout : ∀ kx ∈ support A, msgLe ℓ kx) :
    itsrIF A ≤ reuseSum 63 12 14 (qP + cP + 2 * (qs + 1)) +
      (((q + qc * Lc + (qs + 1) * ((ℓ + 56) / 64 + 3)) ^ 2 : ℕ) : ℝ≥0∞) *
        ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  refine itsr_bound_128s_fine_prog A _ _ ?_ ?_
  · have h := @gameProgF_bound St Blk (Bytes 16) X128 (Bytes 30) (Adrs × ℕ)
      (fun i => lgB Prod.snd i = true) _ sampY128 _ _ _
      (fun n h => by simp [lgB] at h) P128 IV128 ibH obH dig30 idx128 2 (msgLe ℓ)
      (fun kx _ => hashM_bound2 (fun t h => by simp [lgB] at h) IV128 ibH obH dig30 kx)
      (fun t : St × Blk => P128 t.2) (secondP P128) 1 (fun bs : List Blk => bs.length ≤ Lc)
      (fun q h => by simpa [lgB] using h)
      (fun bs _ => mdP_bound1 (fun t h => by simp [lgB] at h) P128 IV128 bs)
      A qP cP qs hqP hcP hqs htgt hLc hout
    rw [Nat.mul_one, Nat.mul_comm (qs + 1) 2] at h
    exact h
  · exact @gameProgF_bound St Blk (Bytes 16) X128 (Bytes 30) (Adrs × ℕ)
      (fun i => i.isRight = true) _ sampY128 _ _ _
      (fun n h => by simp at h) P128 IV128 ibH obH dig30 idx128 ((ℓ + 56) / 64 + 3) (msgLe ℓ)
      (fun kx hkx => hashM_bound IV128 ibH obH dig30 kx _ fun s => by
        have h1 : (ibH kx).length = (kx.2.2.2.length + 56) / 64 + 1 := iblocksH_length _ _ _ _
        have h2 := obH_length kx s
        have h3 : (kx.2.2.2.length + 56) / 64 ≤ (ℓ + 56) / 64 :=
          Nat.div_le_div_right (Nat.add_le_add_right hkx 56)
        omega)
      (fun _ : St × Blk => true) (fun _ : List Blk => true) Lc
      (fun bs : List Blk => bs.length ≤ Lc) (fun q _ => rfl)
      (fun bs hbs => (mdP_bound P128 IV128 bs).mono (by simpa using hbs))
      A q qc qs hq hqc hqs htgt hLc hout

end Ideal

#print axioms Ideal.oblocksH_eq
#print axioms Ideal.itsr_bound_128s_fine
