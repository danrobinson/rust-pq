import MIdeal.Itsr128fTrace

namespace MIdeal.Hmsg.Fast128
open MLink Ideal Ideal.Itsr Ideal.Prf Ideal.HP SLHDSA SLHDSA.Concrete OracleComp OracleSpec KeyedHash
open ENNReal AnswerTape KeyedHash.Covering
noncomputable section

private theorem curry_sample (f : CF St Blk → ProbComp Bool) :
    prT ($ᵗ (CF St Blk) >>= f) = prT ($ᵗ (St → Blk → St) >>= fun g => f (Function.uncurry g)) := by
  let e : (St → Blk → St) ≃ CF St Blk :=
    ⟨Function.uncurry,Function.curry,fun _ => rfl,fun _ => rfl⟩
  have bij : Function.Bijective (Function.uncurry : (St → Blk → St) → CF St Blk) := e.bijective
  have h := (SampleableType.map_uniformSample_evalDistEq_of_bijective bij).bind_left f
  simpa only [bind_map_left] using (prT_congr h.evalDist_eq).symm

private theorem coverage_bound (oa : Prog Bool) (Q : ℕ)
    (hq : IsQueryBoundP oa (fun i => i.isRight = true) Q) :
    prT ($ᵗ (CF St Blk) >>= fun g => (simulateQ (traceImpl g) oa).run [] >>= fun z =>
      pure (coverage g z.2)) ≤ reuseSum 66 6 33 Q := by
  rw [curry_sample]
  have e (g : St → Blk → St) :
      ((simulateQ (traceImpl (Function.uncurry g)) oa).run [] >>= fun z => pure (coverage (Function.uncurry g) z.2)) =
      ((simulateQ (stImpl (spec := mS St Blk) (fun t => g t.1.1 t.1.2) (logU (fun t => t.1.1))) oa).run [] >>= fun z =>
        pure (covB (idxOf Sha2Set.s128f.vp) (z.2.map (rowDigest (Function.uncurry g))))) := by
    have h := unique_run Prod.fst (Function.uncurry g) oa []
    change (simulateQ (stImpl (spec := mS St Blk) (fun t => g t.1.1 t.1.2) (logU (fun t => t.1.1))) oa).run [] = _ at h
    rw [h,bind_map_left]
    rfl
  simp only [e]
  exact (adaptive_row_coverage _ oa Q hq).trans (prT_tape_cov_le Sha2Set.s128f.vp Q)

private theorem bad_bound (oa : Prog Bool) (Q : ℕ)
    (hq : IsQueryBoundP oa (fun i => i.isRight = true) Q) :
    prT ($ᵗ (CF St Blk) >>= fun g => (simulateQ (traceImpl g) oa).run [] >>= fun z =>
      pure (bad g z.2)) ≤ ((Q^2 : ℕ) : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  have e (g : CF St Blk) :
      ((simulateQ (traceImpl g) oa).run [] >>= fun z => pure (bad g z.2)) =
      ((simulateQ (stImpl (spec := mS St Blk) (fun t => g t.1) (logU Prod.fst)) oa).run [] >>= fun z =>
        pure (badV IV128 (z.2.map g))) := by
    have h := unique_run id g oa []
    change (simulateQ (stImpl (spec := mS St Blk) (fun t => g t.1) (logU Prod.fst)) oa).run [] = _ at h
    rw [h,bind_map_left]
    rfl
  simp only [e]
  exact (prT_tape_le (spec := mS St Blk) Prod.fst (fun g t => g t.1) (fun _ _ _ h => h) id
    (fun _ => rfl) (badV IV128) (badV_mono IV128) oa Q hq).trans (prT_tape_bad_le IV128 Q)

local instance (g : CompressionTables) : SampleableType (tablePrimitives g Sha2Set.s128f.vp.params).Y :=
  inferInstanceAs (SampleableType Key)

/-- Classical SHA2-128f ITSR with a public random SHA-256 compression table. The SHA-512
table can be fixed arbitrarily. The total budget includes both MGF1 counter cells. -/
theorem itsr_bound (A : OracleComp (unifSpec + (hS St Blk + ITSRTargetSpec Msg Key)) Input)
    (g512 : CF Chain512 Block512) (q qs L : ℕ)
    (hq : IsQueryBoundP A (fun i => isCompI i = true) q) (hs : IsQueryBoundP A (fun i => isTgtI i = true) qs)
    (ht : AllQueriesSatisfy A (tgtOK (lengthOK L))) (ho : ∀ x ∈ support A, lengthOK L x) :
    let Q := q + (qs + 1) * ((L+56)/64 + 4)
    prT ($ᵗ (CF St Blk) >>= fun g => ITSRExperiment (ItsrAdvI.inst A
      (Reduction.itsrProblem Sha2Set.s128f.vp (tablePrimitives (g,g512) Sha2Set.s128f.vp.params)) g)) ≤
        reuseSum 66 6 33 Q + ((Q^2 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)^256)⁻¹ := by
  let Q := q + (qs + 1) * ((L+56)/64 + 4)
  have count := game_count A q qs L hq hs ht ho
  have step : prT ($ᵗ (CF St Blk) >>= fun g => ITSRExperiment (ItsrAdvI.inst A
      (Reduction.itsrProblem Sha2Set.s128f.vp (tablePrimitives (g,g512) Sha2Set.s128f.vp.params)) g)) ≤
      prT ($ᵗ (CF St Blk) >>= fun g => (simulateQ (traceImpl g) (game A)).run [] >>= fun z =>
        pure (coverage g z.2 || bad g z.2)) := by
    apply prT_bind_mono
    intro g _
    apply le_trans (le_of_eq (congrArg prT (game_eq (g,g512) A).symm))
    change prT (simulateQ (markImpl g) (game A)) ≤ _
    rw [markImpl_eq, ← fst_map_run_stImpl (spec := mS St Blk)
      (fun t => g t.1) logCell (game A) ([] : Trace), map_eq_bind_pure_comp]
    apply prT_bind_mono
    intro z hz
    simp only [Function.comp, prT_pure]
    cases h : z.1 with
    | false => simp
    | true => rcases win_trace g A z hz h with h | h <;> simp [h]
  apply step.trans
  apply (prT_bind_le_add _ _ _ _ (fun g => prT_bind_le_add _ _ _ _ (fun z => prT_pure_or_le _ _))).trans
  apply add_le_add (coverage_bound (game A) Q count)
  simpa only [card_St,Nat.cast_pow,Nat.cast_ofNat] using bad_bound (game A) Q count

end
end MIdeal.Hmsg.Fast128
#print axioms MIdeal.Hmsg.Fast128.itsr_bound
