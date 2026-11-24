import Integration.SlhDsaCompressionClassicalWalk

namespace Reduction.Compression.Transcript
open ENNReal Ideal Ideal.HP Ideal.Prf Ideal.Itsr OracleComp OracleSpec
variable {C V α : Type} [DecidableEq C] [Finite C] [SampleableType V] [SampleableType (C → V)]
abbrev Cache (C V : Type) := List C × (C → V)

/-- Remember every first read and sample only the unseen cells. -/
def lazyRead : QueryImpl (unifSpec + (C →ₒ V)) (StateT (Cache C V) ProbComp) := fun
  | .inl n => StateT.mk fun s => (fun v => (v,s)) <$> (unifSpec.query n : ProbComp _)
  | .inr c => StateT.mk fun (s,t) =>
      if c ∈ s then pure (t c,(s,t))
      else do
        let v ← $ᵗ V
        pure (v,(s ++ [c],Function.update t c v))

/-- Sampling the unobserved cells after an adaptive classical phase preserves the
joint law of its output, queried cells and the complete table. -/
theorem defer (P : OracleComp (unifSpec + (C →ₒ V)) α)
    (K : α → List C → (C → V) → ProbComp Bool) (s : List C) (t : C → V) :
    prT ($ᵗ (C → V) >>= fun g =>
      (simulateQ (stImpl (spec := C →ₒ V) (mix s t g) (logU id)) P).run s >>= fun z =>
        K z.1 z.2 (mix s t g)) =
    prT ((simulateQ lazyRead P).run (s,t) >>= fun z =>
      $ᵗ (C → V) >>= fun g => K z.1 z.2.1 (mix z.2.1 z.2.2 g)) := by
  induction P using OracleComp.inductionOn generalizing s t with
  | pure x => simp
  | query_bind i k ih =>
    rcases i with n|c
    · simp only [run_simulateQ_query_bind, stImpl, lazyRead, StateT.run_mk,
        bind_map_left, bind_assoc]
      rw [prT_swap]
      exact prT_bind_congr _ _ _ fun v _ => ih v s t
    · by_cases hc : c ∈ s
      · simp only [mix_of_mem hc, logU_of_mem (cell := id) hc,
          run_simulateQ_query_bind, stImpl, lazyRead, StateT.run_mk, ite_eq_left hc, pure_bind]
        exact ih _ s t
      · rw [prT_freeze hc t (fun M =>
          (simulateQ (stImpl (spec := C →ₒ V) M (logU id))
            (liftM ((unifSpec + (C →ₒ V)).query (.inr c)) >>= k)).run s >>= fun z => K z.1 z.2 M)]
        simp only [mix_append_self, logU_of_not_mem (cell := id) hc,
          run_simulateQ_query_bind, stImpl, lazyRead, StateT.run_mk, ite_eq_right hc, bind_assoc, pure_bind]
        exact prT_bind_congr _ _ _ fun v _ => ih v _ _

/-- Joint distribution of the classical output, transcript and complete compression table. -/
def eager (P : OracleComp (unifSpec + (C →ₒ V)) α) : ProbComp (α × List C × (C → V)) := do
  let g ← $ᵗ (C → V)
  let z ← (simulateQ (stImpl (spec := C →ₒ V) g (logU id)) P).run []
  pure (z.1,z.2,g)

def deferred (P : OracleComp (unifSpec + (C →ₒ V)) α) (t : C → V) :
    ProbComp (α × List C × (C → V)) := do
  let z ← (simulateQ lazyRead P).run ([],t)
  let g ← $ᵗ (C → V)
  pure (z.1,z.2.1,mix z.2.1 z.2.2 g)

/-- Arbitrary Born continuation weights may depend jointly on all three outputs. -/
theorem weighted (P : OracleComp (unifSpec + (C →ₒ V)) α) (t : C → V)
    (weight : α × List C × (C → V) → ℝ≥0∞) :
    (∑' z, Pr{let x ← eager P}[x = z] * weight z) =
      ∑' z, Pr{let x ← deferred P t}[x = z] * weight z := by
  classical
  apply tsum_congr
  intro z
  congr 1
  let f := fun x : α × List C × (C → V) => decide (x = z)
  have eq := defer P (fun x l g => pure (f (x,l,g))) [] t
  have eq' : prT (eager P >>= fun x => pure (f x)) =
      prT (deferred P t >>= fun x => pure (f x)) := by
    simpa only [eager,deferred,bind_assoc,pure_bind,mix_nil] using eq
  simpa only [prT_bind_pure,f,decide_eq_true_eq] using eq'

omit [Finite C] [SampleableType (C → V)] in
theorem cache_length (P : OracleComp (unifSpec + (C →ₒ V)) α) (q : ℕ)
    (hq : IsQueryBoundP P (fun i => i.isRight = true) q) (s : List C) (t : C → V) :
    ∀ z ∈ support ((simulateQ lazyRead P).run (s,t)), z.2.1.length ≤ s.length + q := by
  induction P using OracleComp.inductionOn generalizing q s t with
  | pure x => simp
  | query_bind i k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    rcases i with n|c
    · simp only [run_simulateQ_query_bind,lazyRead,StateT.run_mk,bind_map_left]
      intro z hz
      rw [mem_support_bind_iff] at hz
      obtain ⟨v,_,hz⟩ := hz
      exact ih v q (by simpa using hq.2 v) s t z hz
    · have pos : 0 < q := hq.1.resolve_left (by simp)
      have rest := hq.2
      simp only [Sum.isRight_inr,ite_true] at rest
      by_cases hc : c ∈ s
      · simp only [run_simulateQ_query_bind,lazyRead,StateT.run_mk,ite_eq_left hc,pure_bind]
        intro z hz
        exact (ih _ _ (rest _) s t z hz).trans (by omega)
      · simp only [run_simulateQ_query_bind,lazyRead,StateT.run_mk,ite_eq_right hc,bind_assoc,pure_bind]
        intro z hz
        rw [mem_support_bind_iff] at hz
        obtain ⟨v,_,hz⟩ := hz
        have h := ih v _ (rest v) (s ++ [c]) (Function.update t c v) z hz
        simp only [List.length_append,List.length_singleton] at h
        omega

open MLink SLHDSA MIdeal.Sha512 ClassCollision
variable (S : Sha2Set)
local notation "P₀" => randPrims (carrier S)

/-- Apply the conditional table law to the classification reduction's actual
first phase, retaining the entire table for the following quantum experiment. -/
theorem walk_weighted (a : CF St Blk) (pk : S.Node) (tbl : SecretTable S.vp P₀)
    (t : CF Chain512 Block512)
    (w : CallLog S × List (Chain512 × Block512) × CF Chain512 Block512 → ℝ≥0∞) :
    let P := readWalk S a pk (structureFree tbl) []
    (∑' z, Pr{let x ← eager P}[x = z] * w z) =
      ∑' z, Pr{let x ← deferred P t}[x = z] * w z :=
  weighted _ t w

end Reduction.Compression.Transcript
#print axioms Reduction.Compression.Transcript.walk_weighted
#print axioms Reduction.Compression.Transcript.cache_length
#print axioms Reduction.Compression.Transcript.defer
#print axioms Reduction.Compression.Transcript.weighted
