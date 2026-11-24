import Integration.SlhDsaCompressionCachedBound
import Integration.SlhDsaCompressionHiddenWeight

namespace Reduction.Compression.Transcript
open MLink Ideal Ideal.HP Ideal.Prf Ideal.Itsr MIdeal.Sha512 PQ.Interactive PQ.QROM Quantum ENNReal Classical
open OracleComp OracleSpec Recording.Compile HiddenWeight
open scoped ComplexOrder
variable {E α β : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Input Output E

private theorem uniform {X : Type} [Fintype X] [SampleableType X] (f : X → ℝ≥0∞) :
    mean ($ᵗ X) f = ∑ x, unifW _ x * f x := by
  simp only [mean,tsum_fintype,prob_uniformSample_eq,unifW]

private theorem mean_supp {X : Type} (P : ProbComp X) (f g : X → ℝ≥0∞)
    (h : ∀ x ∈ support P, f x ≤ g x) : mean P f ≤ mean P g := by
  apply tsum_le_tsum
  intro x
  by_cases hx : x ∈ support P
  · exact mul_le_mul' le_rfl (h x hx)
  · dsimp only
    rw [show prob P (· = x) = 0 from prEvent_eq_zero_of_not_mem_support P hx,zero_mul,zero_mul]

private theorem mean_const {X : Type} (P : ProbComp X) (c : ℝ≥0∞) : mean P (fun _ => c) ≤ c := by
  unfold mean
  rw [ENNReal.tsum_mul_right]
  exact (mul_le_mul' (tsum_prob_eq_le_one P) le_rfl).trans_eq (one_mul _)

noncomputable def remainingLoss (S : Sha2Set) (n q : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (16*((q:ℝ)+1)^3/2^(8*S.vp.params.n)) + (2*(q:ℝ≥0∞)+1)^2 * (n / 2^(8*S.vp.params.n))

/-- Pay for a bad classical transcript once. On each other transcript the
quantum continuation incurs its own query count and a search over recorded prefixes. -/
theorem deferred_bound (S : Sha2Set) (a : CF St Blk) (P : SHAReader α) (n : ℕ)
    (hn : IsQueryBoundP P (fun i => i.isRight = true) n) (t : Right → Chain512)
    (M : α → (Input → Output) → Closed Work β) (pick : β → Option (Right × Right))
    (q : ℕ) (hq : ∀ x, PUE (spec := unifSpec) cnt0 (M x) q)
    (ρ : Matrix Work Work ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1) :
    let P₀ := (simulateQ lazyRead P).run ([],t)
    let bad := fun z : α × Cache Right Chain512 => badV (trunc S initial) (z.2.1.map fun c => trunc S (z.2.2 c))
    mean (deferred P t) (fun z => qWeight (fun v => wins (trunc S) (a,z.2.2) (pick v))
      (M z.1 (oracle (a,z.2.2))) ρ) ≤ prT (P₀ >>= fun z => pure (bad z)) + remainingLoss S n q := by
  classical
  dsimp only
  let P₀ := (simulateQ lazyRead P).run ([],t)
  let bad := fun z : α × Cache Right Chain512 => badV (trunc S initial) (z.2.1.map fun c => trunc S (z.2.2 c))
  let loss := remainingLoss S n q
  rw [deferred,mean_bind,flag]
  apply le_trans _ (add_le_add le_rfl (mean_const P₀ loss))
  rw [← mean_add]
  apply mean_supp
  rintro ⟨x,s,u⟩ hz
  simp only [mean_bind,mean_pure]
  by_cases hbad : bad (x,s,u) = true
  · apply (mean_one _ (fun b => qWeight_le_one _ _ hp ht)).trans
    change _ ≤ (if bad (x,s,u) then 1 else 0) + loss
    rw [hbad]; exact le_self_add
  · have clean : (s.map fun c => trunc S (u c)).Nodup := by
      by_contra hn
      apply hbad
      simp only [bad,badV,decide_eq_true_eq]
      exact Or.inl hn
    have len := cache_length P n hn [] t (x,s,u) hz
    simp only [List.length_nil,zero_add] at len
    rw [uniform]
    change _ ≤ (if bad (x,s,u) then 1 else 0) + loss
    simp only [hbad, Bool.false_eq_true, ↓reduceIte, zero_add]
    exact (after_clean S a s u clean (M x) pick q (hq x) ρ hp ht).trans
      (add_le_add le_rfl (mul_le_mul' le_rfl (mul_le_mul' (Nat.cast_le.mpr len) le_rfl)))

private theorem bad_cache (S : Sha2Set) (P : SHAReader α) (n : ℕ)
    (hn : IsQueryBoundP P (fun i => i.isRight = true) n) (t : Right → Chain512) :
    prT ((simulateQ lazyRead P).run ([],t) >>= fun z =>
      pure (badV (trunc S initial) (z.2.1.map fun c => trunc S (z.2.2 c)))) ≤
    ((n^2 : ℕ) : ℝ≥0∞) * ((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹ := by
  let bad := fun (s : List Right) (u : Right → Chain512) => badV (trunc S initial) (s.map fun c => trunc S (u c))
  have overlay (s : List Right) (u b : Right → Chain512) :
      bad s (Ideal.Prf.mix s u b) = bad s u :=
    congrArg (badV (trunc S initial)) (List.map_congr_left fun c hc =>
      congrArg (trunc S) (mix_of_mem hc u b))
  have eq := defer P (fun _ s u => pure (bad s u)) [] t
  simp only [mix_nil,overlay] at eq
  refine le_trans ?_ (badPrefix_bound S id (fun g c => g c) (fun _ _ _ h => h) P n hn)
  rw [eq]
  apply le_of_eq
  exact prT_bind_congr _ _ _ fun z _ => (prT_bind_const _ _).symm

/-- Mixed classical-then-quantum SHA-512 collision bound, including the honest
phase and a potentially transcript-dependent quantum continuation on both compression ports. -/
theorem mixed_bound (S : Sha2Set) (a : CF St Blk) (P : SHAReader α) (n : ℕ)
    (hn : IsQueryBoundP P (fun i => i.isRight = true) n) (t : Right → Chain512)
    (M : α → (Input → Output) → Closed Work β) (pick : β → Option (Right × Right))
    (q : ℕ) (hq : ∀ x, PUE (spec := unifSpec) cnt0 (M x) q)
    (ρ : Matrix Work Work ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1) :
    mean (eager P) (fun z => qWeight (fun v => wins (trunc S) (a,z.2.2) (pick v))
      (M z.1 (oracle (a,z.2.2))) ρ) ≤
      ((n^2 : ℕ) : ℝ≥0∞) * ((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹ + remainingLoss S n q := by
  apply le_trans (le_of_eq (weighted P t _))
  exact (deferred_bound S a P n hn t M pick q hq ρ hp ht).trans
    (add_le_add (bad_cache S P n hn t) le_rfl)

end Reduction.Compression.Transcript
#print axioms Reduction.Compression.Transcript.deferred_bound
#print axioms Reduction.Compression.Transcript.mixed_bound
