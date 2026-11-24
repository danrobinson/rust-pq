import Integration.SlhDsaCompressionCachedPreimage

namespace Reduction.Compression.Recording.Compile
open MLink Ideal Ideal.Prf MIdeal.Sha512 OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal Classical
open scoped ComplexOrder
variable {E α : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Input Output E

private def outside (s : List Right) : Option (Right × Right) → Right
  | none => default
  | some (u,v) => if u ∈ s then v else u

private theorem classify (S : Sha2Set) (a : CF St Blk) (s : List Right) (t b : Right → Chain512)
    (clean : (s.map fun c => trunc S (t c)).Nodup) (z : Option (Right × Right))
    (h : wins (trunc S) (a,Ideal.Prf.mix s t b) z) :
    wins (trunc S) (a,b) z ∨ trunc S (b (outside s z)) ∈ (s.map fun c => trunc S (t c)).toFinset := by
  rcases z with _|⟨u,v⟩
  · exact h.elim
  obtain ⟨hd,he⟩ := h
  by_cases hu : u ∈ s <;> by_cases hv : v ∈ s
  · exact (hd (List.inj_on_of_nodup_map clean hu hv (by simpa [Ideal.Prf.mix,hu,hv] using he))).elim
  · right
    simpa only [outside,ite_eq_left hu,List.mem_toFinset,List.mem_map] using
      (show ∃ c ∈ s, trunc S (t c) = trunc S (b v) from ⟨u,hu,by simpa [Ideal.Prf.mix,hu,hv] using he⟩)
  · right
    simpa only [outside,ite_eq_right hu,List.mem_toFinset,List.mem_map] using
      (show ∃ c ∈ s, trunc S (t c) = trunc S (b u) from ⟨v,hv,by simpa [Ideal.Prf.mix,hu,hv] using he.symm⟩)
  · exact Or.inl ⟨hd,by simpa [Ideal.Prf.mix,hu,hv] using he⟩

/-- Conditional collision bound after a classical transcript with distinct SHA-512 prefixes. -/
theorem after_clean (S : Sha2Set) (a : CF St Blk) (s : List Right) (t : Right → Chain512)
    (clean : (s.map fun c => trunc S (t c)).Nodup)
    (M : (Input → Output) → Closed Work α) (pick : α → Option (Right × Right))
    (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 M q)
    (ρ : Matrix Work Work ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1) :
    (∑ b : Right → Chain512, unifW _ b * qWeight (fun z => wins (trunc S) (a,Ideal.Prf.mix s t b) (pick z))
      (M (oracle (a,Ideal.Prf.mix s t b))) ρ) ≤ ENNReal.ofReal (16*((q:ℝ)+1)^3/2^(8*S.vp.params.n)) +
        (2*(q:ℝ≥0∞)+1)^2 * (s.length / 2^(8*S.vp.params.n)) := by
  classical
  let B := (s.map fun c => trunc S (t c)).toFinset
  let old := fun b : Right → Chain512 => fun z : α => trunc S (b (outside s (pick z))) ∈ B
  let fresh := fun b : Right → Chain512 => fun z : α => wins (trunc S) (a,b) (pick z)
  let X := fun b : Right → Chain512 => M (oracle (a,Ideal.Prf.mix s t b))
  have weight (b : Right → Chain512) :
      qWeight (fun z => wins (trunc S) (a,Ideal.Prf.mix s t b) (pick z)) (X b) ρ ≤
      qWeight (fresh b) (X b) ρ + qWeight (old b) (X b) ρ := by
    have cover (z) (hz : wins (trunc S) (a,Ideal.Prf.mix s t b) (pick z)) :
        fresh b z ∨ (¬fresh b z ∧ old b z) := by
      by_cases hf : fresh b z
      · exact Or.inl hf
      · exact Or.inr ⟨hf,(classify S a s t b clean _ hz).resolve_left hf⟩
    apply (qWeight_mono cover (X b) ρ).trans
    rw [qWeight_or (fun z h k => k.1 h)]
    exact add_le_add le_rfl (qWeight_mono (fun _ h => h.2) _ _)
  have hc := cached_collision (trunc S) (2^(8*S.vp.params.n)) (by positivity)
    (fun K => (prefixCells_fraction S K).le) a s t M pick q hq ρ hp ht
  have hm := cached_prefix S a s t M (fun z => outside s (pick z)) B q hq ρ hp ht
  have card : B.card ≤ s.length := (List.toFinset_card_le _).trans_eq (List.length_map ..)
  calc _ ≤ ∑ b, unifW _ b * (qWeight (fresh b) (X b) ρ + qWeight (old b) (X b) ρ) :=
             Finset.sum_le_sum fun b _ => mul_le_mul' le_rfl (weight b)
       _ = _ := by simp only [mul_add,Finset.sum_add_distrib,fresh,old,X]
       _ ≤ _ := add_le_add hc (hm.trans (mul_le_mul' le_rfl (mul_le_mul' (Nat.cast_le.mpr card) le_rfl)))

end Reduction.Compression.Recording.Compile
#print axioms Reduction.Compression.Recording.Compile.after_clean
