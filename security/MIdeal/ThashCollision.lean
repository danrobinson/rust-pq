import MIdeal.Thash512
import Ideal.Games.Itsr

namespace MIdeal.Sha512
open Ideal Ideal.HP Ideal.Itsr MLink SLHDSA OracleComp OracleSpec ENNReal
variable (S : Sha2Set)

abbrev Cell := Chain512 × Block512

def path (pk : S.Node) (a : Bytes 22) (xs : List S.Node) :=
  seedBlock S pk :: thashBlocks S a xs

/-- On a transcript with distinct digest prefixes, two SHA-512 paths with the
same truncated output have identical blocks. The initial value is reserved. -/
theorem path_inj (g : CF Chain512 Block512) (log : List Cell)
    (good : badV (trunc S initial) (log.map (fun c => trunc S (g c))) ≠ true)
    (xs ys : List Block512) (hx : xs ≠ []) (hy : ys ≠ [])
    (hl : ∀ c ∈ mdCells g initial xs, c ∈ log) (hr : ∀ c ∈ mdCells g initial ys, c ∈ log)
    (eq : trunc S (mdFold g initial xs) = trunc S (mdFold g initial ys)) : xs = ys := by
  change ¬ badV (trunc S initial) (log.map (fun c => trunc S (g c))) = true at good
  simp only [badV, decide_eq_true_eq, not_or, not_not] at good
  have inj : ∀ c ∈ log, ∀ d ∈ log, trunc S (g c) = trunc S (g d) → c = d :=
    fun c hc d hd h => List.inj_on_of_nodup_map good.1 hc hd h
  apply md_inj g initial log (fun c hc d hd h => inj c hc d hd (congrArg (trunc S) h))
    (fun c hc h => good.2 (h ▸ List.mem_map_of_mem hc)) xs ys hl hr
  obtain h|⟨as,b,h⟩ := List.eq_nil_or_concat xs
  · exact (hx h).elim
  obtain e|⟨bs,d,e⟩ := List.eq_nil_or_concat ys
  · exact (hy e).elim
  rw [List.concat_eq_append] at h e
  subst xs; subst ys
  rw [mdFold_append, mdFold_append] at eq ⊢
  exact congrArg g (inj _ (hl _ (by simp [mdCells_append])) _ (hr _ (by simp [mdCells_append])) eq)

theorem thash_collision (g : CompressionTables) (hw : S.vp.params.n ≠ 16)
    (pk pk' : S.Node) (a a' : Bytes 22) (xs ys : List S.Node)
    (hx : xs.length ≠ 1) (hy : ys.length ≠ 1) (log : List Cell)
    (hl : ∀ c ∈ mdCells g.2 initial (path S pk a xs), c ∈ log)
    (hr : ∀ c ∈ mdCells g.2 initial (path S pk' a' ys), c ∈ log)
    (eq : (tablePrimitives g S.vp.params).Thash pk a xs = (tablePrimitives g S.vp.params).Thash pk' a' ys)
    (diff : (pk,a,xs) ≠ (pk',a',ys)) :
    badV (trunc S initial) (log.map (fun c => trunc S (g.2 c))) = true := by
  by_contra good
  rw [thash_wide S g hw _ _ _ hx, thash_wide S g hw _ _ _ hy] at eq
  have p := path_inj S g.2 log good _ _ (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) hl hr eq
  obtain ⟨hp,hm⟩ := List.cons.inj p
  obtain ⟨ha,hx⟩ := thashBlocks_injective S hm
  exact diff (by rw [seedBlock_injective S hp, ha, hx])

/-- Adaptive readers see a repeated digest prefix or the reserved prefix with
probability at most Q² / 2^(8n), including reads made by honest hash evaluations. -/
theorem badPrefix_bound {ι α : Type} {spec : OracleSpec ι} (cell : ι → Cell)
    (ans : CF Chain512 Block512 → (t : ι) → spec.Range t)
    (locality : ∀ g g' t, g (cell t) = g' (cell t) → ans g t = ans g' t)
    (A : OracleComp (unifSpec + spec) α) (Q : ℕ) (hq : IsQueryBoundP A (fun i => i.isRight = true) Q) :
    prT ($ᵗ (CF Chain512 Block512) >>= fun g =>
      (simulateQ (stImpl (ans g) (logU cell)) A).run [] >>= fun z =>
        pure (badV (trunc S initial) (z.2.map (fun c => trunc S (g c))))) ≤
      ((Q^2 : ℕ) : ℝ≥0∞) * ((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹ := by
  refine (prT_tape_le cell ans locality (trunc S) (trunc_uniform S) _ (badV_mono _) A Q hq).trans
    ((prT_tape_bad_le _ Q).trans (le_of_eq ?_))
  rw [card_bytes, Nat.cast_pow, pow_mul]
  norm_num

end MIdeal.Sha512
