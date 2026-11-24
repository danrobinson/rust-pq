import Integration.SlhDsaCompressionReadout
import Integration.SlhDsaCompressionCompilePort
import Integration.SlhDsaCompressionClassCandidates

set_option maxRecDepth 8192

universe u v w

namespace Reduction.Compression.Recording.Compile
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open scoped Kronecker ComplexOrder

def taggedPair : Option (Right × Right) → Option (Input × Input) :=
  Option.map fun uv => (.inr uv.1,.inr uv.2)

def wins {T : Type} (p : Chain512 → T) (g : CompressionTables) : Option (Right × Right) → Prop
  | none => False
  | some (a,b) => a ≠ b ∧ p (g.2 a) = p (g.2 b)

theorem reports_tagged {T : Type} (p : Chain512 → T) (a : CF St Blk) (h : Full) (uv : Option (Right × Right)) :
    Database.reports p (taggedPair uv) h ↔ wins p (a,h ∘ Sum.inr) uv := by
  rcases uv with _|⟨i,j⟩
  · simp [taggedPair,Database.reports,wins]
  change (∃ l r : Input, some (Sum.inr i, Sum.inr j) = some (l,r) ∧ l ≠ r ∧
    p (h l) = p (h r)) ↔ i ≠ j ∧ p (h (.inr i)) = p (h (.inr j))
  constructor
  · rintro ⟨l,r,hpair,hd,he⟩
    obtain ⟨hl,hr⟩ := Prod.mk.inj (Option.some.inj hpair)
    subst l
    subst r
    exact ⟨fun hij => hd (congrArg Sum.inr hij),he⟩
  · rintro ⟨hd,he⟩
    exact ⟨.inr i,.inr j,rfl,fun e => hd (Sum.inr.inj e),he⟩

private theorem tables_avg (f : CompressionTables → ℝ≥0∞) :
    (∑ g, unifW _ g * f g) = ∑ a, unifW _ a * ∑ b, unifW _ b * f (a,b) := by
  simp only [Fintype.sum_prod_type,unifW,Finset.mul_sum,Fintype.card_prod,Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),mul_assoc]

variable {E α : Type} [Fintype E] [DecidableEq E] {T : Type}

open Classical in
/-- Compile a compression-port search once and identify its exact measured
success averaged over both tables. Addresses reported for SHA-512 always
select the right port, including when SHA-256 is used in superposition. -/
theorem shared_search (p : Chain512 → T) (M : (Input → Output) → Closed (WS Input Output E) α)
    (pick : α → Option (Right × Right)) (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 M q)
    (ρ₀ : Matrix (WS Input Output E) (WS Input Output E) ℂ)
    (pos : ρ₀.PosSemidef) (tr : ρ₀.trace = 1) :
    ∃ x : QuantumComp LocalSig.instruments.{0} (qromSpec Input Output) (fun _ => α) (progReg Input Output E),
    ∃ ρ : SubState ((Input × Output) × E), x.IsQueryBound (fun _ => q) ∧
      (∑ g : CompressionTables, unifW _ g * qWeight (fun z => wins p g (pick z)) (M (oracle g)) ρ₀) =
        ∑ a : CF St Blk, unifW _ a * ∑ h : Full, unifW _ h *
          qprob LocalSig.Interp.instruments (project a h) x ρ
            (fun z => Database.reports p (taggedPair (pick z.2)) h) := by
  classical
  obtain ⟨x,hx,he⟩ := program M q hq
  obtain ⟨ρ,hρ⟩ := exists_subState (A := (Input × Output) × E) ρ₀ pos tr
  refine ⟨x,ρ,hx,?_⟩
  rw [tables_avg]
  refine Finset.sum_congr rfl fun a _ => congrArg (unifW _ a * ·) ?_
  rw [← right_mean (fun b => qWeight (fun z => wins p (a,b) (pick z)) (M (oracle (a,b))) ρ₀)]
  refine Finset.sum_congr rfl fun h _ => congrArg (unifW _ h * ·) ?_
  rw [he a h (fun z => Database.reports p (taggedPair (pick z)) h) ρ,← hρ]
  apply qWeight_congr_ev
  exact fun z => (reports_tagged p a h (pick z)).symm

open PQ.QROM.Purify

/-- An initial mixed state admits one decomposition for all oracle and event choices. -/
theorem mixed_mean {A : QReg} {L : LocalSig.{u,v}} {W : QReg → Type w} (I : L.Interp)
    (x : QuantumComp L (qromSpec Input Output) W A) (ρ : SubState A) (q : ℕ)
    (hq : x.IsQueryBound (fun _ => q)) (a : CF St Blk) (ev : Full → (Σ u, W u) → Prop)
    (C : ℝ) (hC : 0 ≤ C)
    (pure_bound : ∀ v : EuclideanSpace ℂ (A × Unit), (∑ h : Full, (Fintype.card Full : ℝ)⁻¹ *
      pv I (project a h) x (ev h) v) ≤ C * ‖v‖ ^ 2) :
    (∑ h : Full, unifW _ h * qprob I (project a h) x ρ (ev h)) ≤ ENNReal.ofReal C := by
  classical
  obtain ⟨vs,hvs⟩ := exists_ketBra_sum (ρ.prod (SubState.basis ())).posSemidef
  have mass : ∑ j, ‖vs j‖ ^ 2 ≤ 1 := by
    have ht := (ρ.prod (SubState.basis ())).trace_re_le_one
    rw [hvs,Matrix.trace_sum,Complex.re_sum] at ht
    exact le_trans (le_of_eq (Finset.sum_congr rfl fun j _ => (trace_re_ketBra_self _).symm)) ht
  have finite : ∀ h, qprob I (project a h) x ρ (ev h) ≠ ⊤ := fun h =>
    ne_top_of_le_ne_top one_ne_top ((HybridModel.ofProgram I x ρ q hq (ev h)).prob_le_one _ id)
  have wfinite (h : Full) : unifW Full h ≠ ⊤ := by
    exact ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have wf (h : Full) : (unifW Full h).toReal = (Fintype.card Full : ℝ)⁻¹ := by
    rw [unifW,ENNReal.toReal_inv,ENNReal.toReal_natCast]
  have decomp (h : Full) : (qprob I (project a h) x ρ (ev h)).toReal =
      ∑ j, pv I (project a h) x (ev h) (vs j) := by
    rw [qprob_toReal_eq_DW,hvs,map_sum,Complex.re_sum]
    rfl
  apply (ENNReal.toReal_le_toReal (ENNReal.sum_ne_top.mpr (fun h _ =>
    ENNReal.mul_ne_top (wfinite h) (finite h))) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hC,ENNReal.toReal_sum (fun h _ => ENNReal.mul_ne_top (wfinite h) (finite h))]
  simp only [ENNReal.toReal_mul,wf,decomp,Finset.mul_sum]
  rw [Finset.sum_comm]
  calc _ ≤ ∑ j, C * ‖vs j‖^2 := Finset.sum_le_sum fun j _ => pure_bound (vs j)
       _ ≤ C := by rw [← Finset.mul_sum]; simpa using mul_le_mul_of_nonneg_left mass hC

open Classical in
/-- Transfer a homogeneous bound for bounded pure-state program runs to the
actual Born probability of a machine, averaged over the two compression tables. -/
theorem shared_search_le (p : Chain512 → T) (M : (Input → Output) → Closed (WS Input Output E) α)
    (pick : α → Option (Right × Right)) (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 M q)
    (ρ₀ : Matrix (WS Input Output E) (WS Input Output E) ℂ)
    (pos : ρ₀.PosSemidef) (tr : ρ₀.trace = 1) (C : ℝ) (hC : 0 ≤ C)
    (hpure : ∀ (a : CF St Blk)
      (x : QuantumComp LocalSig.instruments.{0} (qromSpec Input Output) (fun _ => α) (progReg Input Output E)),
      x.IsQueryBound (fun _ => q) → ∀ v : EuclideanSpace ℂ ((progReg Input Output E) × Unit),
      (∑ h : Full, (Fintype.card Full : ℝ)⁻¹ * pv LocalSig.Interp.instruments (project a h) x
        (fun t => Database.reports p (taggedPair (pick t.2)) h) v) ≤ C * ‖v‖^2) :
    (∑ g : CompressionTables, unifW _ g * qWeight (fun z => wins p g (pick z)) (M (oracle g)) ρ₀) ≤
      ENNReal.ofReal C := by
  obtain ⟨x,ρ,hx,e⟩ := shared_search p M pick q hq ρ₀ pos tr
  rw [e]
  calc _ ≤ ∑ a : CF St Blk, unifW _ a * ENNReal.ofReal C := by
         refine Finset.sum_le_sum fun a _ => mul_le_mul' le_rfl ?_
         exact mixed_mean _ x ρ q hx a _ C hC (hpure a x hx)
       _ = _ := by rw [← Finset.sum_mul,sum_unifW,one_mul]

end Reduction.Compression.Recording.Compile
#print axioms Reduction.Compression.Recording.Compile.shared_search
#print axioms Reduction.Compression.Recording.Compile.mixed_mean
#print axioms Reduction.Compression.Recording.Compile.shared_search_le
