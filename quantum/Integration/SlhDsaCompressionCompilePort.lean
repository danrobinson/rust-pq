import Integration.SlhDsaCompressionCost
import PQ.QROM.PurifyProgram
import PQ.Interactive.QromBridgeEvalProg

namespace Reduction.Compression.Recording.Compile
open MLink Ideal OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open scoped Kronecker

abbrev Left := St × Blk
abbrev Right := Chain512 × Block512
abbrev Full := Input → Chain512

/-- Each left address uses the fixed SHA-256 table. The right restriction of
the recording table supplies the independent uniform SHA-512 table. -/
def project (a : CF St Blk) (h : Full) : Input → Output :=
  oracle (a,fun x => h (.inr x))

def split : Full ≃ (Left → Chain512) × (Right → Chain512) :=
  ⟨fun h => (h ∘ Sum.inl,h ∘ Sum.inr), fun p => Sum.elim p.1 p.2,
    fun h => funext (fun x => by cases x <;> rfl), fun _ => rfl⟩

/-- The unused cells disappear under uniform averaging for every test. -/
theorem right_mean (F : (Right → Chain512) → ℝ≥0∞) :
    (∑ h : Full, unifW _ h * F (h ∘ Sum.inr)) = ∑ b, unifW _ b * F b := by
  classical
  have card := Fintype.card_congr split
  simp only [unifW, ← Finset.mul_sum]
  rw [card, Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
    (Or.inl (ENNReal.natCast_ne_top _))]
  rw [show (∑ h : Full, F (h ∘ Sum.inr)) =
      ∑ p : (Left → Chain512) × (Right → Chain512), F p.2 from Equiv.sum_comp split (fun p => F p.2)]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc : (Fintype.card (Left → Chain512) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hfin := ENNReal.natCast_ne_top (Fintype.card (Left → Chain512))
  calc _ = ((Fintype.card (Left → Chain512) : ℝ≥0∞)⁻¹ * Fintype.card (Left → Chain512)) *
      ((Fintype.card (Right → Chain512) : ℝ≥0∞)⁻¹ * ∑ b, F b) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hc hfin,one_mul]


variable {E α : Type} [Fintype E] [DecidableEq E]

/-- A single bounded program realizes all tagged worlds, including on an
arbitrary mixed input state and an event selected separately in each world. -/
theorem program (M : (Input → Output) → Closed (WS Input Output E) α) (q : ℕ)
    (hm : PUE (spec := unifSpec) cnt0 M q) :
    ∃ x : QuantumComp LocalSig.instruments.{0} (qromSpec Input Output) (fun _ => α) (progReg Input Output E),
    x.IsQueryBound (fun _ => q) ∧ ∀ (a : CF St Blk) (h : Full) (Ev : α → Prop) [DecidablePred Ev]
      (ρ : SubState ((Input × Output) × E)),
      qprob LocalSig.Interp.instruments (project a h) x ρ (fun p => Ev p.2) =
        qWeight Ev (M (project a h)) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) := by
  obtain ⟨x,hq,he⟩ := hm.exists_prog_qprob
  exact ⟨x,hq,fun a h Ev _ ρ => he Ev _ ρ⟩

variable (U : Type) [Fintype U] [DecidableEq U]
abbrev Fiber (Y : Type) [Fintype Y] := EuclideanSpace ℂ (Y × U)

/-- Restrict a coherent query vector to one address. -/
noncomputable def slice {X Y : Type} [Fintype X] [Fintype Y]
    (v : EuclideanSpace ℂ (Tight.Reg X Y U)) (x : X) : Fiber U Y :=
  WithLp.toLp 2 (fun p => v ((x,p.1),p.2))

private def translate {Y : Type} [AddCommGroup Y] (z : Y) : Y × U ≃ Y × U :=
  ⟨fun p => (p.1 + z,p.2), fun p => (p.1 - z,p.2),
    fun p => by rcases p with ⟨y,u⟩; simp, fun p => by rcases p with ⟨y,u⟩; simp⟩

/-- The response register receives the oracle answer by group addition. -/
noncomputable def shift {Y : Type} [Fintype Y] [AddCommGroup Y] (z : Y) : Fiber U Y ≃ₗᵢ[ℝ] Fiber U Y :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℂ (translate U z)

theorem slice_oracle {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] (H : X → Y) (v : EuclideanSpace ℂ (Tight.Reg X Y U)) (x : X) :
    slice U ((Tight.stdOracle X Y U).O H v) x = shift U (H x) (slice U v x) := by
  ext p
  rcases p with ⟨y,u⟩
  change (Tight.stdOracle X Y U).O H v ((x,y),u) = v ((x,y-H x),u)
  conv_lhs => rw [show y = (y-H x)+H x from (sub_add_cancel ..).symm]
  exact Tight.stdOracle_O_apply ..

def response (a : CF St Blk) : Input → Chain512 → Output
  | .inl t, _ => (a t,0)
  | .inr _, y => (0,arrayVectorEquivFin UInt64 8 y)

noncomputable def control (a : CF St Blk) (x : Input) : Option Chain512 → Fiber U Output ≃ₗᵢ[ℝ] Fiber U Output
  | none => LinearIsometryEquiv.refl ℝ _
  | some y => shift U (response a x y)

theorem ordinary_port (a : CF St Blk) (h : Full) (v : EuclideanSpace ℂ (Tight.Reg Input Output U)) (x : Input) :
    slice U ((Tight.stdOracle Input Output U).O (project a h) v) x =
      control U a x (some (h x)) (slice U v x) := by
  have e : response a x (h x) = project a h x := by cases x <;> rfl
  simp only [control,e]
  exact slice_oracle U _ _ _

end Reduction.Compression.Recording.Compile
#print axioms Reduction.Compression.Recording.Compile.right_mean
#print axioms Reduction.Compression.Recording.Compile.ordinary_port
#print axioms Reduction.Compression.Recording.Compile.program
