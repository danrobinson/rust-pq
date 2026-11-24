import Integration.SlhDsaAllGeneral
import Integration.SlhDsaSetEuf
import MReduction.Instances
import MReduction.Shake

namespace Reduction
open MLink TweakableHash SLHDSA SLHDSA.Security PQ.Interactive OracleSpec OracleComp Quantum ENNReal
open scoped Classical

variable {vp : ValidatedParams} {prims : Primitives vp.params}
  [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y] [Fintype prims.Y] {codec : CoreWireCodec vp.params prims.core}
  {rand : PublicKeyCore prims.core → ProbComp prims.Y} {seeds : ProbComp prims.PkSeed}
  {W : Type} [Fintype W]

/-- The twelve advantages of the actual primitive-game machines constructed
by the strong-forgery reduction. The public hash functions can be fixed. -/
noncomputable def reducedAdvantages (B : QForger W (internalAlg vp prims rand seeds)) : List ℝ≥0∞ :=
  [qPrfAdvantage (skPrfC vp prims) (qbPrfWC sufCheck B) B.ρ₀,
   qPrfAdvantage (msgPrf vp prims) (qbPrfMsgWL sufCheck B) B.ρ₀,
   qItsrAdvantage (itsrProblem vp prims) (qbItsrL B) B.ρ₀,
   qDsprFV_AdvantageG (qToDspr B).toGeneral, qTcrFV_AdvantageG (qToTcr B).toGeneral,
   qSM_DT_TCR_AdvantageG (qbTcrArM 1 B).toGeneral, qSM_DT_TCR_AdvantageG (qbTcrArM 2 B).toGeneral,
   qSM_DT_TCR_AdvantageG (qbTcrArM vp.params.len B).toGeneral,
   qSM_DT_TCR_AdvantageG (qbTcrArM vp.params.k B).toGeneral,
   qSM_DT_UD_AdvantageG (qrUd B).toGeneral, qSM_DT_PRE_AdvantageG (qrPre B).toGeneral,
   qSM_DT_TCR_AdvantageG (qrTcrT B).toGeneral]

set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
/-- For w=16 the coefficients of the twelve games sum to 27. A forger
therefore gives a specific primitive-game advantage at least its success / 27.
This conclusion concerns advantage; the computational overhead of each
machine is a separate resource question. -/
theorem fixed_primitive_witness (structural : Structural vp prims) (w : vp.params.w = 16)
    (Q : QForger W (pureBytesAlg vp prims codec rand seeds)) :
    ∃ a ∈ reducedAdvantages (qPureBytesToInternal Q),
      qStrongUnforgeableAdvantage Q ≤ 27*a ∧ qUnforgeableAdvantage Q ≤ 27*a := by
  classical
  let B := qPureBytesToInternal Q
  let games := (reducedAdvantages B).toFinset
  have nonempty : games.Nonempty := by
    refine ⟨_, List.mem_toFinset.mpr (List.mem_cons_self ..)⟩
  let a := games.max' nonempty
  have bound (x) (hx : x ∈ reducedAdvantages B) : x ≤ a :=
    Finset.le_max' games x (List.mem_toFinset.mpr hx)
  simp only [reducedAdvantages,List.forall_mem_cons,List.not_mem_nil, false_implies,forall_const,and_true] at bound
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩ := bound
  have limit : qBetaSufMemoG B ≤ 27*a := by
    unfold qBetaSufMemoG qBoundMemoG
    rw [w]
    norm_num
    calc _ ≤ a+a+a+(a+3*a)+(a+a+a+a)+14*a+a+a := by
            gcongr
         _ = _ := by ring
  have h := (slhdsa_pure_bytes_suf_cma_final_quantum_all_general structural Q).trans limit
  exact ⟨a, List.mem_toFinset.mp (Finset.max'_mem games nonempty), h, (quantum_euf_le_suf Q).trans h⟩

private theorem half_witness (structural : Structural vp prims) (w : vp.params.w = 16)
    (Q : QForger W (pureBytesAlg vp prims codec rand seeds)) (success : 1/2 ≤ qStrongUnforgeableAdvantage Q) :
    ∃ a ∈ reducedAdvantages (qPureBytesToInternal Q), 1/54 ≤ a := by
  obtain ⟨a,mem,strong,_⟩ := fixed_primitive_witness structural w Q
  refine ⟨a,mem,?_⟩
  calc (1/54:ℝ≥0∞) = (1/27)*(1/2) := by
         apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
         norm_num [ENNReal.toReal_div,ENNReal.toReal_mul]
       _ ≤ (1/27)*(27*a) := mul_le_mul' le_rfl (success.trans strong)
       _ = a := by rw [← mul_assoc,one_div,ENNReal.inv_mul_cancel (by norm_num) (by norm_num),one_mul]

theorem shake_half_witness (S : Sha2Set)
    (r : PublicKeyCore (ShakeSecurity.prims S).core → ProbComp (ShakeSecurity.prims S).Y)
    (seed : ProbComp (ShakeSecurity.prims S).PkSeed)
    (Q : QForger W (pureBytesAlg S.vp (ShakeSecurity.prims S) (ShakeSecurity.wireCodec S.vp.params) r seed))
    (success : 1/2 ≤ qStrongUnforgeableAdvantage Q) :
    ∃ a ∈ reducedAdvantages (qPureBytesToInternal Q), 1/54 ≤ a :=
  half_witness (ShakeSecurity.structural S) (by cases S <;> decide) Q success

theorem sha2_half_witness (S : Sha2Set)
    (r : PublicKeyCore S.prims.core → ProbComp S.prims.Y) (seed : ProbComp S.prims.PkSeed)
    (Q : QForger W (pureBytesAlg S.vp S.prims (MReduction.codec S) r seed))
    (success : 1/2 ≤ qStrongUnforgeableAdvantage Q) :
    ∃ a ∈ reducedAdvantages (qPureBytesToInternal Q), 1/54 ≤ a :=
  half_witness (MReduction.structural S) (by cases S <;> decide) Q success

/-- Concrete bit-security transfer for w=16. The hypothesis bounds the
advantages of the twelve primitive adversaries constructed from this forger.
A hardness estimate for a resource class can discharge it when that class
contains the reduction machines, including their signing-simulation work. -/
theorem fixed_hash_security_bits (structural : Structural vp prims) (w : vp.params.w = 16)
    (Q : QForger W (pureBytesAlg vp prims codec rand seeds)) (bits : ℕ)
    (hard : ∀ a ∈ reducedAdvantages (qPureBytesToInternal Q),
      a ≤ ((2 : ℝ≥0∞)^(bits+5))⁻¹) :
    qStrongUnforgeableAdvantage Q ≤ ((2 : ℝ≥0∞)^bits)⁻¹ ∧
    qUnforgeableAdvantage Q ≤ ((2 : ℝ≥0∞)^bits)⁻¹ := by
  obtain ⟨a, mem, strong, ordinary⟩ := fixed_primitive_witness structural w Q
  have transfer : 27*a ≤ ((2 : ℝ≥0∞)^bits)⁻¹ := calc
    27*a ≤ 32*((2 : ℝ≥0∞)^(bits+5))⁻¹ := mul_le_mul' (by norm_num) (hard a mem)
    _ = _ := by
      rw [pow_add, mul_comm ((2 : ℝ≥0∞)^bits), ENNReal.mul_inv (by simp) (by simp), ← mul_assoc]
      norm_num
      rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  exact ⟨strong.trans transfer, ordinary.trans transfer⟩

theorem shake_security_of_hash_security (S : Sha2Set)
    (r : PublicKeyCore (ShakeSecurity.prims S).core → ProbComp (ShakeSecurity.prims S).Y)
    (seed : ProbComp (ShakeSecurity.prims S).PkSeed)
    (Q : QForger W (pureBytesAlg S.vp (ShakeSecurity.prims S) (ShakeSecurity.wireCodec S.vp.params) r seed))
    (bits : ℕ) (hard : ∀ a ∈ reducedAdvantages (qPureBytesToInternal Q),
      a ≤ ((2 : ℝ≥0∞)^(bits+5))⁻¹) :
    qStrongUnforgeableAdvantage Q ≤ ((2 : ℝ≥0∞)^bits)⁻¹ ∧
    qUnforgeableAdvantage Q ≤ ((2 : ℝ≥0∞)^bits)⁻¹ :=
  fixed_hash_security_bits (ShakeSecurity.structural S) (by cases S <;> decide) Q bits hard

theorem sha2_security_of_hash_security (S : Sha2Set)
    (r : PublicKeyCore S.prims.core → ProbComp S.prims.Y) (seed : ProbComp S.prims.PkSeed)
    (Q : QForger W (pureBytesAlg S.vp S.prims (MReduction.codec S) r seed))
    (bits : ℕ) (hard : ∀ a ∈ reducedAdvantages (qPureBytesToInternal Q),
      a ≤ ((2 : ℝ≥0∞)^(bits+5))⁻¹) :
    qStrongUnforgeableAdvantage Q ≤ ((2 : ℝ≥0∞)^bits)⁻¹ ∧
    qUnforgeableAdvantage Q ≤ ((2 : ℝ≥0∞)^bits)⁻¹ :=
  fixed_hash_security_bits (MReduction.structural S) (by cases S <;> decide) Q bits hard

end Reduction
#print axioms Reduction.fixed_primitive_witness
#print axioms Reduction.shake_half_witness
#print axioms Reduction.sha2_half_witness
#print axioms Reduction.fixed_hash_security_bits
#print axioms Reduction.shake_security_of_hash_security
#print axioms Reduction.sha2_security_of_hash_security
