import Integration.SlhDsaSetOracle
import Integration.SlhDsaBridgeInd

namespace Reduction.SetOracle

open SLHDSA SLHDSA.Security MLink OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open scoped ComplexOrder Kronecker

variable (S : Sha2Set) (c : Caps)
abbrev KeyTable := S.Node × (S.Node × Bytes 22) → S.Node

def replaceKey (g : FinFns S.vp.params c) (t : KeyTable S) : FinFns S.vp.params c :=
  g.withPrf (fun pk sk a => t (sk, pk, a))

/-- A uniformly sampled component can be resampled inside the average if swapping
the old and fresh values is an involution on the product space. -/
theorem avg_resample {Ω T : Type} [Fintype Ω] [Fintype T] [Nonempty T]
    (replace : Ω → T → Ω) (read : Ω → T)
    (hswap : Function.Involutive (fun z : Ω × T => (replace z.1 z.2, read z.1)))
    (f : Ω → ℝ≥0∞) :
    (∑ g, unifW _ g * f g) = ∑ g, unifW _ g * ∑ t, unifW _ t * f (replace g t) := by
  classical
  have eq := Equiv.sum_comp hswap.toPerm fun z : Ω × T => f z.1
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Function.Involutive.coe_toPerm] at eq
  unfold unifW
  let n : ℝ≥0∞ := Fintype.card T
  have h0 : n ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have ht : n ≠ ⊤ := ENNReal.natCast_ne_top _
  simp only [← Finset.mul_sum]
  congr 1
  change _ = n⁻¹ * _
  rw [eq, ← Finset.mul_sum, ← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]

private theorem avg_replace (f : FinFns S.vp.params c → ℝ≥0∞) :
    (∑ g, unifW _ g * f g) = ∑ g, unifW _ g *
      ∑ t : KeyTable S, unifW _ t * f (replaceKey S c g t) :=
  avg_resample (replaceKey S c) (fun g (sk,pk,a) => g.prf pk sk a)
    (by rintro ⟨⟨_,_,_,_⟩,_⟩; rfl) f

private def prfKeyAt (d : S.Node × SkAdrs S.vp) := (d.1, Concrete.sha2AdrsKey d.2.val)

variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
  {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (Input S c) (Output S) E)

noncomputable abbrev keyMachine (g : FinFns S.vp.params c) (H : Input S c → Output S) :=
  qbPrfWC sufCheck (qPureBytesToInternal (F.at H (scheme S c rand seeds g)))

/-- The actual PRF term of the strong signature reduction at every SHA-2 set,
with only the forger's own port calls charged. -/
theorem suf_key_prf (q : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q) :
    (∑ g, unifW _ g * qPrfRealPr (skPrfC S.vp (randPrims g.toRand))
      (keyMachine S c rand seeds F g (oracle S g)) F.ρ₀) ≤
    (∑ g, unifW _ g * qPrfIdealPr (keyMachine S c rand seeds F g (oracle S g)) F.ρ₀) +
      ENNReal.ofReal (8 * (q : ℝ)^2 / 2^(8*S.vp.params.n)) := by
  have indep (g : FinFns S.vp.params c) (t : KeyTable S) (H : Input S c → Output S) :
      keyMachine S c rand seeds F (replaceKey S c g t) H = keyMachine S c rand seeds F g H :=
    QInd.qbPrfWC_setPrf (prims := randPrims g.toRand)
      (fun pk sk a => t (sk,pk,Concrete.sha2AdrsKey a)) (codecFor S g.toRand)
      (fun pk => rand pk.pkSeed pk.pkRoot) (fun pk => rand pk.pkSeed pk.pkRoot)
      (fun _ => rfl) seeds (F.at H (scheme S c rand seeds g))
  have hp (g : FinFns S.vp.params c) : PU (keyMachine S c rand seeds F g) q := by
    apply pu_qbPrfWC
    intro pk
    exact PU.map _ (PU.wrap0 _ (PU.map _ (PU.wrap0 _ (PU.compileQ _ q (hq _)))))
  have hk : Function.Injective (prfKeyAt S) := by
    rintro ⟨pk,a⟩ ⟨pk',b⟩ h
    obtain ⟨h1,h2⟩ := Prod.mk.inj h
    exact Prod.ext h1 (Subtype.ext ((MReduction.structural S).keyInj a.property.addressFacts b.property.addressFacts h2))
  have hscheme (g : FinFns S.vp.params c) (t : KeyTable S) :
      skPrfC S.vp (randPrims (replaceKey S c g t).toRand) = keyedScheme (prfKeyAt S) t := rfl
  obtain ⟨ρ, hρ⟩ := exists_subState F.ρ₀ F.posSemidef F.trace_eq_one
  let loc : Input S c → Option (S.Node × (S.Node × Bytes 22))
    | .inr (.inr (.inl x)) => some (x.2.1, x.1, x.2.2)
    | _ => none
  have localTable (g : FinFns S.vp.params c) (t t' : KeyTable S) (x : Input S c)
      (h : ∀ i, loc x = some i → t i = t' i) :
      oracle S (replaceKey S c g t) x = oracle S (replaceKey S c g t') x := by
    rcases x with x | x | x | x
    · rfl
    · rfl
    · exact congrArg (fun v => (v,0)) (h _ rfl)
    · rfl
  have hh (g : FinFns S.vp.params c) := prf_PU_real_le_ideal_add (prfKeyAt S) hk
    (keyMachine S c rand seeds F g) q (hp g) (fun t => oracle S (replaceKey S c g t)) loc
    (localTable g) ρ
  rw [avg_replace S c (fun g => qPrfRealPr _ (keyMachine S c rand seeds F g (oracle S g)) _),
    avg_replace S c (fun g => qPrfIdealPr (keyMachine S c rand seeds F g (oracle S g)) _)]
  simp only [hscheme, indep, hρ]
  have card : (Fintype.card S.Node : ℝ) = 2^(8*S.vp.params.n) := by
    rw [card_bytes', Nat.cast_pow, Nat.cast_ofNat, pow_mul]
    norm_num
  rw [← card]
  calc _ ≤ ∑ g, unifW _ g * (_ + ENNReal.ofReal (8 * (q : ℝ)^2 / Fintype.card S.Node)) :=
          Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl (hh g)
       _ = _ := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_unifW, one_mul]
          rfl

end Reduction.SetOracle

#print axioms Reduction.SetOracle.suf_key_prf
