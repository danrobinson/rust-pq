import Integration.SlhDsaSetPrf
import Integration.SlhDsaBridgeMsg

namespace Reduction.SetOracle

open SLHDSA SLHDSA.Security MLink OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open QMsg
open scoped ComplexOrder Kronecker

variable (S : Sha2Set) (c : Caps)
abbrev MessageDomain := S.Node × BList Byte c.ml

def restrictMessage (d : S.Node × List Byte) : Option (MessageDomain S c) :=
  if h : d.2.length ≤ c.ml then some (d.1, BList.ofList d.2 h) else none

private theorem restrict_inj (d₁ d₂ : S.Node × List Byte) (z : MessageDomain S c)
    (h₁ : restrictMessage S c d₁ = some z) (h₂ : restrictMessage S c d₂ = some z) : d₁ = d₂ := by
  unfold restrictMessage at h₁ h₂
  split_ifs at h₁ h₂ with e₁ e₂
  cases h₁
  obtain ⟨a,b⟩ := d₁
  obtain ⟨a',b'⟩ := d₂
  obtain ⟨h,h'⟩ := Prod.mk.inj (Option.some.inj h₂)
  have hb := congrArg (fun x : BList Byte c.ml => List.ofFn x.2) h'.symm
  exact Prod.ext h.symm (by simpa only [BList.ofFn_ofList] using hb)

abbrev MessageTable := S.Node × MessageDomain S c → S.Node

def replaceMessage (g : FinFns S.vp.params c) (t : MessageTable S c) :=
  g.withPrfMsg (fun sk r m => t (sk,r,m))

def readMessage (g : FinFns S.vp.params c) : MessageTable S c := fun (sk,r,m) => g.prfMsg sk r m

variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
  {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (Input S c) (Output S) E)

noncomputable abbrev msgMachine (g : FinFns S.vp.params c) (H : Input S c → Output S) :=
  qbPrfMsgWL sufCheck (qPureBytesToInternal (F.at H (scheme S c rand seeds g)))

/-- All-set message PRF term for a quantum strong forger making classical, in-cap signing requests. -/
theorem suf_msg_prf (q : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    (∑ g, unifW _ g * qPrfRealPr (msgPrf S.vp (randPrims g.toRand))
      (msgMachine S c rand seeds F g (oracle S g)) F.ρ₀) ≤
    (∑ g, unifW _ g * qPrfIdealPr (msgMachine S c rand seeds F g (oracle S g)) F.ρ₀) +
      ENNReal.ofReal (8 * (q : ℝ)^2 / 2^(8*S.vp.params.n)) := by
  let mach := msgMachine S c rand seeds F
  let res := restrictMessage S c
  let short := fun g H => wrap0 (Restrict.restrictImpl res) (mach g H)
  have hpu (g) : PU (short g) q := by
    apply PU.wrap0
    unfold mach msgMachine qbPrfMsgWL qLazyRun qMsgOpenW qRunForgerSig
    refine PU.wrap0 _ (PU.map _ (PU.wrap _ ?_ []))
    refine PU.liftQ_bind _ fun pkSeed => PU.liftQ_bind _ fun root => ?_
    refine PU.bind (q₂ := 0) (PU.wrap _ ?_ []) fun z => PU.liftQ _ 0
    exact PU.map _ (PU.wrap0 _ (PU.map _ (PU.wrap0 _ (PU.compileQ _ q (hq _)))))
  have hind (g t H) : short (replaceMessage S c g t) H = short g H := by
    apply congrArg (wrap0 (Restrict.restrictImpl res))
    exact QMsg.qbPrfMsgWL_setPrf (prims := randPrims g.toRand) (randPrims g.toRand).PRF
      (fun sk r m => if h : m.length ≤ c.ml then t (sk,r,BList.ofList m h) else default)
      (codecFor S g.toRand) (fun pk => rand pk.pkSeed pk.pkRoot) (fun pk => rand pk.pkSeed pk.pkRoot)
      (fun _ => rfl) seeds (F.at H (scheme S c rand seeds g))
  have hr (g) : qPrfRealPr (msgPrf S.vp (randPrims g.toRand)) (mach g (oracle S g)) F.ρ₀ =
      qPrfRealPr (keyedScheme id (readMessage S c g)) (short g (oracle S g)) F.ρ₀ := by
    apply qPrfRealPr_restrict res _ _ rfl
    rintro k ⟨r,m⟩
    by_cases h : m.length ≤ c.ml
    · simp [res, restrictMessage, h, msgPrf, msgPrfScheme, keyedScheme, readMessage, FinFns.toRand]
    · simp [res, restrictMessage, h, msgPrf, msgPrfScheme, FinFns.toRand]
  have hi (g) : qPrfIdealPr (mach g (oracle S g)) F.ρ₀ = qPrfIdealPr (short g (oracle S g)) F.ρ₀ := by
    apply qPrfIdealPr_restrict res (restrict_inj S c)
    have hall := allQ_qLazyRun (W := WS (Input S c) (Output S) E) (PublicHash.impl (randPrims g.toRand))
      (fun d : S.Node × List Byte => d.2.length ≤ c.ml) _
      (allQ_qMsgOpenW (randPrims g.toRand) c.ml sufCheck
        (qPureBytesToInternal (forgerAt S c rand seeds F g))
        (allQ_qPureBytesToInternal c.ml _ fun pk => allQ_compileQ c _ (F.main pk) (hcap pk)))
    refine allQ_mono ?_ (fun _ _ => trivial) hall
    rintro (j | n | d) ht
    · trivial
    · trivial
    · have hd : d.2.length ≤ c.ml := ht
      change (restrictMessage S c d).isSome
      simp [restrictMessage, hd]
  change (∑ g, _ * qPrfRealPr _ (mach g _) _) ≤ (∑ g, _ * qPrfIdealPr (mach g _) _) + _
  simp_rw [hr, hi]
  have resample := avg_resample (replaceMessage S c) (readMessage S c)
    (by rintro ⟨⟨_,_,_,_⟩,_⟩; rfl)
  rw [resample (fun g => qPrfRealPr _ (short g (oracle S g)) _),
      resample (fun g => qPrfIdealPr (short g (oracle S g)) _)]
  have read_replace (g t) : readMessage S c (replaceMessage S c g t) = t := rfl
  simp only [read_replace, hind]
  let loc : Input S c → Option (S.Node × MessageDomain S c)
    | .inr (.inr (.inr x)) => some x
    | _ => none
  have locality g (t t' : MessageTable S c) (x) (h : ∀ i, loc x = some i → t i = t' i) :
      oracle S (replaceMessage S c g t) x = oracle S (replaceMessage S c g t') x := by
    rcases x with x | x | x | x
    · rfl
    · rfl
    · rfl
    · exact congrArg (fun v => (v,0)) (h _ rfl)
  obtain ⟨ρ,hρ⟩ := exists_subState F.ρ₀ F.posSemidef F.trace_eq_one
  rw [hρ]
  have hcard : (Fintype.card S.Node : ℝ) = 2^(8*S.vp.params.n) := by
    rw [card_bytes', Nat.cast_pow, Nat.cast_ofNat, pow_mul]
    norm_num
  rw [← hcard]
  calc _ ≤ ∑ g, unifW _ g * (_ + ENNReal.ofReal (8 * (q : ℝ)^2 / Fintype.card S.Node)) :=
          Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl
            (prf_PU_real_le_ideal_add (K := S.Node) (Dm := MessageDomain S c) (R := S.Node)
              id Function.injective_id (short g) q (hpu g)
              (fun t => oracle S (replaceMessage S c g t)) loc (locality g) ρ)
       _ = _ := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_unifW, one_mul]
          rfl

set_option maxHeartbeats 1000000 in
/-- Remove both PRF games from the six-set linear security reduction. The remaining
terms are the ITSR, FORS, class-TCR and WOTS games. -/
theorem suf_after_prfs (q : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    (∑ g, unifW _ g * qStrongUnforgeableAdvantage (forgerAt S c rand seeds F g)) +
    (∑ g, unifW _ g *
      qLinearIdealSideG (qPureBytesToInternal (forgerAt S c rand seeds F g)) 0 0) ≤
    2 * ENNReal.ofReal (8 * (q : ℝ)^2 / 2^(8*S.vp.params.n)) +
    ∑ g, unifW _ g * qLinearRealSideG (qPureBytesToInternal (forgerAt S c rand seeds F g)) 0 0 := by
  let B := fun g => qPureBytesToInternal (forgerAt S c rand seeds F g)
  let R₁ := fun g => qPrfRealPr (skPrfC S.vp (randPrims g.toRand)) (qbPrfWC sufCheck (B g)) F.ρ₀
  let R₂ := fun g => qPrfRealPr (msgPrf S.vp (randPrims g.toRand)) (qbPrfMsgWL sufCheck (B g)) F.ρ₀
  let I₁ := fun g => qPrfIdealPr (qbPrfWC sufCheck (B g)) F.ρ₀
  let I₂ := fun g => qPrfIdealPr (qbPrfMsgWL sufCheck (B g)) F.ρ₀
  let avg (f : FinFns S.vp.params c → ℝ≥0∞) := ∑ g, unifW _ g * f g
  let err := ENNReal.ofReal (8 * (q : ℝ)^2 / 2^(8*S.vp.params.n))
  have hadd (f h : FinFns S.vp.params c → ℝ≥0∞) :
      avg (fun g => f g + h g) = avg f + avg h := by
    simp only [avg, mul_add, Finset.sum_add_distrib]
  have hreal (g) : qLinRealSufG (B g) = (R₁ g + R₂ g) + qLinearRealSideG (B g) 0 0 := by
    simp only [qLinRealSufG, qLinearRealSideG, R₁, R₂, zero_add, add_assoc]
    rfl
  have hideal (g) : qLinIdealSufG (B g) = (I₁ g + I₂ g) + qLinearIdealSideG (B g) 0 0 := by
    simp only [qLinIdealSufG, qLinearIdealSideG, I₁, I₂, zero_add, add_assoc]
    rfl
  have h := suf_linear S c rand seeds F
  change _ + avg (fun g => qLinIdealSufG (B g)) ≤ avg (fun g => qLinRealSufG (B g)) at h
  simp_rw [hreal, hideal] at h
  rw [hadd, hadd, hadd, hadd] at h
  have hr : avg R₁ + avg R₂ ≤ (avg I₁ + err) + (avg I₂ + err) :=
    add_le_add (suf_key_prf S c rand seeds F q hq) (suf_msg_prf S c rand seeds F q hq hc)
  have fin (f : FinFns S.vp.params c → ℝ≥0∞) (hf : ∀ g, f g ≤ 1) : avg f ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun g _ => ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)) (ne_top_of_le_ne_top one_ne_top (hf g))
  have hfin : avg I₁ + avg I₂ ≠ ⊤ := ENNReal.add_ne_top.2
    ⟨fin I₁ (fun g => qPrfIdealPr_le_one' _ F.posSemidef F.trace_eq_one),
     fin I₂ (fun g => qPrfIdealPr_le_one' _ F.posSemidef F.trace_eq_one)⟩
  apply (ENNReal.add_le_add_iff_right hfin).1
  let success := avg (fun g => qStrongUnforgeableAdvantage (forgerAt S c rand seeds F g))
  let idealRest := avg (fun g => qLinearIdealSideG (B g) 0 0)
  let realRest := avg (fun g => qLinearRealSideG (B g) 0 0)
  change success + idealRest + (avg I₁ + avg I₂) ≤ 2 * err + realRest + (avg I₁ + avg I₂)
  calc _ = success + (avg I₁ + avg I₂ + idealRest) := by ac_rfl
       _ ≤ (avg I₁ + err + (avg I₂ + err)) + realRest := h.trans (add_le_add hr le_rfl)
       _ = _ := by rw [two_mul]; ac_rfl

end Reduction.SetOracle

#print axioms Reduction.SetOracle.suf_msg_prf
#print axioms Reduction.SetOracle.suf_after_prfs
