import MIdeal.Class128fBound
import MIdeal.Fors128fSignature
import MIdeal.Itsr128fSignature
import MIdeal.MsgPrf128fSignature
import MIdeal.Secret128fSignature

/-! Classical pure-byte EUF-CMA and SUF-CMA for SHA2-128f, with public queries to both shared ideal compression functions. -/
namespace MIdeal.Sha2_128f
open Ideal Ideal.Realize MLink SLHDSA SLHDSA.Security OracleComp OracleSpec Reduction Reduction.Open Ideal.Transport TweakableHash ENNReal
open Class128f (vp P)
open PureCompression (average)
attribute [local irreducible] wotsChainTargets wotsStepTargets wotsStepTargetsT Lazy.structSecIdx Lazy.sparseTable wotsInsts
noncomputable local instance (g : CompressionTables) : SampleableType (P g).Y := sampY128
local instance (g : CompressionTables) : SampleableType (P g).SkSeed := inferInstanceAs (SampleableType (Bytes 16))
local instance (g : CompressionTables) : SampleableType (P g).SkPrf := inferInstanceAs (SampleableType (Bytes 16))
local instance (g : CompressionTables) : Inhabited (P g).Y := inferInstanceAs (Inhabited (Bytes 16))
local instance (g : CompressionTables) : DecidableEq (P g).Y := inferInstanceAs (DecidableEq (Bytes 16))
local instance (g : CompressionTables) : DecidableEq (P g).PkSeed := inferInstanceAs (DecidableEq (Bytes 16))
local instance (g : CompressionTables) : DecidableEq (P g).AdrsKey := inferInstanceAs (DecidableEq (Bytes 22))
local instance (g : CompressionTables) : Fintype (P g).Y := inferInstanceAs (Fintype (Bytes 16))


private theorem average_mul (c : ℝ≥0∞) (f : CompressionTables → ℝ≥0∞) :
    average (fun g => c * f g) = c * average f := by
  unfold average
  simp only [cfAvg_mul_left]

private theorem average_one {f : CompressionTables → ℝ≥0∞} (h : ∀ g, f g ≤ 1) : average f ≤ 1 := by
  have bound {S B : Type} [SampleableType (CF S B)] :
      cfAvg (fun _ : CF S B => (1:ℝ≥0∞)) ≤ 1 := by
    let _ : MeasurableSpace (CF S B) := ⊤
    unfold cfAvg
    rw [MeasureTheory.lintegral_const]
    exact mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)
  apply (cfAvg_mono (fun d => (cfAvg_mono (fun c => h (c,d))).trans bound)).trans bound
private theorem combine
    {adv r1 i1 a1 r2 i2 a2 c c' Ds S dv T T' X X' n R I aU p p' t t' : ℝ≥0∞}
    (h1 : r1 ≤ i1 + a1) (h2 : r2 ≤ i2 + a2) (h3 : Ds ≤ S + dv) (h4 : R ≤ I + aU)
    (hc : c ≤ c') (hT : T ≤ T') (hX : X ≤ X') (hp : p ≤ p') (ht : t ≤ t')
    (hfin : i1 + i2 + S + n * I ≠ ⊤)
    (h : adv + (i1 + i2 + S + n * I) ≤ r1 + r2 + c + (Ds + 3 * T) + X + n * R + p + t) :
    adv ≤ a1 + a2 + c' + (dv + 3 * T') + X' + n * aU + p' + t' := by
  have h' : adv + (i1 + i2 + S + n * I) ≤
      (a1 + a2 + c' + (dv + 3 * T') + X' + n * aU + p' + t') + (i1 + i2 + S + n * I) :=
    calc adv + (i1 + i2 + S + n * I)
        ≤ r1 + r2 + c + (Ds + 3 * T) + X + n * R + p + t := h
      _ ≤ (i1 + a1) + (i2 + a2) + c' + ((S + dv) + 3 * T') + X' + n * (I + aU) + p' + t' := by
          gcongr
      _ = _ := by ring
  exact (ENNReal.add_le_add_iff_right hfin).1 h'


noncomputable def loss (q qs L : ℕ) : ℝ≥0∞ :=
  Secret128f.loss q qs L + Msg128f.loss q qs L + Itsr128f.loss q qs L +
    (Fors128f.dsprLoss + 3*Fors128f.tcrLoss q qs L) +
    (Class128f.classLoss 1 q qs L + Class128f.classLoss 2 q qs L +
       Class128f.classLoss vp.params.len q qs L + Class128f.classLoss vp.params.k q qs L) +
    ((vp.params.w-2 : ℕ) : ℝ≥0∞)*Wots128f.udLoss q qs L + Wots128f.preLoss q qs L + Wots128f.tcrLoss q qs L

variable (rand : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (seeds : ProbComp (Bytes 16)) (A : PureCompression.Forger)
variable (q qs L : ℕ)
    (hq : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained isPortQP i = true) q)
    (hs : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained isSignQP i = true) qs)
    (hl : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained (isLongQP L) i = true) 0)
    (ho : ∀ pk z, z ∈ support (A.main pk) → z.1.1.length ≤ L)


set_option maxRecDepth 8192 in
include hq hs hl ho in
theorem suf (hcap : 4*Fors128f.budget q qs L ≤ 2^128) :
    average (fun g => SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp
      (PureCompression.strong Sha2Set.s128f rand seeds A g)) ≤ loss q qs L := by
  have lin := PureCompression.suf_internal_linear Sha2Set.s128f rand seeds A
  dsimp only [linRealSuf,linIdealSuf,linearRealSide,linearIdealSide] at lin
  simp only [PureCompression.average_add,average_mul] at lin
  have prf := Secret128f.term rand A seeds true hq hs hl ho
  have msg := Msg128f.term rand A seeds q qs L true hq hs hl ho
  have ds := Fors128f.dspr_term rand A seeds q qs L hq hs hl ho hcap
  have ft := Fors128f.tcr_term rand A seeds q qs L hq hs hl ho
  have it := Itsr128f.term rand A seeds q qs L hq hs hl ho
  have wu := Wots128f.ud_term rand A seeds q qs L hq hs hl ho
  have wp := Wots128f.pre_term rand A seeds q qs L hq hs hl ho
  have wt := Wots128f.tcr_term rand A seeds q qs L hq hs hl ho
  have cl (n : ℕ) := Class128f.class_term rand A seeds n q qs L hq hs hl ho
  let R g := Wots128f.reduced rand A seeds g
  have i1 := average_one (fun g => prfIdealPr_le_one (vp := vp) (prims := P g) (Secret128f.adversary rand A seeds true g))
  have i2 := average_one (fun g => msgIdealPr_le_one (prims := P g) (Msg128f.adversary rand A seeds true g))
  have id := average_one (fun g => dsprSPProbability_le_one (toDspr (Lazy.bOpenPreS (R g))))
  have iu := average_one (fun g => udIdealSuccess_le_one (rUd (prims := P g) seeds (Lazy.bWotsS (R g))))
  have cls := add_le_add (add_le_add (add_le_add (cl 1) (cl 2)) (cl vp.params.len)) (cl vp.params.k)
  let n : ℝ≥0∞ := ((vp.params.w-2 : ℕ) : ℝ≥0∞)
  have hfin := ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
    ⟨(i1.trans_lt ENNReal.one_lt_top).ne, (i2.trans_lt ENNReal.one_lt_top).ne⟩,
    (id.trans_lt ENNReal.one_lt_top).ne⟩, ENNReal.mul_ne_top (a := n) (ENNReal.natCast_ne_top _) (iu.trans_lt ENNReal.one_lt_top).ne⟩
  exact combine prf msg ds wu it ft cls wp wt hfin lin

include hq hs hl ho in
theorem euf (hcap : 4*Fors128f.budget q qs L ≤ 2^128) :
    average (fun g => SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp
      (PureCompression.strong Sha2Set.s128f rand seeds A g).toUnforgeableAdversary) ≤ loss q qs L :=
  (PureCompression.average_mono fun g => SignatureAlg.unforgeableAdvantage_le_strongUnforgeableAdvantage _
    (PureCompression.strong Sha2Set.s128f rand seeds A g).toUnforgeableAdversary).trans (suf rand seeds A q qs L hq hs hl ho hcap)
end MIdeal.Sha2_128f
#print axioms MIdeal.Sha2_128f.suf
#print axioms MIdeal.Sha2_128f.euf
