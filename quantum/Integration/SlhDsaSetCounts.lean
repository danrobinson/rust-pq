import Integration.SlhDsaComposedClosedNum
import MReduction.Explicit

namespace Reduction

open SLHDSA MLink ENNReal

/-- Each field counts the reduction's own hash evaluations in the component QROM.
The two PRF games charge the forger's queries directly. -/
def componentCounts (vp : ValidatedParams) (qs : ℕ) : RedCounts where
  prf := 0
  msg := 0
  itsr := itsrHashes vp qs
  dspr := forsMHashes vp qs
  tcrFv := forsMHashes vp qs
  tcr1 := tcrMHashes vp qs
  tcr2 := tcrMHashes vp qs
  tcrLen := tcrMHashes vp qs
  tcrK := tcrMHashes vp qs
  ud := qmWotsUdHashes vp qs
  pre := qmWotsPreHashes vp qs
  tcrT := qmWotsTcrTHashes vp qs

theorem componentCounts_128s (qs : ℕ) :
    componentCounts Sha2Set.s128s.vp qs = (openCounts128s qs).noPrfMsg := by
  change componentCounts Link.vp qs = _
  unfold componentCounts
  rw [itsrHashes_openCounts128s, (forsMHashes_openCounts128s _).1,
    (tcrMHashes_openCounts128s _).1, qmWotsUdHashes_openCounts128s,
    qmWotsPreHashes_openCounts128s, qmWotsTcrTHashes_openCounts128s]
  rfl

theorem componentCounts_128s_num :
    composedBoundFinal (2^40) (2^20) (componentCounts Sha2Set.s128s.vp (2^20)) ≤
      ((2 : ℝ≥0∞) ^ 22)⁻¹ := by
  rw [componentCounts_128s]
  exact Num.composedBoundFinal_num

end Reduction

#print axioms Reduction.componentCounts_128s_num
