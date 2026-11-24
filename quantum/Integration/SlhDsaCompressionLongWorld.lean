import Integration.SlhDsaCompressionLongMap
import Integration.SlhDsaCompressionShortBlocks
namespace Reduction.Compression.LongClass
open MLink Ideal Ideal.HP Ideal.MP2 Recording.Database Recording.Compile Recording.Compile.LeftPort
open SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal Classical
open HiddenWeight (mean)
set_option linter.unusedSectionVars false

def programmed (pk : Wots256.Node) (cv : St) (c : Partial St Blk) (raw : CF St Blk) : CF St Blk := fun x =>
  if x = (IV128,sb128 pk) then cv else (c (tag cv x)).getD (raw x)

noncomputable def mapping (pk : Wots256.Node) (cv : St) (c : Partial St Blk) (b : CF Chain512 Block512) :
    Response.Mapping
  | .inl x, y => (if x = (IV128,sb128 pk) then cv else (c (tag cv x)).getD (halves y).1,0)
  | .inr x, _ => (0,arrayVectorEquivFin UInt64 8 (b x))

theorem port_world (pk : Wots256.Node) (cv : St) (c : Partial St Blk) (b : CF Chain512 Block512) (h : Full) :
    Response.project (LongClass.mapping pk cv c b) h = oracle (programmed pk cv c (projectTable h),b) := by
  funext x
  cases x <;> rfl

theorem programmed_rows (pk : Wots256.Node) (cv : St) (c : Partial St Blk) (g : CF St Blk) (t : Blk → St) :
    programmed pk cv c (rowRep g cv t) = gstar IV128 (sb128 pk) cv
      (fun x => (c (.inl x)).getD (g x)) (fun b => (c (.inr b)).getD (t b)) := by
  funext x
  by_cases seed : x = (IV128,sb128 pk) <;> by_cases row : x.1 = cv <;>
    simp [programmed,tag,gstar,rowRep,seed,row]

private theorem row_swap (cv : St) (z : CF St Blk × (Blk → St)) :
    (rowRep (rowRep z.1 cv z.2) cv (fun b => z.1 (cv,b)),fun b => rowRep z.1 cv z.2 (cv,b)) = z := by
  apply Prod.ext
  · funext x
    rcases x with ⟨s,b⟩
    by_cases e : s = cv <;> simp [rowRep,e]
  · funext b
    simp [rowRep]

theorem mean_rows (cv : St) (f : CF St Blk → ℝ≥0∞) :
    mean ($ᵗ (CF St Blk)) (fun g => mean ($ᵗ (Blk → St)) (fun t => f (rowRep g cv t))) =
      ∑ h : Full, unifW _ h * f (projectTable h) := by
  exact (Wots256.swapMean f (fun g t => rowRep g cv t) (fun g b => g (cv,b)) (row_swap cv)).symm.trans
    ((Wots256.explicitMean f).trans (LeftPort.mean f).symm)

noncomputable def freshRate (N Q : ℕ) : ℝ :=
  ((2:ℝ)^128)⁻¹ + ((2*(N+(Q+2))+3 : ℕ):ℝ) / 2^256

theorem failure_growth (seeds : ProbComp Wots256.Node) (ar n : ℕ) (cv : St) (c : Partial St Blk)
    (ts : List (Bytes 22 × ShortBlocks.Msg ar)) (N Q : ℕ)
    (hg : Good (ShortBlocks.family seeds ar n) btw128 ((22+16*ar+8)/64) ts cv c)
    (fin : CFin c N) (tw : ∀ t a b, (t,a) ∈ ts → (t,b) ∈ ts → a=b) (t : ℕ) (ht : t ≤ Q) :
    Growth (fun d : Cells => ¬Good (ShortBlocks.family seeds ar n) btw128 ((22+16*ar+8)/64)
      ts cv (extend c (records cv d))) t (freshRate N Q) := by
  refine growth_records cv (fun d => ¬Good (ShortBlocks.family seeds ar n) btw128 _ ts cv (extend c d)) t (freshRate N Q) (by unfold freshRate; positivity) ?_
  have gr := good_growth (ShortBlocks.family seeds ar n) btw128 _ ts cv c N (Q+1) fin hg tw
    (((2:ℝ≥0∞)^128)⁻¹) (by finiteness) (fun y => (prEvent_out16_eq y).le)
  constructor
  · exact gr.mono
  · intro x r sz ok
    have h := gr.fresh x r (sz.trans (Nat.succ_le_succ ht)) ok
    simpa only [freshRate,ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
      card_St,Nat.cast_pow,Nat.cast_ofNat,Nat.add_assoc] using h

end Reduction.Compression.LongClass
#print axioms Reduction.Compression.LongClass.mean_rows
#print axioms Reduction.Compression.LongClass.failure_growth
