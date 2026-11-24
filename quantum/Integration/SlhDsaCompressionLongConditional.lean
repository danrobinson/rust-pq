import Integration.SlhDsaCompressionLongWorld
import Integration.SlhDsaCompressionLongCertificate
import Integration.SlhDsaCompressionLongReadout

namespace Reduction.Compression.LongClass
open MLink Ideal Ideal.HP Ideal.MP2 Recording.Database Recording.Compile Recording.Compile.LeftPort
open SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal Classical
open HiddenWeight (mean)
open scoped ComplexOrder
set_option linter.unusedSectionVars false
variable (seeds : ProbComp Wots256.Node) (ar n : ℕ) (pk : Wots256.Node) (cv : St) (c : Partial St Blk)
variable (ts : List (Bytes 22 × ShortBlocks.Msg ar))
local notation "L₀" => (22+16*ar+8)/64
local notation "fam" => ShortBlocks.family seeds ar n
local notation "rep" => Certificate.report seeds ar n pk cv c
local notation "normT" => Certificate.normalized IV128 (sb128 pk) cv c
abbrev Receipt := Bool × List (Left × St)
private def accepted (z : Receipt) : Prop := z.1 = true ∧
  ∃ g T jm, z = rep g T ts jm
private def log (m : ℕ) (z : Receipt) := z.2.take m

private theorem certificate_fails (hcv : cv ≠ IV128) (z : Receipt) (d : Cells)
    (ok : accepted seeds ar n pk cv c ts z)
    (seen : ∀ p ∈ log (2*(L₀+1)) z, ∃ y, d (.inl p.1)=some y ∧ (halves y).1=p.2) :
    ¬Good fam btw128 L₀ ts cv (extend c (records cv d)) := by
  obtain ⟨win,g,T,jm,rfl⟩ := ok
  have small := Certificate.report_length seeds ar n pk cv c g T ts jm
  apply Certificate.bad_of_report seeds ar n pk cv c g T ts hcv (base_le c _) jm win
  intro p v hm
  obtain ⟨_,absent,_⟩ := Certificate.report_fresh seeds ar n pk cv c g T ts jm hm
  have mem : (p,v) ∈ log (2*(L₀+1)) (rep g T ts jm) := by simpa only [log,List.take_of_length_le small] using hm
  obtain ⟨y,hy,eq⟩ := seen (p,v) mem
  change extend c (records cv d) (tag cv p) = some v
  change c (tag cv p) = none at absent
  simpa only [extend,absent,Option.none_or,recorded_at,hy,Option.map_some,Option.some.injEq] using eq

private theorem row_self (g : CF St Blk) : rowRep g cv (fun b => g (cv,b)) = g := by
  funext x
  rcases x with ⟨s,b⟩
  by_cases e : s=cv <;> simp [rowRep,e]

private theorem normal_raw (g : CF St Blk) :
    normT g (fun b => g (cv,b)) = programmed pk cv c g :=
  (programmed_rows pk cv c g _).symm.trans (congrArg (programmed pk cv c) (row_self cv g))

private theorem on_rows (U : CF St Blk) (V : Blk → St) (jm : ℕ × ShortBlocks.Msg ar) :
    rep (rowRep U cv V) (fun b => rowRep U cv V (cv,b)) ts jm = rep U V ts jm := by
  unfold Certificate.report
  rw [normal_raw,programmed_rows]
  rfl

noncomputable def endLoss (N q m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2*(m:ℝ)*Real.sqrt ((2^256:ℝ)⁻¹)+(q:ℝ)*(4*Real.sqrt (freshRate N q)))^2)

variable {W : Type} [Fintype W] [DecidableEq W]
variable (mach : (Input → Output) → Closed (WS Input Output W) (ℕ × ShortBlocks.Msg ar))
variable (ρ : Matrix (WS Input Output W) (WS Input Output W) ℂ)
private def monitor (H : Input → Output) :=
  rep (tablesOf H).1 (fun b => (tablesOf H).1 (cv,b)) ts <$> mach H

private theorem monitor_cost (q : ℕ) (hq : PUE (spec := unifSpec) cnt0 mach q) :
    PUE (spec := unifSpec) cnt0 (monitor seeds ar n pk cv c ts mach) (q+2*(L₀+1)) := by
  unfold monitor
  simp only [map_eq_bind_pure_comp,Function.comp_def]
  exact
    Certificate.report_pue seeds ar n pk cv c ts mach q hq

set_option maxRecDepth 8192 in
private theorem world (b : CF Chain512 Block512) (h : Full) :
    qWeight (fun jm => (rep (projectTable h) (fun B => projectTable h (cv,B)) ts jm).1=true)
      (mach (oracle (programmed pk cv c (projectTable h),b))) ρ ≤
    qWeight (fun z => accepted seeds ar n pk cv c ts z ∧ ∀ p ∈ log (2*(L₀+1)) z, projectTable h p.1 = p.2)
      (monitor seeds ar n pk cv c ts mach (Response.project (LongClass.mapping pk cv c b) h)) ρ := by
  classical
  let g := projectTable h
  let T := fun B => g (cv,B)
  rw [port_world,monitor,qWeight_map,tablesOf_oracle]
  apply qWeight_mono
  intro jm win
  change accepted seeds ar n pk cv c ts (rep (programmed pk cv c g) (fun B => programmed pk cv c g (cv,B)) ts jm) ∧ _
  rw [← normal_raw pk cv c g,Certificate.report_normalized]
  refine ⟨⟨win,g,T,jm,rfl⟩,?_⟩
  intro p hp
  have m : p ∈ (rep g T ts jm).2 := List.mem_of_mem_take hp
  have read := Certificate.report_physical seeds ar n pk cv c g T ts jm (p := p.1) (v := p.2) m
  simpa only [T,row_self] using read

set_option maxRecDepth 8192 in
/-- Conditional phase-two bound for a physically shared SHA-256 compression
table, with the target list and honest cache fixed at the end of phase one. -/
theorem conditional (b : CF Chain512 Block512) (N q : ℕ) (hg : Good fam btw128 L₀ ts cv c)
    (fin : CFin c N) (tw : ∀ t a b, (t,a) ∈ ts → (t,b) ∈ ts → a=b) (hcv : cv ≠ IV128)
    (hq : PUE (spec := unifSpec) cnt0 mach q) (hp : ρ.PosSemidef) (ht : ρ.trace=1) :
    mean ($ᵗ (CF St Blk)) (fun U => mean ($ᵗ (Blk → St)) (fun V =>
      qWeight (fun jm => (rep U V ts jm).1=true) (mach (oracle (normT U V,b))) ρ)) ≤
        endLoss N (q+2*(L₀+1)) (2*(L₀+1)) := by
  classical
  let m := 2*(L₀+1)
  let Q := q+m
  let f := fun g : CF St Blk => qWeight (fun jm => (rep g (fun B => g (cv,B)) ts jm).1=true)
    (mach (oracle (programmed pk cv c g,b))) ρ
  have left (U : CF St Blk) (V : Blk → St) : f (rowRep U cv V) =
      qWeight (fun jm => (rep U V ts jm).1=true) (mach (oracle (normT U V,b))) ρ := by
    simp only [f,on_rows,programmed_rows,Certificate.normalized]
  simp_rw [← left]
  rw [mean_rows]
  apply le_trans (Finset.sum_le_sum fun h _ => mul_le_mul' (a := unifW _ h) le_rfl
    (world seeds ar n pk cv c ts mach ρ b h))
  let P := fun d : Cells => ¬Good fam btw128 L₀ ts cv (extend c (records cv d))
  have empty : ¬P (fun _ => none) := by
    change ¬¬Good _ _ _ _ _ _
    rw [records_empty,show extend c (fun _ => none) = c from funext fun x => by simp [extend]]
    exact not_not_intro hg
  let ok := accepted seeds ar n pk cv c ts
  let rate := freshRate N Q
  let K := 2*(m:ℝ)*Real.sqrt ((2^256:ℝ)⁻¹)
  have gb := failure_growth seeds ar n cv c ts N Q hg fin tw
  have checked := certificate_fails seeds ar n pk cv c ts hcv
  have len (z : Receipt) : (log m z).length ≤ m := List.length_take_le ..
  have rb := log_leaf (log m) ok P m checked len
  have hq' := monitor_cost seeds ar n pk cv c ts mach q hq
  have result := Failure.machine_mean (LongClass.mapping pk cv c b) P
    (fun z h => ok z ∧ ∀ p ∈ log m z, projectTable h p.1=p.2) (monitor seeds ar n pk cv c ts mach) Q
    hq' ρ hp ht rate K (show 0 ≤ rate from by unfold rate freshRate; positivity)
    (show 0 ≤ K from by dsimp [K]; positivity) empty gb rb
  convert result using 1
  · apply Finset.sum_congr rfl
    intro h _
    apply congrArg (unifW _ h * ·)
    congr 1
  · rfl

end Reduction.Compression.LongClass
#print axioms Reduction.Compression.LongClass.conditional
