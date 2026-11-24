import Integration.SlhDsaShakePermutationClassicalPublicRisk

namespace Reduction.ShakePermutation.Classic
open Classical OracleSpec OracleComp MLink SLHDSA PQ.Interactive
open SetOracle (uniformMean)
open scoped ENNReal
noncomputable section

abbrev Native (S : Sha2Set) (N : ℕ) := (Port →ₒ Words) + (ShakeApi.Input N →ₒ Bytes S.vp.params.m)

def prefixRows (T : ℕ) (p : List Rate) : List Rate → List (Row T)
  | [] => []
  | r::rs => rowId T (p++[r]) :: prefixRows T (p++[r]) rs

theorem prefixRows_length (T : ℕ) (p xs : List Rate) : (prefixRows T p xs).length = xs.length := by
  induction xs generalizing p with | nil => rfl | cons r rs ih => simp [prefixRows,ih]

structure Report (T : ℕ) where
  edges : EdgeTrace Words
  seen : Finset (Row T)
  privateRows : Finset (Row T)
  clean : Bool

def emptyReport (T : ℕ) : Report T := ⟨[],∅,∅,true⟩

def recordPub (T : ℕ) (H : Row T → Words) (r : Report T) (d : Bool) (x : Words) : Words × Report T :=
  if h : old r.edges d x then (h.choose,r) else
    let j := publicRow T r.edges d x
    let y := H j
    (y,{r with edges := edge d x y :: r.edges, seen := insert j r.seen, clean := r.clean && decide (isolated r.edges x y)})

def blocksOf {N : ℕ} (x : ShakeApi.Input N) := messageBlocks (sp (List.ofFn x.2))

def reportStep (S : Sha2Set) (N T : ℕ) (H : Row T → Words) (raw : ShakeApi.RawTable S N) :
    (i : (Native S N).Domain) → Report T → (Native S N).Range i × Report T
  | .inl (d,x),r => recordPub T H r d x
  | .inr x,r => (raw x,{r with privateRows := (prefixRows T [] (blocksOf x)).toFinset ∪ r.privateRows})

def report (S : Sha2Set) (N T : ℕ) {Z : Type} (H : Row T → Words) (raw : ShakeApi.RawTable S N)
    (P : OracleComp (Native S N) Z) : Report T → Z × Report T :=
  OracleComp.construct (C := fun _ => Report T → Z × Report T) (fun z r => (z,r))
    (fun i _ k r => let v := reportStep S N T H raw i r; k v.1 v.2) P

def mass {T : ℕ} (r : Report T) := r.edges.length+r.privateRows.card
def cost {S : Sha2Set} {N : ℕ} : (Native S N).Domain → ℕ
  | .inl _ => 1
  | .inr x => (blocksOf x).length

theorem report_mass (S : Sha2Set) (N T : ℕ) {Z : Type} (H : Row T → Words) (raw : ShakeApi.RawTable S N)
    (P : OracleComp (Native S N) Z) (q : ℕ) (hq : WCount (cost (S := S) (N := N)) P q)
    (r : Report T) : mass (report S N T H raw P r).2 ≤ mass r + q := by
  induction P using OracleComp.inductionOn generalizing q r with
  | pure => exact Nat.le_add_right _ _
  | query_bind i k ih =>
    rw [wCount_query_bind] at hq
    let z := reportStep S N T H raw i r
    apply (ih z.1 _ (hq.2 _) z.2).trans
    have step : mass z.2 ≤ mass r + cost (S := S) i := by
      rcases i with ⟨d,x⟩|x
      · simp only [z,reportStep,recordPub]; split <;> simp [mass,cost] <;> omega
      · change r.edges.length + ((prefixRows T [] (blocksOf x)).toFinset ∪ r.privateRows).card ≤ _
        have hi := Finset.card_union_le (prefixRows T [] (blocksOf x)).toFinset r.privateRows
        have hj := List.toFinset_card_le (prefixRows T [] (blocksOf x))
        rw [prefixRows_length] at hj
        change _ ≤ r.edges.length+r.privateRows.card+(blocksOf x).length
        omega
    omega

theorem seen_mono (S : Sha2Set) (N T : ℕ) {Z : Type} (H : Row T → Words) (raw : ShakeApi.RawTable S N)
    (P : OracleComp (Native S N) Z) (r : Report T) : r.seen ⊆ (report S N T H raw P r).2.seen := by
  induction P using OracleComp.inductionOn generalizing r with
  | pure => exact Finset.Subset.rfl
  | query_bind i k ih =>
    let z := reportStep S N T H raw i r
    apply Finset.Subset.trans _ (ih z.1 z.2)
    rcases i with ⟨d,x⟩|x
    · simp only [z,reportStep,recordPub]; split <;> simp
    · exact Finset.Subset.rfl

theorem report_stable (S : Sha2Set) (N T : ℕ) {Z : Type} (H G : Row T → Words) (raw : ShakeApi.RawTable S N)
    (P : OracleComp (Native S N) Z) (r : Report T)
    (agree : ∀ i ∈ (report S N T H raw P r).2.seen, G i = H i) :
    report S N T G raw P r = report S N T H raw P r := by
  induction P using OracleComp.inductionOn generalizing r with
  | pure => rfl
  | query_bind i k ih =>
    let z := reportStep S N T H raw i r
    have step : reportStep S N T G raw i r = z := by
      rcases i with ⟨d,x⟩|x
      · simp only [z,reportStep,recordPub]
        split
        · rfl
        · rename_i fresh
          have new : publicRow T r.edges d x ∈ z.2.seen := by simp [z,reportStep,recordPub,fresh]
          have val := agree _ (seen_mono S N T H raw (k z.1) z.2 new)
          rw [val]
      · rfl
    change report S N T G raw (k (reportStep _ _ _ G raw i r).1) (reportStep _ _ _ G raw i r).2 = _
    rw [step]
    exact ih z.1 z.2 agree

def hidden {T : ℕ} (r : Report T) := r.privateRows \ r.seen
def denied {T : ℕ} (r : Report T) := forbidden wordSplit 0 r.edges 0

theorem report_hidden (S : Sha2Set) (N T : ℕ) {Z : Type} (rates : Row T → Rate) (raw : ShakeApi.RawTable S N)
    (P : OracleComp (Native S N) Z) (q : ℕ) (hq : WCount (cost (S := S) (N := N)) P q) :
    let trace := fun (g : Row T → Capacity) => (report S N T (fun j => join (rates j) (g j)) raw P (emptyReport T)).2
    uniformMean (fun g => hit (leaked (hidden (trace g)) (denied (trace g)) g)) ≤
      ((q*(2*q+2)+q^2 : ℕ) : ℝ≥0∞) / Fintype.card Capacity := by
  let R := {r : Report T // mass r ≤ q}
  let trace := fun (g : Row T → Capacity) => (report S N T (fun j => join (rates j) (g j)) raw P (emptyReport T)).2
  let Tof (g : Row T → Capacity) : R := ⟨trace g,by simpa only [trace,mass,emptyReport,Finset.card_empty,
    List.length_nil,zero_add] using (report_mass S N T (fun j => join (rates j) (g j)) raw P q hq (emptyReport T))⟩
  apply adaptive_hidden_risk Tof (fun r => r.val.seen) (fun r => hidden r.val) (fun r => denied r.val) _ _ q (2*q+2)
  · intro r
    have h : r.val.edges.length+r.val.privateRows.card ≤ q := r.property
    exact ⟨(Finset.card_le_card Finset.sdiff_subset).trans (by omega),(forbidden_card ..).trans (by omega)⟩
  · intro g h eq
    apply Subtype.ext
    exact congrArg Prod.snd (report_stable S N T _ _ raw P (emptyReport T)
      (fun j hj => congrArg (join (rates j)) (eq j hj)))
  · intro r i hi
    exact (Finset.mem_sdiff.mp hi).2

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.report_hidden
