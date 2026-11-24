import Integration.SlhDsaCompressionHmacHop
import Integration.SlhDsaCompressionBudget
import Ideal.Realize.Walk

/-! Weighted query counts for the lazy message-PRF reduction. A public hash pays
for every compression block it evaluates, and a message-oracle call pays for
the remaining inner and outer HMAC blocks. -/
namespace Reduction.Compression.HmacKey
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum
variable (S : Sha2Set) (f : RandFns S.vp.params) {E : Type} [Fintype E] [DecidableEq E]
local notation "P₀" => randPrims f
local notation "Work" => WS Input Output E
local notation "PS" => PRFScheme.PRFOracleSpec (S.Node × List Byte) S.Node

/-- A deterministic port computation retains its query bound when the continuation
can also query a classical oracle whose uniform samples are free. -/
theorem pureEvalQ {ι α : Type} {sp : OracleSpec ι} (cnt : (unifSpec + sp).Domain → ℕ)
    (hu : ∀ n, cnt (.inl n) = 0) (d : (Input → Output) → α) {n : ℕ}
    (h : EvalCost (fun H => (pure (d H) : ProbComp α)) n) :
    EvalCostQ E cnt (fun H => (pure (d H) : OracleComp (unifSpec + sp) α)) n := by
  have hc := h E α (fun a _ => (pure a : Closed Work α)) 0 (fun a => PUE.pure a 0)
  simp only [liftU_pure, pure_bind, Nat.zero_add] at hc
  let emb : QueryImpl unifSpec (OracleComp (unifSpec + sp)) := fun i => liftM ((unifSpec + sp).query (.inl i))
  have ho := PUE.wrap0 (cnt' := cnt) emb (fun t => wCount_liftM_query _ _ (le_of_eq (hu t))) hc
  simp only [wrap0_pure] at ho
  intro β B q hB
  simpa only [liftQ_pure, pure_bind, Nat.add_comm n q] using PUE.bind ho hB

def openCharge (D : Type) : (Lazy.RSpec (Lazy.msgG P₀) D S.Node (publicHashSpec (P₀).core)).Domain → ℕ
  | .inr (.inl d) => messageCharge S (.inr d)
  | .inr (.inr (.inr t)) => hashCalls S f t
  | _ => 0

private theorem sample_free {α : Type} (p : ProbComp α) :
    WCount (messageCharge S) (liftM p : OracleComp PS α) 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => simp only [liftM_pure]; exact trivial
  | query_bind i k ih =>
    rw [liftM_bind]
    exact WCount.bind (n := 0) (m := 0) (wCount_liftM_query (sp := PS) (messageCharge S) (.inl i) le_rfl) ih

theorem lazy_cost {α : Type}
    (A : (Input → Output) → QOC Work (Lazy.OSpec P₀ (Lazy.msgG P₀)) α)
    (q : ℕ) (hA : PUE (openCharge S f _) A q) :
    PUE (messageCharge S) (fun H => qLazyRun (hashPort S f H) (A H)) q := by
  unfold qLazyRun
  refine PUE.wrap0E (fun H => Lazy.interp (hashPort S f H)) (cnt := openCharge S f Unit) ?_
    (PUE.map _ (PUE.wrap _ (cnt := openCharge S f _) ?_ hA []))
  · rintro (n|d|u|hash)
    · exact EvalCostQ.const _ (wCount_liftM_query _ _ le_rfl)
    · exact EvalCostQ.const _ (wCount_liftM_query _ _ le_rfl)
    · exact EvalCostQ.const _ (sample_free S _)
    · exact pureEvalQ (messageCharge S) (fun _ => rfl) _ (hashPort_cost S f hash)
  · let sp := Lazy.RSpec (Lazy.msgG P₀) Unit S.Node (publicHashSpec (P₀).core)
    rintro (n|d|a|hash) s
    · exact WCount.map (wCount_liftM_query (sp := sp) (openCharge S f Unit) (.inl n) le_rfl) (fun x => (x,s))
    · exact WCount.map (wCount_liftM_query (sp := sp) (openCharge S f Unit) (.inr (.inl d)) le_rfl) (fun x => (x,s))
    · cases hl : s.lookup a with
      | some b => rw [Lazy.lazyImplR_sec_run_hit a s b hl]; exact trivial
      | none => rw [Lazy.lazyImplR_sec_run_miss a s hl]; exact WCount.map (wCount_liftM_query (sp := sp) (openCharge S f Unit) (.inr (.inr (.inl ()))) le_rfl) (fun x => (x,(a,x)::s))
    · exact WCount.map (wCount_liftM_query (sp := sp) (openCharge S f Unit) (.inr (.inr (.inr hash))) le_rfl) (fun x => (x,s))

local notation "OS" => Lazy.OSpec P₀ (Lazy.msgG P₀)

private theorem open_count {α : Type} (P : OracleComp OS α) (q B : ℕ)
    (hh : IsQueryBoundP P (fun t => Lazy.kind t = .hash) q)
    (hg : IsQueryBoundP P (fun t => Lazy.kind t = .game) 0)
    (hc : IsQueryBoundP P (fun t => B < openCharge S f _ t) 0) :
    WCount (openCharge S f _) P (q*B) := by
  refine cappedCount _ (fun t => Lazy.kind t = .hash ∨ Lazy.kind t = .game) _ ?_ _ _ ?_ hc
  · rintro (n|d|a|h) e <;> first | rfl | exact (e (Or.inl rfl)).elim | exact (e (Or.inr rfl)).elim
  · exact hh.or hg

theorem keygen_count (pk : S.Node) :
    WCount (openCharge S f _) (Lazy.openKeygen P₀ (Lazy.msgG P₀) pk)
      (Lazy.keygenHashes S.vp * signMax S 0) := by
  apply open_count
  · exact (Lazy.openKeygen_kindBound (vp := S.vp) (prims := P₀) (gspec := Lazy.msgG P₀) .hash pk).mono
      (by simpa [Lazy.ind] using Lazy.keygenB_hash (vp := S.vp))
  · apply Realize.np_openKeygen <;> intros <;> exact fun h => nomatch h
  · apply Realize.np_openKeygen
    · intro d; exact Nat.not_lt_zero _
    · intro key xs hx
      change ¬signMax S 0 < thashCalls S xs.length
      rcases hx with h|h|h|h <;> rw [h] <;> unfold signMax keygenMax <;> omega

theorem sign_core_count (m : List Byte) (pk root R : S.Node) :
    WCount (openCharge S f _) (Lazy.openSign P₀ (Lazy.msgG P₀) m pk root R)
      (Lazy.signHashes S.vp * signMax S m.length) := by
  apply open_count
  · exact (Lazy.openSign_kindBound (vp := S.vp) (prims := P₀) (gspec := Lazy.msgG P₀) .hash m pk root R).mono
      (by simpa [Lazy.ind] using Lazy.signB_hash (vp := S.vp))
  · apply Realize.np_openSign <;> intros <;> exact fun h => nomatch h
  · apply Realize.np_openSign
    · intro d; exact Nat.not_lt_zero _
    · intro key xs hx
      change ¬signMax S m.length < thashCalls S xs.length
      rcases hx with h|h|h|h <;> rw [h] <;> unfold signMax keygenMax <;> omega
    · exact not_lt_of_ge (le_max_right ..)

theorem open_sample {α : Type} (p : ProbComp α) :
    WCount (openCharge S f _) (liftM p : OracleComp OS α) 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => simp only [liftM_pure]; exact trivial
  | query_bind i k ih =>
    rw [liftM_bind]
    exact WCount.bind (n := 0) (m := 0) (wCount_liftM_query (sp := OS) _ (.inl i) le_rfl) ih

def signCharge (L : ℕ) := (L + S.vp.params.n + 16)/128 + 2 + Lazy.signHashes S.vp * signMax S L

theorem sign_count (rand : PublicKeyCore (P₀).core → ProbComp S.Node) (pk : PublicKeyCore (P₀).core)
    (m : List Byte) :
    WCount (openCharge S f _) (Lazy.msgSignO (vp := S.vp) rand pk m) (signCharge S m.length) := by
  unfold Lazy.msgSignO
  have h := WCount.bind (open_sample S f (rand pk)) (fun r =>
    WCount.bind (wCount_liftM_query (sp := OS) (openCharge S f _) (.inr (.inl (r,m)))
      (le_refl ((m.length + S.vp.params.n + 16)/128 + 2))) (sign_core_count S f m pk.pkSeed pk.pkRoot))
  rw [Nat.zero_add] at h
  kexact h

end Reduction.Compression.HmacKey
#print axioms Reduction.Compression.HmacKey.lazy_cost
#print axioms Reduction.Compression.HmacKey.keygen_count
#print axioms Reduction.Compression.HmacKey.sign_count
