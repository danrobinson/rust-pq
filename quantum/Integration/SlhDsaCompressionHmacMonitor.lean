import Integration.SlhDsaCompressionHmacCollision
import Integration.SlhDsaCompressionHmacExtract

namespace Reduction.Compression.HmacKey
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive Quantum
variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E] {α : Type}
local notation "Work" => WS Input Output E
local notation "D" => S.Node × List Byte
local notation "Spec" => PRFScheme.PRFOracleSpec D S.Node

private noncomputable def step (i : Chain512) (d : D) (seen : Chain512 → Option D) (c : (D →ₒ S.Node).QueryCache)
    (k : S.Node → (Input → Output) → QOC Work Spec α) (v : Chain512) (H : Input → Output) :
    Closed Work (Option (D × D)) :=
  DigestCollision.onQuery d v (fun r => DigestCollision.watch (R := S.Node)
    (innerDigest S (tablesOf H) i) (k r H)) seen c

theorem monitor_cost (i : Chain512) {A : (Input → Output) → QOC Work Spec α} {q : ℕ}
    (hA : PUE (messageCharge S) A q) (seen : Chain512 → Option D) (c : (D →ₒ S.Node).QueryCache) :
    PUE (spec := unifSpec) cnt0 (fun H =>
      DigestCollision.watch (R := S.Node) (innerDigest S (tablesOf H) i) (A H) seen c) q := by
  induction hA generalizing seen c with
  | pure a q => exact PUE.pure none q
  | instr j k q _ ih => exact PUE.instr j _ _ (fun x => ih x seen c)
  | port k q _ ih => exact PUE.port _ _ (ih seen c)
  | eval x k q _ ih => exact PUE.eval x _ _ (fun y => ih y seen c)
  | query t k q _ ih =>
    rcases t with n|d
    · exact PUE.query n _ q (fun r => ih r seen c)
    · have digest := fold512_cost i (MIdeal.Sha512.iblocks S d.1 d.2)
      have cost (v : Chain512) : PUE (spec := unifSpec) cnt0 (step S i d seen c k v) q := by
        unfold step DigestCollision.onQuery
        split
        · exact PUE.pure _ q
        · cases e : c d with
          | some r => exact ih r seen c
          | none =>
            have hc := PUE.liftU_bind (EvalCost.const (X := Input) (Y := Output) ($ᵗ S.Node))
              (fun r => ih r (Function.update seen v (some d)) (c.cacheQuery d r))
            simpa only [Nat.add_zero] using hc
      have h := PUE.liftU_bind digest cost
      simp only [liftU_pure, pure_bind, MIdeal.Sha512.iblocks_length] at h
      have bound : q + ((d.2.length + S.vp.params.n + 16)/128 + 1) ≤ q + messageCharge S (.inr d) := by
        simp only [messageCharge]; omega
      have hh := h.mono bound
      have e : (fun H => DigestCollision.watch (R := S.Node) (innerDigest S (tablesOf H) i)
          (liftM ((instrSpec Work + Spec).query (.inr (.inr d))) >>= fun r => k r H) seen c) =
          fun H => step S i d seen c k (innerDigest S (tablesOf H) i d) H := by
        funext H
        rfl
      rw [e]
      exact hh

private def inBudget (q : ℕ) (d : D) := messageCharge S (.inr d) ≤ q

private def pairInBudget (q : ℕ) : Option (D × D) → Prop
  | none => True
  | some (d,e) => inBudget S q d ∧ inBudget S q e

private theorem monitor_lengths {A : (Input → Output) → QOC Work Spec α} {q : ℕ} (hA : PUE (messageCharge S) A q)
    (H : Input → Output) (h : D → Chain512) (limit : ℕ) (hle : q ≤ limit)
    (seen : Chain512 → Option D) (hs : ∀ v d, seen v = some d → inBudget S limit d) (c : (D →ₒ S.Node).QueryCache) :
    AllQueries (fun _ => True) (pairInBudget S limit)
      (DigestCollision.watch (R := S.Node) h (A H) seen c) := by
  induction hA generalizing seen c with
  | pure a q => trivial
  | instr j k q _ ih => exact ⟨trivial, fun r => ih r hle seen hs c⟩
  | port k q _ ih => exact ⟨trivial, fun _ => ih (by omega) seen hs c⟩
  | eval x k q _ ih => exact ih (H x) (by omega) seen hs c
  | query t k q _ ih =>
    have hq : q ≤ limit := by omega
    rcases t with n|d
    · exact ⟨trivial, fun r => ih r hq seen hs c⟩
    · have hd : inBudget S limit d := by apply Nat.le_trans (Nat.le_add_left _ q) hle
      rw [DigestCollision.watch_query]
      split
      · cases e : seen (h d) with
        | none => trivial
        | some d' => exact ⟨hs _ _ e,hd⟩
      · cases e : c d with
        | some r => exact ih r hq seen hs c
        | none =>
          apply QMsg.allQ_bind (QMsg.allQ_true_of (fun _ => trivial) _)
          intro r _
          apply ih r hq
          intro v x hx
          by_cases hv : v = h d
          · subst v
            rw [Function.update_self] at hx
            exact Option.some.inj hx ▸ hd
          · exact hs _ _ ((Function.update_of_ne hv ..).symm.trans hx)

private def collect (g : CompressionTables) (i : Chain512) (limit : ℕ) :
    Option (D × D) → Option Evidence
  | none => none
  | some (x,y) => if messageCharge S (.inr x) ≤ limit ∧ messageCharge S (.inr y) ≤ limit
      then extractInner S g i x y else none

/-- The same quantum machine both observes colliding messages in the ideal game
and returns checkable compression inputs. The public starting state is sampled
independently of the compression tables. -/
noncomputable def evidenceMachine (A : (Input → Output) → QOC Work Spec Bool) (i : Chain512) (q : ℕ)
    (H : Input → Output) : Closed Work (Option Evidence) :=
  collect S (tablesOf H) i q <$> DigestCollision.watch (R := S.Node) (innerDigest S (tablesOf H) i)
    (A H) (fun _ => none) ∅

theorem evidence_budget (A : (Input → Output) → QOC Work Spec Bool) (i : Chain512)
    (q : ℕ) (hA : PUE (messageCharge S) A q) :
    PUE (spec := unifSpec) cnt0 (evidenceMachine S A i q) (q + (q+q)) := by
  unfold evidenceMachine
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  apply PUE.bind (monitor_cost S i hA _ _)
  intro z
  cases z with
  | none => exact PUE.pure none _
  | some z =>
    rcases z with ⟨x,y⟩
    change PUE cnt0 (fun H => pure (if messageCharge S (.inr x) ≤ q ∧ messageCharge S (.inr y) ≤ q
      then extractInner S (tablesOf H) i x y else none)) (q+q)
    by_cases ok : messageCharge S (.inr x) ≤ q ∧ messageCharge S (.inr y) ≤ q
    · simp only [ite_eq_left ok]
      have ⟨hx,hy⟩ := ok
      simp only [messageCharge] at hx hy
      let B := fun (v : Option Evidence) (_ : Input → Output) => (pure v : Closed Work _)
      have cost := (extract_inner_cost S i x y).mono (n' := q+q) (by omega)
      have h := PUE.liftU_bind (q := 0) (B := B) cost (fun v => PUE.pure _ 0)
      simpa only [B, liftU_pure, pure_bind, Nat.zero_add] using h
    · simp only [ite_eq_right ok]
      exact PUE.pure none _

def acceptsEvidence (g : CompressionTables) (i : Chain512) : Option Evidence → Bool
  | none => false
  | some (.inl x) => decide (g.2 x = i)
  | some (.inr (x,y)) => decide (x ≠ y ∧ g.2 x = g.2 y)

theorem evidence_success (A : (Input → Output) → QOC Work Spec Bool) (g : CompressionTables)
    (i : Chain512) (q : ℕ) (hA : PUE (messageCharge S) A q) (M : Matrix Work Work ℂ) :
    digestCollisionPr S A M g i ≤
      qWeight (fun z => acceptsEvidence g i z = true)
        (evidenceMachine S A i q (oracle g)) M := by
  classical
  unfold evidenceMachine digestCollisionPr
  rw [qWeight_map, tablesOf_oracle]
  apply QItsr.qWeight_mono_allQ (monitor_lengths S hA (oracle g) (innerDigest S g i) q le_rfl
    (fun _ => none) (by intro _ _ h; cases h) ∅)
  rintro (_ | ⟨x,y⟩) cap hit
  · simp [DigestCollision.found] at hit
  · have ⟨ne,eq⟩ : x ≠ y ∧ innerDigest S g i x = innerDigest S g i y := by
      simpa [DigestCollision.found] using hit
    obtain ⟨w,he,hw⟩ := extract_inner_hit S g i x y ne eq
    change acceptsEvidence g i (if messageCharge S (.inr x) ≤ q ∧ messageCharge S (.inr y) ≤ q
        then extractInner S g i x y else none) = true
    rw [ite_eq_left (show messageCharge S (.inr x) ≤ q ∧ messageCharge S (.inr y) ≤ q from cap),he]
    rcases w with u|⟨u,v⟩ <;> exact decide_eq_true hw

end Reduction.Compression.HmacKey
#print axioms Reduction.Compression.HmacKey.monitor_cost
#print axioms Reduction.Compression.HmacKey.evidence_budget
#print axioms Reduction.Compression.HmacKey.evidence_success
