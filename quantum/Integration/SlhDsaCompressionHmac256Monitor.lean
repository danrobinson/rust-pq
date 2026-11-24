import Integration.SlhDsaCompressionHmac256Collision
import Integration.SlhDsaCompressionHmac256Extract

namespace Reduction.Compression.Hmac256
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive Quantum
variable {E : Type} [Fintype E] [DecidableEq E] {α : Type}
local notation "Work" => WS Input Output E
local notation "D" => (Bytes 16) × List Byte
local notation "Spec" => PRFScheme.PRFOracleSpec D (Bytes 16)

private noncomputable def step (i : St) (d : D) (seen : St → Option D) (c : (D →ₒ (Bytes 16)).QueryCache)
    (k : (Bytes 16) → (Input → Output) → QOC Work Spec α) (v : St) (H : Input → Output) :
    Closed Work (Option (D × D)) :=
  DigestCollision.onQuery d v (fun r => DigestCollision.watch (R := (Bytes 16))
    (innerDigest (tablesOf H) i) (k r H)) seen c

theorem monitor_cost (i : St) {A : (Input → Output) → QOC Work Spec α} {q : ℕ}
    (hA : PUE (messageCharge) A q) (seen : St → Option D) (c : (D →ₒ (Bytes 16)).QueryCache) :
    PUE (spec := unifSpec) cnt0 (fun H =>
      DigestCollision.watch (R := (Bytes 16)) (innerDigest (tablesOf H) i) (A H) seen c) q := by
  induction hA generalizing seen c with
  | pure a q => exact PUE.pure none q
  | instr j k q _ ih => exact PUE.instr j _ _ (fun x => ih x seen c)
  | port k q _ ih => exact PUE.port _ _ (ih seen c)
  | eval x k q _ ih => exact PUE.eval x _ _ (fun y => ih y seen c)
  | query t k q _ ih =>
    rcases t with n|d
    · exact PUE.query n _ q (fun r => ih r seen c)
    · have digest := fold256_cost i (Ideal.iblocks d.1 d.2)
      have cost (v : St) : PUE (spec := unifSpec) cnt0 (step i d seen c k v) q := by
        unfold step DigestCollision.onQuery
        split
        · exact PUE.pure _ q
        · cases e : c d with
          | some r => exact ih r seen c
          | none =>
            have hc := PUE.liftU_bind (EvalCost.const (X := Input) (Y := Output) ($ᵗ (Bytes 16)))
              (fun r => ih r (Function.update seen v (some d)) (c.cacheQuery d r))
            simpa only [Nat.add_zero] using hc
      have h := PUE.liftU_bind digest cost
      simp only [liftU_pure, pure_bind, Ideal.iblocks_length] at h
      have bound : q + ((d.2.length + 24)/64 + 1) ≤ q + messageCharge (.inr d) := by
        simp only [messageCharge]; omega
      have hh := h.mono bound
      have e : (fun H => DigestCollision.watch (R := (Bytes 16)) (innerDigest (tablesOf H) i)
          (liftM ((instrSpec Work + Spec).query (.inr (.inr d))) >>= fun r => k r H) seen c) =
          fun H => step i d seen c k (innerDigest (tablesOf H) i d) H := by
        funext H
        rfl
      rw [e]
      exact hh

private def inBudget (q : ℕ) (d : D) := messageCharge (.inr d) ≤ q

private def pairInBudget (q : ℕ) : Option (D × D) → Prop
  | none => True
  | some (d,e) => inBudget q d ∧ inBudget q e

private theorem monitor_lengths {A : (Input → Output) → QOC Work Spec α} {q : ℕ} (hA : PUE (messageCharge) A q)
    (H : Input → Output) (h : D → St) (limit : ℕ) (hle : q ≤ limit)
    (seen : St → Option D) (hs : ∀ v d, seen v = some d → inBudget limit d) (c : (D →ₒ (Bytes 16)).QueryCache) :
    AllQueries (fun _ => True) (pairInBudget limit)
      (DigestCollision.watch (R := (Bytes 16)) h (A H) seen c) := by
  induction hA generalizing seen c with
  | pure a q => trivial
  | instr j k q _ ih => exact ⟨trivial, fun r => ih r hle seen hs c⟩
  | port k q _ ih => exact ⟨trivial, fun _ => ih (by omega) seen hs c⟩
  | eval x k q _ ih => exact ih (H x) (by omega) seen hs c
  | query t k q _ ih =>
    have hq : q ≤ limit := by omega
    rcases t with n|d
    · exact ⟨trivial, fun r => ih r hq seen hs c⟩
    · have hd : inBudget limit d := by apply Nat.le_trans (Nat.le_add_left _ q) hle
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

private def collect (g : CompressionTables) (i : St) (limit : ℕ) :
    Option (D × D) → Option Evidence
  | none => none
  | some (x,y) => if messageCharge (.inr x) ≤ limit ∧ messageCharge (.inr y) ≤ limit
      then extractInner g i x y else none

/-- The same quantum machine both observes colliding messages in the ideal game
and returns checkable compression inputs. The public starting state is sampled
independently of the compression tables. -/
noncomputable def evidenceMachine (A : (Input → Output) → QOC Work Spec Bool) (i : St) (q : ℕ)
    (H : Input → Output) : Closed Work (Option Evidence) :=
  collect (tablesOf H) i q <$> DigestCollision.watch (R := (Bytes 16)) (innerDigest (tablesOf H) i)
    (A H) (fun _ => none) ∅

theorem evidence_budget (A : (Input → Output) → QOC Work Spec Bool) (i : St)
    (q : ℕ) (hA : PUE (messageCharge) A q) :
    PUE (spec := unifSpec) cnt0 (evidenceMachine A i q) (q + (q+q)) := by
  unfold evidenceMachine
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  apply PUE.bind (monitor_cost i hA _ _)
  intro z
  cases z with
  | none => exact PUE.pure none _
  | some z =>
    rcases z with ⟨x,y⟩
    change PUE cnt0 (fun H => pure (if messageCharge (.inr x) ≤ q ∧ messageCharge (.inr y) ≤ q
      then extractInner (tablesOf H) i x y else none)) (q+q)
    by_cases ok : messageCharge (.inr x) ≤ q ∧ messageCharge (.inr y) ≤ q
    · simp only [ite_eq_left ok]
      have ⟨hx,hy⟩ := ok
      simp only [messageCharge] at hx hy
      let B := fun (v : Option Evidence) (_ : Input → Output) => (pure v : Closed Work _)
      have cost := (extract_inner_cost i x y).mono (n' := q+q) (by omega)
      have h := PUE.liftU_bind (q := 0) (B := B) cost (fun v => PUE.pure _ 0)
      simpa only [B, liftU_pure, pure_bind, Nat.zero_add] using h
    · simp only [ite_eq_right ok]
      exact PUE.pure none _

def acceptsEvidence (g : CompressionTables) (i : St) : Option Evidence → Bool
  | none => false
  | some (.inl x) => decide (g.1 x = i)
  | some (.inr (x,y)) => decide (x ≠ y ∧ g.1 x = g.1 y)

theorem evidence_success (A : (Input → Output) → QOC Work Spec Bool) (g : CompressionTables)
    (i : St) (q : ℕ) (hA : PUE (messageCharge) A q) (M : Matrix Work Work ℂ) :
    digestCollisionPr A M g i ≤
      qWeight (fun z => acceptsEvidence g i z = true)
        (evidenceMachine A i q (oracle g)) M := by
  classical
  unfold evidenceMachine digestCollisionPr
  rw [qWeight_map, tablesOf_oracle]
  apply QItsr.qWeight_mono_allQ (monitor_lengths hA (oracle g) (innerDigest g i) q le_rfl
    (fun _ => none) (by intro _ _ h; cases h) ∅)
  rintro (_ | ⟨x,y⟩) cap hit
  · simp [DigestCollision.found] at hit
  · have ⟨ne,eq⟩ : x ≠ y ∧ innerDigest g i x = innerDigest g i y := by
      simpa [DigestCollision.found] using hit
    obtain ⟨w,he,hw⟩ := extract_inner_hit g i x y ne eq
    change acceptsEvidence g i (if messageCharge (.inr x) ≤ q ∧ messageCharge (.inr y) ≤ q
        then extractInner g i x y else none) = true
    rw [ite_eq_left (show messageCharge (.inr x) ≤ q ∧ messageCharge (.inr y) ≤ q from cap),he]
    rcases w with u|⟨u,v⟩ <;> exact decide_eq_true hw

end Reduction.Compression.Hmac256
#print axioms Reduction.Compression.Hmac256.monitor_cost
#print axioms Reduction.Compression.Hmac256.evidence_budget
#print axioms Reduction.Compression.Hmac256.evidence_success
