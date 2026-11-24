import Integration.SlhDsaShakePermutationIdealDriver

namespace Reduction.ShakePermutation.IdealDriver
open Classical Quantum OracleSpec OracleComp PQ.Interactive Fix Machine RoundPort Player
variable {ι α E : Type} [Fintype E] [DecidableEq E] {sp : OracleSpec ι}

def driverOK (ok : ι → Prop) : InstrIdx (Big E) ⊕ (Unit ⊕ (Unit ⊕ ι)) → Prop
  | .inr (.inr (.inr t)) => ok t
  | _ => True

omit [DecidableEq E] in
private theorem inner_ok {X Y : Type} (ok : ι → Prop) (port : Driver E sp Unit)
    (hp : AllQueries (driverOK ok) (fun _ => True) port)
    (lens : Equiv.Perm (Register X Y Work) → Equiv.Perm (Reg Work)) (g : Circuit X Y Work) :
    AllQueries (driverOK ok) (fun _ => True) (Player.lower port lens g) := by
  induction g with
  | localOp => exact ⟨trivial,fun _ => trivial⟩
  | port => exact hp
  | seq a b ha hb => exact QMsg.allQ_bind ha fun _ _ => hb

omit [DecidableEq E] in
private theorem expansion_ok (ok : ι → Prop) (g : Program Work) :
    AllQueries (driverOK ok) (fun _ => True) (expand (E := E) (sp := sp) g) := by
  induction g with
  | mask c => exact inner_ok _ _ (QMsg.allQ_query _ _ trivial) _ c
  | head c => exact inner_ok _ _ (QMsg.allQ_query _ _ trivial) _ c
  | localOp => exact ⟨trivial,fun _ => trivial⟩
  | seq a b ha hb => exact QMsg.allQ_bind ha fun _ _ => hb

private theorem empty_count {I : Type} {os : OracleSpec I} {ok : I → Prop} {w : I → ℕ}
    (P : OracleComp os α) (h : AllQueries ok (fun _ => True) P) (zero : ∀ t, ok t → w t = 0) :
    WCount w P 0 := by
  induction P using OracleComp.inductionOn with
  | pure => trivial
  | query_bind t k ih =>
    rw [QMsg.allQ_query_bind] at h
    rw [wCount_query_bind,zero t h.1]
    exact ⟨le_rfl,fun r => ih r (h.2 r)⟩

private theorem single {I : Type} {os : OracleSpec I} (w : I → ℕ) (t : I) :
    WCount w (liftM (os.query t) : OracleComp os _) (w t) := by
  rw [← bind_pure (liftM (os.query t) : OracleComp os _),wCount_query_bind]
  exact ⟨le_rfl,fun _ => trivial⟩

def driverSign : InstrIdx (Big E) ⊕ (Unit ⊕ (Unit ⊕ (ℕ ⊕ Msg))) → ℕ
  | .inr (.inr (.inr (.inr _))) => 1
  | _ => 0

variable (π : Permutation) (T : ℕ) (h : RateMask)

/-- The classical interface of the expanded circuit makes precisely the
original player's signing requests. -/
theorem expanded_sign (P : QOC (Old E) (portSpec + Signing) α) (q : ℕ) (hp : CountBound isSign P q) :
    WCount driverSign (expanded π P) q := by
  apply WCount.simulateQ (Player.impl π) _ ((countBound_iff_wCount _ _ _).1 hp)
  rintro (j | ⟨⟨⟩⟩ | n | m)
  · exact single _ _
  · apply empty_count _ (expansion_ok (E := E) (sp := Signing) (fun _ => False) (publicPort π))
    rintro (j | _ | _ | _ | _) h <;> first | rfl | contradiction
  · exact single _ _
  · exact single _ _

theorem expanded_cap (c : Caps) (P : QOC (Old E) (portSpec + Signing) (Msg × Sig))
    (hp : AllQueries (capIdx c) (capOut c) P) :
    AllQueries (driverOK (signedCap c)) (capOut c) (expanded π P) := by
  apply QMsg.allQ_simulateQ (Player.impl π) _ hp
  rintro (j | ⟨⟨⟩⟩ | i) ok
  · exact QMsg.allQ_query _ _ trivial
  · exact expansion_ok _ _
  · cases i <;> exact QMsg.allQ_query _ _ ok

omit [DecidableEq E] in
private theorem raw_port_count (p : Driver E Signing α) (n : ℕ)
    (hP : WCount (Player.weight false) p n) :
    CountBound (fun i => mark true (fun _ => false) i = true) (run π T h p) n := by
  apply (countBound_iff_wCount ..).2
  apply WCount.simulateQ (IdealDriver.lower π T h) _ hP
  rintro (j | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | i)
  · exact single _ _
  · exact ⟨Nat.zero_le _,fun _ => trivial⟩
  · exact single _ _
  · exact single _ _

omit [DecidableEq E] in
private theorem raw_sign_count (p : Driver E Signing α) (n : ℕ)
    (hP : WCount driverSign p n) :
    CountBound (fun i => mark false signingCost i = true) (run π T h p) n := by
  apply (countBound_iff_wCount ..).2
  apply WCount.simulateQ (IdealDriver.lower π T h) _ hP
  rintro (j | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | n | m)
  · exact single _ _
  · exact ⟨Nat.zero_le _,fun _ => trivial⟩
  · exact single _ _
  · exact single _ _
  · exact single _ _

theorem bounds (F : PortForger Port Words E) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) (pk) :
    let p := (forger π T h F).main pk
    CountBound (fun i => mark true (fun _ => false) i = true) p (8*q) ∧
    CountBound (fun i => mark false signingCost i = true) p qs ∧
    AllQueries (allowed (signedCap c)) (capOut c) p := by
  intro p
  refine ⟨raw_port_count _ _ _ _ _ (Player.expanded_count _ false _ _ (hq pk)),
    raw_sign_count _ _ _ _ _ (expanded_sign _ _ _ (hs pk)),?_⟩
  apply QMsg.allQ_simulateQ (IdealDriver.lower π T h) _ (expanded_cap π c _ (hc pk))
  rintro (j | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | t) ok
  · exact QMsg.allQ_query _ _ trivial
  · exact ⟨trivial,fun _ => trivial⟩
  · exact QMsg.allQ_query _ _ trivial
  · exact QMsg.allQ_query _ _ ok

end Reduction.ShakePermutation.IdealDriver
#print axioms Reduction.ShakePermutation.IdealDriver.bounds
