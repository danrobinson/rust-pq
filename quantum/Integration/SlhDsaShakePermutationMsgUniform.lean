import Integration.SlhDsaShakePermutationMsgPhases

/-! A one-challenge decomposition in which the measured continuation is
itself a uniformly query-bounded *family*. It may use either public oracle
at resumption. Before resumption it carries no unqueried oracle values. -/
namespace Reduction.ShakePermutation.MsgSplit
open Classical OracleComp OracleSpec PQ.Interactive Quantum
variable {X Y E D R A : Type} [Fintype X] [Fintype Y] [Fintype E] [DecidableEq X]
  [DecidableEq Y] [DecidableEq E] [AddCommGroup Y] [Inhabited R]

abbrev FamilyPost (X Y E R A : Type) [Fintype X] [Fintype Y] [Fintype E] [DecidableEq X]
    [DecidableEq Y] [DecidableEq E] [AddCommGroup Y] (Q : ℕ) :=
  {f : R → (X → Y) → Closed (WS X Y E) A // ∀ r, PUE (spec:=unifSpec) cnt0 (f r) Q}
abbrev FamilyStage (X Y E D R A : Type) [Fintype X] [Fintype Y] [Fintype E] [DecidableEq X]
    [DecidableEq Y] [DecidableEq E] [AddCommGroup Y] (Q : ℕ) :=
  A ⊕ (D × FamilyPost X Y E R A Q)

noncomputable def callPost {Q : ℕ} (H : X → Y) (f : D → R) :
    FamilyStage X Y E D R A Q → Closed (WS X Y E) A
  | .inl a => pure a
  | .inr (d,post) => post.val (f d) H

noncomputable def specialize {Q : ℕ} (H : X → Y) :
    FamilyStage X Y E D R A Q → Stage (WS X Y E) D R A
  | .inl a => .inl a
  | .inr (d,post) => .inr (d,fun r => post.val r H)

theorem family_before {p : (X → Y) → Source (WS X Y E) D R A} {q : ℕ}
    (hp : PUE (fun _ => 0) p q) (Q : ℕ) (hq : q ≤ Q) :
    ∃ pre : (X → Y) → Closed (WS X Y E) (FamilyStage X Y E D R A Q),
      PUE (spec:=unifSpec) cnt0 pre q ∧
      ∀ H, before (p H) = specialize H <$> pre H := by
  induction hp with
  | pure a q =>
    exact ⟨fun _ => pure (.inl a),PUE.pure _ _,fun _ => by simp [before,specialize]⟩
  | instr j k q _ ih =>
    choose pre cost eq using fun i => ih i hq
    refine ⟨fun H => liftM ((instrSpec (WS X Y E) + unifSpec).query (.inl (framedIdx j))) >>= fun i => pre i H,
      PUE.instr j _ _ cost,?_⟩
    intro H
    change (liftM _ >>= fun i => before (k i H)) = _
    rw [map_bind]
    exact bind_congr fun i => eq i H
  | port k q _ ih =>
    obtain ⟨pre,cost,eq⟩ := ih (by omega)
    refine ⟨fun H => liftM ((instrSpec (WS X Y E) + unifSpec).query (.inl (portIdx H))) >>= fun _ => pre H,
      PUE.port _ _ cost,?_⟩
    intro H
    change (liftM _ >>= fun _ => before (k H)) = _
    rw [map_bind]
    exact bind_congr fun _ => eq H
  | query t k q h ih =>
    rcases t with n|d
    · choose pre cost eq using fun i => ih i hq
      refine ⟨fun H => liftM ((instrSpec (WS X Y E) + unifSpec).query (.inr n)) >>= fun i => pre i H,
        PUE.query n _ q cost,?_⟩
      intro H
      change (liftM _ >>= fun i => before (k i H)) = _
      rw [map_bind]
      exact bind_congr fun i => eq i H
    · let post (r : R) (H : X → Y) := ansRun (fun _ => (default : R)) (k r H)
      have pc (r) : PUE (spec:=unifSpec) cnt0 (post r) Q := by
        unfold post ansRun
        apply PUE.map Prod.fst
        exact (PUE.close _ (fun _ _ => EvalCost.const _) (h r) ()).mono hq
      exact ⟨fun _ => pure (.inr (d,⟨post,pc⟩)),PUE.pure _ _,fun H => by simp [before,specialize,post]⟩
  | eval x k q _ ih =>
    choose pre cost eq using fun y => ih y (by omega)
    exact ⟨fun H => pre (H x) H,PUE.eval x _ q cost,fun H => eq (H x) H⟩

theorem uniform_split {p : (X → Y) → Source (WS X Y E) D R A} {q : ℕ}
    (hp : PUE (fun _ => 0) p q) (Q : ℕ) (hq : q ≤ Q) :
    ∃ pre : (X → Y) → Closed (WS X Y E) (FamilyStage X Y E D R A Q),
      PUE (spec:=unifSpec) cnt0 pre q ∧
      ∀ H f, CountBound (fun i => isChallenge i = true) (p H) 1 →
        ansRun f (p H) = pre H >>= callPost H f := by
  obtain ⟨pre,cost,eq⟩ := family_before hp Q hq
  refine ⟨pre,cost,fun H f bound => ?_⟩
  rw [answered _ _ bound,eq,bind_map_left]
  exact bind_congr fun z => by rcases z with a | ⟨d,post⟩ <;> rfl

end Reduction.ShakePermutation.MsgSplit
#print axioms Reduction.ShakePermutation.MsgSplit.uniform_split
