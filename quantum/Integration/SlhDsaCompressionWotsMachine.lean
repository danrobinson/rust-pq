import Integration.SlhDsaCompressionWotsCost

namespace Reduction.Compression
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum QMsg Resources2 Open
variable (S : Sha2Set) (f : RandFns S.vp.params)
local notation "P₀" => randPrims f
variable {E : Type} [Fintype E] [DecidableEq E]
    (rand : S.Node → S.Node → ProbComp S.Node) (F : PortForger Input Output E)

abbrev WState := SecretTable S.vp P₀ × List (WotsGame.Entry P₀) × S.Node
abbrev WAnswer := ℕ × S.Node × WotsSig S.vp.params (P₀).core

private noncomputable def clip (L : ℕ) (st : WState S f) (pk : S.Node) (H : Input → Output) :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore S.vp (P₀).core))
      (StateT (G2Log P₀) ProbComp)
  | .inl n => qmSignG (fun k => rand k.pkSeed k.pkRoot) (hashPort S f H) st.1 ⟨pk,st.2.2⟩
      (wotsSignFromHistO st.2.1 ⟨pk,st.2.2⟩) (.inl n)
  | .inr m => qmSignG (fun k => rand k.pkSeed k.pkRoot) (hashPort S f H) st.1 ⟨pk,st.2.2⟩
      (wotsSignFromHistO st.2.1 ⟨pk,st.2.2⟩) (.inr (m.take L))

private theorem clip_cost (L : ℕ) (st : WState S f) (pk : S.Node) (t) (s : G2Log P₀) :
    EvalCost (fun H => (clip S f rand L st pk H t).run s) (sgnW (wotsSignHistHashes S.vp * signMax S L) t) := by
  rcases t with n|m
  · exact EvalCost.const _
  · let msg := m.take L
    change EvalCost (fun H => rand pk st.2.2 >>= fun rnd => lazyRandomizer s msg rnd >>= fun R =>
      simulateQ (qmImpl (hashPort S f H) st.1) (wotsSignFromHistO st.2.1 ⟨pk,st.2.2⟩ msg R) >>=
      fun sig => (pure (sig,s ++ [(msg,rnd,R)]) : ProbComp _)) _
    have h := EvalCost.bind (EvalCost.const (X := Input) (Y := Output) (rand pk st.2.2)) fun rnd =>
      EvalCost.bind (EvalCost.const (X := Input) (Y := Output) (lazyRandomizer s msg rnd)) fun R =>
        EvalCost.bind (wotsSign_cost S f st.1 st.2.1 ⟨pk,st.2.2⟩ msg R) fun sig =>
          EvalCost.const (X := Input) (Y := Output) (pure (sig,s ++ [(msg,rnd,R)]) : ProbComp _)
    apply h.mono
    simp only [Nat.zero_add,Nat.add_zero,sgnW]
    exact Nat.mul_le_mul_left _ (signMax_mono S (by simp [msg]))

noncomputable def wMachine {β : Type} (st : WState S f) (pk : S.Node)
    (post : WAnswer S f → OracleComp (Lazy.OSpec P₀ []ₒ) β) (H : Input → Output) :=
  qmWotsMach (fun k => rand k.pkSeed k.pkRoot) (hashPort S f H) (mainAt S f F H) st pk post

def wotsBudget (L q qs post : ℕ) := q + qs*(wotsSignHistHashes S.vp*signMax S L) +
  (wotsAnswerHashes S.vp + post)*signMax S L

theorem wMachine_pue {β : Type} (c : Caps) (st : WState S f) (pk : S.Node)
    (post : WAnswer S f → OracleComp (Lazy.OSpec P₀ []ₒ) β) (cp q qs : ℕ)
    (hp : ∀ x, IsQueryBoundP (post x) (fun t => Lazy.kind t = .hash) cp)
    (hl : ∀ x L, IsQueryBoundP (post x) (exceeds S f L) 0)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    PUE (spec := unifSpec) cnt0 (wMachine S f rand F st pk post) (wotsBudget S c.ml q qs cp) := by
  let key : PublicKeyCore (P₀).core := ⟨pk,st.2.2⟩
  let tail := fun (m : List Byte) sig => wotsAnswerOpen st.2.1 key m sig >>= post
  let work := fun H => close (clip S f rand c.ml st pk H) (mainAt S f F H key) [] >>= fun z =>
    (liftU (simulateQ (qmImpl (hashPort S f H) st.1) (tail (z.1.1.take c.ml) z.1.2)) : Closed (WS Input Output E) β)
  have same : wMachine S f rand F st pk post = work := by
    funext H
    unfold wMachine qmWotsMach work
    apply close_congr_on (G := Gint c.ml) (ok := fun z => z.1.length ≤ c.ml)
    · rintro (n|m) ht
      · rfl
      · exact congrArg (β := StateT (G2Log P₀) ProbComp (GeneralScheme.SignatureCore S.vp (P₀).core))
          (fun m : List Byte => qmSignG (fun k => rand k.pkSeed k.pkRoot) (hashPort S f H) st.1 key
            (wotsSignFromHistO st.2.1 key) (.inr m)) (List.take_of_length_le ht).symm
    · intro z hz
      simp only [List.take_of_length_le hz, tail,key]
    · exact mainAt_cap S f F c hc H key
  rw [same]
  refine PUE.bind (PUE.close _ (clip_cost S f rand c.ml st pk)
    (mainAt_pue S f F q qs _ hq hs key) _) fun z => ?_
  let m := z.1.1.take c.ml
  have ht := openProgram_cost S f st.1 (tail m z.1.2) (wotsAnswerHashes S.vp+cp) m.length
    (Lazy.qb_bind _ (wotsAnswerOpen_hashes st.2.1 key m z.1.2) hp)
    (isQueryBoundP_bind_zero _ _ (wotsAnswer_cap S f st.2.1 key m z.1.2) (fun x => hl x m.length))
  have hu := PUE.liftU_bind (E := E) (q := 0) (B := fun o _ => (pure o : Closed (WS Input Output E) β))
    (ht.mono (Nat.mul_le_mul_left _ (signMax_mono S (by simp [m] : m.length ≤ c.ml)))) fun o => PUE.pure o 0
  simpa only [bind_pure,Nat.zero_add] using hu

end Reduction.Compression
#print axioms Reduction.Compression.wMachine_pue
