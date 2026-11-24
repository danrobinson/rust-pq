import Integration.SlhDsaCompressionClassCost

namespace Reduction.Compression.ClassOne
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum Resources2 QMsg
variable (S : Sha2Set) (f : RandFns S.vp.params)
local notation "P₀" => randPrims f
variable {E : Type} [Fintype E] [DecidableEq E] (rand : S.Node → S.Node → ProbComp S.Node)
variable (F : PortForger Input Output E)

abbrev State := SecretTable S.vp P₀ × List (Bytes 22 × List S.Node)

private noncomputable def signClip (L : ℕ) (st : State S f) (pk root : S.Node) (H : Input → Output) :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore S.vp (P₀).core))
      (StateT (G2Log P₀) ProbComp) := fun
  | .inl n => qmImplS (fun k => rand k.pkSeed k.pkRoot) (hashPort S f H) st.1 pk root (.inl n)
  | .inr m => qmImplS (fun k => rand k.pkSeed k.pkRoot) (hashPort S f H) st.1 pk root (.inr (m.take L))

private theorem signClip_cost (L : ℕ) (st : State S f) (pk root : S.Node) (t) (s : G2Log P₀) :
    EvalCost (fun H => (signClip S f rand L st pk root H t).run s) (sgnW (Lazy.signHashes S.vp * signMax S L) t) := by
  rcases t with n|m
  · exact EvalCost.const _
  · let msg := m.take L
    change EvalCost (fun H => rand pk root >>= fun rnd => lazyRandomizer s msg rnd >>= fun R =>
      simulateQ (qmImpl (hashPort S f H) st.1) (Lazy.openSign P₀ []ₒ msg pk root R) >>= fun sig =>
      (pure (sig,s ++ [(msg,rnd,R)]) : ProbComp _)) _
    have h := EvalCost.bind (EvalCost.const (X := Input) (Y := Output) (rand pk root)) fun rnd =>
      EvalCost.bind (EvalCost.const (X := Input) (Y := Output) (lazyRandomizer s msg rnd)) fun R =>
        EvalCost.bind (sign_cost S f st.1 pk root R msg) fun sig =>
          EvalCost.const (X := Input) (Y := Output) (pure (sig,s ++ [(msg,rnd,R)]) : ProbComp _)
    apply h.mono
    simp only [Nat.zero_add,Nat.add_zero,sgnW]
    exact Nat.mul_le_mul_left _ (signMax_mono S (by simp [msg]))

noncomputable def machine (arity : ℕ) (st : State S f) (pk : S.Node) (H : Input → Output) :=
  qmMach (fun k => rand k.pkSeed k.pkRoot) (hashPort S f H) arity (mainAt S f F H) st pk

def budget (L q qs : ℕ) := Lazy.keygenHashes S.vp * keygenMax S + q + qs*(Lazy.signHashes S.vp*signMax S L) +
  (1 + verifyHashes S.vp * 2)*signMax S L

theorem machine_pue (c : Caps) (n : ℕ) (st : State S f) (pk : S.Node) (q qs : ℕ)
    (hl : ∀ x ∈ st.2, x.2.length ≤ S.vp.params.len)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    PUE (spec := unifSpec) cnt0 (machine S f rand F n st pk) (budget S c.ml q qs) := by
  let K := Lazy.signHashes S.vp * signMax S c.ml
  let V := (1 + verifyHashes S.vp * 2)*signMax S c.ml
  let work := fun (root : S.Node) (H : Input → Output) =>
    close (signClip S f rand c.ml st pk root H) (mainAt S f F H ⟨pk,root⟩) [] >>= fun z =>
      (liftU (classOut P₀ n st.2 <$> simulateQ (qmImpl (hashPort S f H) st.1)
        (qmTail pk st.2 root ((z.1.1.take c.ml,z.1.2),z.2))) : Closed (WS Input Output E) _)
  have hwork (root : S.Node) : PUE (spec := unifSpec) cnt0 (work root) (q + qs*K + V) := by
    refine PUE.bind (PUE.close _ (signClip_cost S f rand c.ml st pk root)
      (mainAt_pue S f F q qs K hq hs ⟨pk,root⟩) _) fun z => ?_
    have h := (tail_cost S f st.1 pk root st.2 hl ((z.1.1.take c.ml,z.1.2),z.2)).map (classOut P₀ n st.2)
    have hv := h.mono (Nat.mul_le_mul_left _ (signMax_mono S (by simp : (z.1.1.take c.ml).length ≤ c.ml)))
    have hq' := PUE.liftU_bind (E := E) (q := 0) (B := fun o _ => (pure o : Closed (WS Input Output E) _)) hv (fun o => PUE.pure o 0)
    simpa only [bind_pure,Nat.zero_add,V] using hq'
  have both := PUE.liftU_bind (keygen_cost S f st.1 pk) hwork
  have same : machine S f rand F n st pk = fun H => liftU
      (simulateQ (qmImpl (hashPort S f H) st.1) (Lazy.openKeygen P₀ []ₒ pk)) >>= fun root => work root H := by
    funext H
    unfold machine qmMach work
    apply bind_congr
    intro root
    apply close_congr_on (G := Gint c.ml) (ok := fun z => z.1.length ≤ c.ml)
    · rintro (j|m) ht
      · rfl
      · change m.length ≤ c.ml at ht
        exact congrArg (β := StateT (G2Log P₀) ProbComp (GeneralScheme.SignatureCore S.vp (P₀).core))
          (fun m : List Byte => qmImplS (fun k => rand k.pkSeed k.pkRoot) (hashPort S f H)
            st.1 pk root (.inr m)) (List.take_of_length_le ht).symm
    · intro z hz
      simp only [List.take_of_length_le hz]
    · exact mainAt_cap S f F c hc H ⟨pk,root⟩
  rw [same]
  apply both.mono
  dsimp only [budget,K,V]
  omega

end Reduction.Compression.ClassOne
#print axioms Reduction.Compression.ClassOne.machine_pue
