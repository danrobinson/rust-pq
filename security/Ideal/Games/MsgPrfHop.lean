import Ideal.Games.MsgPrfDefs
import Ideal.Games.MsgPrfLazy
import Ideal.Games.Prf

/-!
# The HMAC-shaped PRF: from the real game to the hybrid with private rows

All games are run against answer functions computed from eagerly sampled tables.

* `prT_G2`: for fixed key blocks `a ≠ b`, overriding the cells `(IV, a)`, `(IV, b)` of a uniform
  table by fresh `cvI`, `cvO` and the rows `cvI`, `cvO` by independent uniform row tables `TI`,
  `TO` gives a uniform table (`HP.evalDist_gstar` twice).
* `realAns_G2`: with the overridden table the real answers are the hybrid answers
  `d ↦ out (TO (ob (mdFold g (TI b₁) rest)))` except at bad queries (`bad1`).
* `prT_real_le_hyb`: `Pr[real] ≤ Pr[hybrid] + Pr[badGame1]`.
-/

open OracleComp OracleSpec ENNReal PRFScheme

namespace Ideal.MsgPrf

open Ideal.HP Ideal.Prf

variable {St Blk K P M Y : Type}

/-! ## The experiments as answer-function runs -/

/-- Answers of the real experiment at table `g` and key `k`. -/
def realAns (IV : St) (ik ok : K → Blk) (ib : P × M → Blk × List Blk) (ob : St → Blk)
    (out : St → Y) (g : CF St Blk) (k : K) :
    (t : (St × Blk) ⊕ (P × M)) → (hS St Blk + ((P × M) →ₒ Y)).Range t
  | .inl q => g q
  | .inr d => macF IV ik ok ib ob out g k d

/-- The cell of the outer row table read by the function oracle at `d`. -/
def phi (ib : P × M → Blk × List Blk) (ob : St → Blk) (g : CF St Blk) (TI : Blk → St)
    (d : P × M) : Blk :=
  ob (chainI g TI (ib d))

/-- Answers of the hybrid: compression queries by `g`, the function oracle at `d` by
`out (TO (ob (mdFold g (TI b₁) rest)))`. -/
abbrev hybAns (ib : P × M → Blk × List Blk) (ob : St → Blk) (out : St → Y) (g : CF St Blk)
    (TI TO : Blk → St) : (t : (St × Blk) ⊕ (P × M)) → (hS St Blk + ((P × M) →ₒ Y)).Range t :=
  ansL (spec₀ := hS St Blk) (fun q => g q) (phi ib ob g TI) out TO

theorem simulateQ_real [SampleableType K] (IV : St) (ik ok : K → Blk)
    (ib : P × M → Blk × List Blk) (ob : St → Blk) (out : St → Y) (g : CF St Blk) (k : K)
    {α : Type} (oa : OracleComp (unifSpec + (hS St Blk + ((P × M) →ₒ Y))) α) :
    simulateQ ((macSchemeI IV ik ok ib ob out g).prfRealQueryImpl k) (simulateQ (instImpl g) oa) =
      simulateQ (ansImpl (realAns IV ik ok ib ob out g k)) oa := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) oa
  rcases t with n | q | d
  · exact simulateQ_spec_query _ _
  · rfl
  · exact simulateQ_spec_query _ _

theorem macRealGameI_eq [SampleableType K] [SampleableType (CF St Blk)] [SampleableType Y]
    [DecidableEq P] [DecidableEq M] (IV : St) (ik ok : K → Blk) (ib : P × M → Blk × List Blk)
    (ob : St → Blk) (out : St → Y) (A : PrfAdvI St Blk P M Y) :
    macRealGameI IV ik ok ib ob out A = $ᵗ (CF St Blk) >>= fun g => $ᵗ K >>= fun k =>
      simulateQ (ansImpl (realAns IV ik ok ib ob out g k)) A := by
  unfold macRealGameI
  refine bind_congr fun g => ?_
  show ($ᵗ K >>= fun k => simulateQ ((macSchemeI IV ik ok ib ob out g).prfRealQueryImpl k)
    (simulateQ (instImpl g) A)) = _
  simp only [simulateQ_real]

/-! ## The double override -/

section Override

variable [DecidableEq St] [DecidableEq Blk]

/-- The table `g` with the cells `(IV, a)`, `(IV, b)` overridden by `cvI`, `cvO` and the rows
`cvI`, `cvO` by the row tables `TI`, `TO`. -/
def G2 (IV : St) (a b : Blk) (cvI cvO : St) (g : CF St Blk) (TI TO : Blk → St) : CF St Blk :=
  gstar IV b cvO (gstar IV a cvI g TI) TO

/-- **The doubly overridden table is uniform.** -/
theorem prT_G2 [SampleableType St] [Fintype Blk] [SampleableType (CF St Blk)] (IV : St)
    (a b : Blk) (F : CF St Blk → ProbComp Bool) :
    prT ($ᵗ (CF St Blk) >>= F) =
      prT ($ᵗ St >>= fun cvO => $ᵗ St >>= fun cvI => $ᵗ (Blk → St) >>= fun TO =>
        $ᵗ (CF St Blk) >>= fun g => $ᵗ (Blk → St) >>= fun TI =>
          F (G2 IV a b cvI cvO g TI TO)) := by
  rw [prT_congr (evalDist_gstar IV b F)]
  refine prT_bind_congr _ _ _ fun cvO _ => ?_
  rw [prT_swap]
  have h : prT ($ᵗ (Blk → St) >>= fun TO => $ᵗ (CF St Blk) >>= fun G1 =>
        F (gstar IV b cvO G1 TO)) =
      prT ($ᵗ (Blk → St) >>= fun TO => $ᵗ St >>= fun cvI => $ᵗ (CF St Blk) >>= fun g =>
        $ᵗ (Blk → St) >>= fun TI => F (G2 IV a b cvI cvO g TI TO)) :=
    prT_bind_congr _ _ _ fun TO _ =>
      prT_congr (evalDist_gstar IV a fun G1 => F (gstar IV b cvO G1 TO))
  rw [h, prT_swap]

/-- A query at which the real answers at the overridden table may differ from the hybrid
answers: a compression query at a key cell or in row `cvI` or `cvO`; a function query one of
whose chaining values (used as a row) is `IV`, `cvI` or `cvO`. -/
def bad1 (IV : St) (ib : P × M → Blk × List Blk) (a b : Blk) (cvI cvO : St) (g : CF St Blk)
    (TI : Blk → St) : (St × Blk) ⊕ (P × M) → Bool
  | .inl q => (decide (q = (IV, a)) || decide (q = (IV, b))) ||
      (decide (q.1 = cvI) || decide (q.1 = cvO))
  | .inr d => cvHit IV g (TI (ib d).1) (ib d).2 ||
      (cvHit cvI g (TI (ib d).1) (ib d).2 || cvHit cvO g (TI (ib d).1) (ib d).2)

theorem mdFold_G2 (IV : St) (a b : Blk) (cvI cvO : St) (g : CF St Blk) (TI TO : Blk → St)
    (c : St) (bs : List Blk) (h1 : cvHit IV g c bs = false) (h2 : cvHit cvI g c bs = false)
    (h3 : cvHit cvO g c bs = false) :
    mdFold (G2 IV a b cvI cvO g TI TO) c bs = mdFold g c bs := by
  induction bs generalizing c with
  | nil => rfl
  | cons b' bs ih =>
    simp only [cvHit, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h1 h2 h3
    have e : G2 IV a b cvI cvO g TI TO (c, b') = g (c, b') := by
      simp [G2, gstar, h1.1, h2.1, h3.1]
    simp only [mdFold, List.foldl_cons] at ih ⊢
    rw [e]
    exact ih _ h1.2 h2.2 h3.2

/-- Outside the bad queries, the real answers at the overridden table are the hybrid answers. -/
theorem realAns_G2 (IV : St) (ik ok : K → Blk) (ib : P × M → Blk × List Blk) (ob : St → Blk)
    (out : St → Y) (k : K) (hab : ik k ≠ ok k) (cvI cvO : St) (hI : cvI ≠ IV) (hO : cvO ≠ IV)
    (hIO : cvI ≠ cvO) (g : CF St Blk) (TI TO : Blk → St) (t : (St × Blk) ⊕ (P × M))
    (ht : bad1 IV ib (ik k) (ok k) cvI cvO g TI t = false) :
    realAns IV ik ok ib ob out (G2 IV (ik k) (ok k) cvI cvO g TI TO) k t =
      hybAns ib ob out g TI TO t := by
  rcases t with q | d
  · simp only [bad1, Bool.or_eq_false_iff, decide_eq_false_iff_not] at ht
    show G2 IV (ik k) (ok k) cvI cvO g TI TO q = g q
    simp [G2, gstar, ht.1.1, ht.1.2, ht.2.1, ht.2.2]
  · simp only [bad1, Bool.or_eq_false_iff] at ht
    show out (G2 IV (ik k) (ok k) cvI cvO g TI TO (G2 IV (ik k) (ok k) cvI cvO g TI TO (IV, ok k),
        ob (mdFold (G2 IV (ik k) (ok k) cvI cvO g TI TO)
          (G2 IV (ik k) (ok k) cvI cvO g TI TO
            (G2 IV (ik k) (ok k) cvI cvO g TI TO (IV, ik k), (ib d).1)) (ib d).2))) =
      out (TO (ob (mdFold g (TI (ib d).1) (ib d).2)))
    have e1 : G2 IV (ik k) (ok k) cvI cvO g TI TO (IV, ok k) = cvO := by simp [G2, gstar]
    have e2 : G2 IV (ik k) (ok k) cvI cvO g TI TO (IV, ik k) = cvI := by
      simp [G2, gstar, hab, Ne.symm hO]
    have e3 : G2 IV (ik k) (ok k) cvI cvO g TI TO (cvI, (ib d).1) = TI (ib d).1 := by
      simp [G2, gstar, hI, hIO]
    have e4 : ∀ x, G2 IV (ik k) (ok k) cvI cvO g TI TO (cvO, x) = TO x := fun x => by
      simp [G2, gstar, hO]
    rw [e1, e2, e3, mdFold_G2 IV _ _ cvI cvO g TI TO _ _ ht.1 ht.2.1 ht.2.2, e4]

/-- The conditions on `cvI`, `cvO` under which the override is well behaved fail. -/
def glob (IV cvI cvO : St) : Bool :=
  decide (cvI = IV) || (decide (cvO = IV) || decide (cvI = cvO))

theorem prT_real_pointwise (IV : St) (ik ok : K → Blk) (ib : P × M → Blk × List Blk)
    (ob : St → Blk) (out : St → Y) (hne : ∀ k, ik k ≠ ok k) (A : PrfAdvI St Blk P M Y) (k : K)
    (cvI cvO : St) (g : CF St Blk) (TI TO : Blk → St) :
    prT (simulateQ (ansImpl (realAns IV ik ok ib ob out
        (G2 IV (ik k) (ok k) cvI cvO g TI TO) k)) A) ≤
      prT (simulateQ (ansImpl (hybAns ib ob out g TI TO)) A) +
      prT ((simulateQ (trImpl (hybAns ib ob out g TI TO)) A).run [] >>= fun z =>
        pure (glob IV cvI cvO || z.2.any (bad1 IV ib (ik k) (ok k) cvI cvO g TI))) := by
  by_cases hg : glob IV cvI cvO = true
  · have h1 : prT ((simulateQ (trImpl (hybAns ib ob out g TI TO)) A).run [] >>= fun z =>
        pure (glob IV cvI cvO || z.2.any (bad1 IV ib (ik k) (ok k) cvI cvO g TI))) = 1 := by
      refine prT_eq_one_of_support _ fun b hb => ?_
      rw [mem_support_bind_iff] at hb
      obtain ⟨z, -, hb⟩ := hb
      simpa [hg] using hb
    rw [h1]
    exact (prT_le_one _).trans le_add_self
  · have hg' : glob IV cvI cvO = false := by simpa using hg
    have hg2 := hg'
    simp only [glob, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hg2
    have h := prT_simulateQ_le_add_trace
      (realAns IV ik ok ib ob out (G2 IV (ik k) (ok k) cvI cvO g TI TO) k)
      (hybAns ib ob out g TI TO) (bad1 IV ib (ik k) (ok k) cvI cvO g TI)
      (fun t ht => realAns_G2 IV ik ok ib ob out k (hne k) cvI cvO hg2.1 hg2.2.1 hg2.2.2 g TI TO
        t ht) A pure []
    simpa only [bind_pure, hg', Bool.false_or] using h

end Override

/-! ## The hybrid and the bad game -/

section Games

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St] [Fintype Blk]
  [SampleableType (CF St Blk)] [SampleableType K]

/-- The hybrid game: private row tables for the two keyed rows. -/
noncomputable def hybGame (ib : P × M → Blk × List Blk) (ob : St → Blk) (out : St → Y)
    (A : PrfAdvI St Blk P M Y) : ProbComp Bool :=
  $ᵗ (Blk → St) >>= fun TO => $ᵗ (CF St Blk) >>= fun g => $ᵗ (Blk → St) >>= fun TI =>
    simulateQ (ansImpl (hybAns ib ob out g TI TO)) A

/-- The bad-event game of the hop: the key and the two hidden chaining values make a traced
query of the hybrid run bad. -/
noncomputable def badGame1 (IV : St) (ik ok : K → Blk) (ib : P × M → Blk × List Blk)
    (ob : St → Blk) (out : St → Y) (A : PrfAdvI St Blk P M Y) : ProbComp Bool :=
  $ᵗ K >>= fun k => $ᵗ St >>= fun cvO => $ᵗ St >>= fun cvI => $ᵗ (Blk → St) >>= fun TO =>
    $ᵗ (CF St Blk) >>= fun g => $ᵗ (Blk → St) >>= fun TI =>
      (simulateQ (trImpl (hybAns ib ob out g TI TO)) A).run [] >>= fun z =>
        pure (glob IV cvI cvO || z.2.any (bad1 IV ib (ik k) (ok k) cvI cvO g TI))

/-- **The hop**: `Pr[real] ≤ Pr[hybrid] + Pr[bad]`. -/
theorem prT_real_le_hyb [SampleableType Y] [DecidableEq P] [DecidableEq M] (IV : St)
    (ik ok : K → Blk) (ib : P × M → Blk × List Blk) (ob : St → Blk) (out : St → Y)
    (hne : ∀ k, ik k ≠ ok k) (A : PrfAdvI St Blk P M Y) :
    prT (macRealGameI IV ik ok ib ob out A) ≤
      prT (hybGame ib ob out A) + prT (badGame1 IV ik ok ib ob out A) := by
  rw [macRealGameI_eq, prT_swap]
  have hk : ∀ k : K, prT ($ᵗ (CF St Blk) >>= fun g =>
        simulateQ (ansImpl (realAns IV ik ok ib ob out g k)) A) ≤
      prT (hybGame ib ob out A) +
        prT ($ᵗ St >>= fun cvO => $ᵗ St >>= fun cvI => $ᵗ (Blk → St) >>= fun TO =>
          $ᵗ (CF St Blk) >>= fun g => $ᵗ (Blk → St) >>= fun TI =>
            (simulateQ (trImpl (hybAns ib ob out g TI TO)) A).run [] >>= fun z =>
              pure (glob IV cvI cvO || z.2.any (bad1 IV ib (ik k) (ok k) cvI cvO g TI))) := by
    intro k
    rw [prT_G2 IV (ik k) (ok k) fun g => simulateQ (ansImpl (realAns IV ik ok ib ob out g k)) A]
    refine (prT_bind_le_add _ _ _ _ fun cvO => prT_bind_le_add _ _ _ _ fun cvI =>
      prT_bind_le_add _ _ _ _ fun TO => prT_bind_le_add _ _ _ _ fun g =>
        prT_bind_le_add _ _ _ _ fun TI =>
          prT_real_pointwise IV ik ok ib ob out hne A k cvI cvO g TI TO).trans (le_of_eq ?_)
    rw [prT_bind_const, prT_bind_const]
    rfl
  refine (prT_bind_le_add ($ᵗ K) _ (fun _ => hybGame ib ob out A) _ hk).trans ?_
  rw [prT_bind_const]
  rfl

end Games

end Ideal.MsgPrf

#print axioms Ideal.MsgPrf.prT_real_le_hyb
