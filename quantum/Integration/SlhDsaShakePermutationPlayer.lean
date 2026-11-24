import Integration.SlhDsaShakePermutationPortMatrix
import PQ.Interactive.QromBridgeEvalIAdv

/-! Expansion of a port forger's actual control tree into local instruments,
two quantum table ports, and its original classical oracles. The signing and
sampling branches are forwarded verbatim. -/
namespace Reduction.ShakePermutation.RoundPort.Player
open Classical Quantum OracleComp OracleSpec PQ.Interactive Fix

abbrev Old (E : Type) := (Port × Words) × E
abbrev Aux := MaskReg × HeadReg × Words
abbrev Big (E : Type) := Old E × Aux

def wires (E : Type) : Big E ≃ Reg Work × E where
  toFun s := ((s.2.1,s.2.2.1,s.1.1.1,s.1.1.2,s.2.2.2),s.1.2)
  invFun s := (((s.1.2.2.1,s.1.2.2.2.1),s.2),s.1.1,s.1.2.1,s.1.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def wireGate (E : Type) (e : Equiv.Perm (Reg Work)) : Equiv.Perm (Big E) :=
  (wires E).trans ((e.prodCongr (Equiv.refl _)).trans (wires E).symm)

def onMask (e : Equiv.Perm (Register MaskAddr Capacity Work)) : Equiv.Perm (Reg Work) :=
  (maskOrder Work).trans ((e.prodCongr (Equiv.refl _)).trans (maskOrder Work).symm)

def onHead (e : Equiv.Perm (Register Capacity Rate Work)) : Equiv.Perm (Reg Work) :=
  (Equiv.refl _).prodCongr e

def onWork (e : Equiv.Perm Work) : Equiv.Perm (Reg Work) :=
  (Equiv.refl _).prodCongr ((Equiv.refl _).prodCongr e)

noncomputable def gateIdx {A : Type} [DecidableEq A] [Fintype A] (e : Equiv.Perm A) : InstrIdx A :=
  ⟨0,(SubInstrument.relabel e).comap (fun _ : Fin 1 => ()) fin1_bijective.injective,
    DSubInstrument.Lossless.comap (SubInstrument.lossless_relabel e) fin1_bijective⟩

variable {ι E : Type} [Fintype E] [DecidableEq E] {sp : OracleSpec ι}

abbrev Banks (sp : OracleSpec ι) := portSpec + (portSpec + sp)
abbrev Driver (E : Type) [Fintype E] (sp : OracleSpec ι) :=
  QOC (Big E) (Banks sp)

noncomputable def gate (e : Equiv.Perm (Reg Work)) : Driver E sp Unit := do
  let _ ← (instrSpec (Big E) + Banks sp).query (.inl (gateIdx (wireGate E e)))
  pure ()

def askMask : Driver E sp Unit :=
  liftM ((instrSpec (Big E) + Banks sp).query (.inr (.inl ())))
def askHead : Driver E sp Unit :=
  liftM ((instrSpec (Big E) + Banks sp).query (.inr (.inr (.inl ()))))

noncomputable def lower {X Y : Type} (port : Driver E sp Unit)
    (lens : Equiv.Perm (Register X Y Work) → Equiv.Perm (Reg Work)) :
    Circuit X Y Work → Driver E sp Unit
  | .localOp e => gate (lens e)
  | .port => port
  | .seq a b => lower port lens a >>= fun _ => lower port lens b

noncomputable def expand : Program Work → Driver E sp Unit
  | .mask c => lower askMask onMask c
  | .head c => lower askHead onHead c
  | .localOp e => gate (onWork e)
  | .seq a b => expand a >>= fun _ => expand b

noncomputable def frameIdx (j : InstrIdx (Old E)) : InstrIdx (Big E) :=
  ⟨j.1,j.2.1.frame Aux,SubInstrument.Lossless.frame j.2.2 Aux⟩

noncomputable def impl (π : Permutation) : QueryImpl (instrSpec (Old E) + (portSpec + sp)) (Driver E sp)
  | .inl j => liftM ((instrSpec (Big E) + Banks sp).query (.inl (frameIdx j)))
  | .inr (.inl ()) => expand (publicPort π)
  | .inr (.inr i) => liftM ((instrSpec (Big E) + Banks sp).query (.inr (.inr (.inr i))))

noncomputable def expanded {α : Type} (π : Permutation) (P : QOC (Old E) (portSpec + sp) α) :=
  simulateQ (impl π) P

def weight (maskBank : Bool) : InstrIdx (Big E) ⊕ (Unit ⊕ (Unit ⊕ ι)) → Nat
  | .inr (.inl _) => if maskBank then 1 else 0
  | .inr (.inr (.inl _)) => if maskBank then 0 else 1
  | _ => 0

private theorem single {J α : Type} {s : OracleSpec J} (w : J → Nat) (j : J)
    (f : s.Range j → α) :
    WCount w ((liftM (s.query j) >>= fun u => pure (f u)) : OracleComp s α) (w j) := by
  rw [wCount_query_bind]
  exact ⟨le_rfl,fun _ => trivial⟩

private theorem gate_free (bank : Bool) (e : Equiv.Perm (Reg Work)) :
    WCount (weight (E := E) (ι := ι) bank) (gate (sp := sp) e) 0 := by
  exact single _ _ _

private theorem lower_count {X Y : Type} (b : Bool) (port : Driver E sp Unit)
    (lens : Equiv.Perm (Register X Y Work) → Equiv.Perm (Reg Work)) (w : Nat)
    (h : WCount (weight b) port w) (c : Circuit X Y Work) :
    WCount (weight b) (lower port lens c) (w*c.cost) := by
  induction c with
  | localOp e => simpa only [Circuit.cost,Nat.mul_zero,lower] using gate_free (sp := sp) (E := E) b (lens e)
  | port => simpa only [Circuit.cost,Nat.mul_one,lower] using h
  | seq a c ia ic => simpa only [Circuit.cost,Nat.mul_add,lower] using WCount.bind ia (fun _ => ic)

private theorem simple {J : Type} {s : OracleSpec J} (w : J → Nat) (j : J) :
    WCount w (liftM (s.query j) : OracleComp s _) (w j) := by
  simpa only [id_eq, bind_pure] using single (s := s) w j id

theorem expand_count (b : Bool) (p : Program Work) :
    WCount (weight (ι := ι) (E := E) b) (expand (sp := sp) p) (p.count b) := by
  induction p with
  | mask c =>
    have h := lower_count b (askMask (E := E) (sp := sp)) onMask
      (if b then 1 else 0) (simple _ _) c
    cases b <;> simpa only [Program.count,expand,ite_true,ite_false,Bool.false_eq_true,Nat.zero_mul,Nat.one_mul] using h
  | head c =>
    have h := lower_count b (askHead (E := E) (sp := sp)) onHead
      (if b then 0 else 1) (simple _ _) c
    cases b <;> simpa only [Program.count,expand,ite_true,ite_false,Bool.false_eq_true,Nat.zero_mul,Nat.one_mul] using h
  | localOp e => exact gate_free _ _
  | seq a c ia ic => exact WCount.bind ia (fun _ => ic)

theorem expanded_count (π : Permutation) (b : Bool) {α : Type} (P : QOC (Old E) (portSpec + sp) α)
    (n : Nat) (hc : CountBound isPort P n) : WCount (weight b) (expanded π P) (8*n) := by
  induction P using OracleComp.inductionOn generalizing n with
  | pure a => simp only [expanded,simulateQ_pure]; trivial
  | query_bind i k ih =>
    rw [countBound_query_bind] at hc
    simp only [expanded,simulateQ_bind,simulateQ_spec_query]
    rcases i with j | (⟨⟩|t)
    · change 0 ≤ 8*n ∧ ∀ r, WCount (weight b) (expanded π (k r)) (8*n - 0)
      exact ⟨Nat.zero_le _,fun r => ih r n (hc r)⟩
    · have hp := expand_count (sp := sp) (E := E) b (publicPort π)
      have eight : (publicPort π).count b = 8 := by
        cases b
        · exact (publicPort_cost π).2
        · exact (publicPort_cost π).1
      rw [eight] at hp
      have hh := WCount.bind hp (fun r => ih r (n-1) (by simpa [isPort] using hc.2 r))
      exact hh.mono (by have hn : 0 < n := hc.1; omega)
    · change 0 ≤ 8*n ∧ ∀ r, WCount (weight b) (expanded π (k r)) (8*n - 0)
      exact ⟨Nat.zero_le _,fun r => ih r n (hc r)⟩

end Reduction.ShakePermutation.RoundPort.Player
#print axioms Reduction.ShakePermutation.RoundPort.Player.expanded_count
