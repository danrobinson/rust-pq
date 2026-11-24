import Integration.SlhDsaShakePermutationFixSimulator
import Integration.SlhDsaShakePermutationFixProgram

namespace Reduction.ShakePermutation.Fix
namespace Circuit
variable {X Y Z W : Type}

def frame : Circuit X Y Z → Circuit X Y (Z × W)
  | .localOp e =>
    let assoc := Equiv.prodAssoc (X × Y) Z W
    .localOp (assoc.symm.trans ((e.prodCongr (Equiv.refl W)).trans assoc))
  | .port => .port
  | .seq a b => .seq a.frame b.frame

@[simp] theorem frame_cost (c : Circuit X Y Z) : (c.frame (W := W)).cost = c.cost := by
  induction c <;> simp [frame,cost, *]

theorem frame_run [AddCommGroup Y] (H : X → Y) (c : Circuit X Y Z) (xy : X × Y) (z : Z) (w : W) :
    (c.frame (W := W)).run H (xy,(z,w)) = ((c.run H (xy,z)).1,((c.run H (xy,z)).2,w)) := by
  induction c generalizing xy z with
  | localOp => rfl
  | port => rfl
  | seq a b ha hb => simp only [frame,run,Equiv.trans_apply,ha,hb,Prod.mk.eta]

open PQ.Interactive Quantum

/-- Transport of a circuit on a clean subspace. The embedding may preserve
an arbitrary untouched reference, and its input can be any density operator. -/
theorem transport_embedding {V : Type} [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [Fintype V]
    (e : Equiv.Perm (Register X Y Z)) (ι : V → WS X Y Z) (M : Matrix V V ℂ) :
    transport e (MatrixMap.conj (basisMatrix ι) M) =
      MatrixMap.conj (basisMatrix (fun v => (e (ι v).1,(ι v).2))) M := by
  let f := e.prodCongr (Equiv.refl Unit)
  change _ = MatrixMap.conj (basisMatrix (f ∘ ι)) M
  rw [basisMatrix_comp,MatrixMap.conj_mul,LinearMap.comp_apply,conj_basisMatrix_equiv]
  rfl

end Circuit

namespace Access
variable {T : ℕ} {X Y U : Type} [DecidableEq X] [AddCommGroup Y]
variable (A : Access X Y) (L : ℕ) (base : X)

abbrev Scratch (T : ℕ) (U : Type) := Data T × U

def zeroPath : Domain T := BList.ofList [] (by simp)
def scratch (u : U) : Scratch T U := ((zeroPath,0),u)

noncomputable def route (sel : U → Domain T) : Equiv.Perm (Scratch T U) := by
  classical
  exact Function.Involutive.toPerm (fun s => ((Equiv.swap zeroPath (sel s.2) s.1.1,s.1.2),s.2))
    (by intro s; simp)

def useAnswer (act : Rate → Equiv.Perm U) : Equiv.Perm (Scratch T U) where
  toFun s := (s.1,act s.1.2 s.2)
  invFun s := (s.1,(act s.1.2).symm s.2)
  left_inv s := by simp
  right_inv s := by simp

def xorAnswer (r : Rate) : Equiv.Perm Rate :=
  Function.Involutive.toPerm (fun x => rateXor x r) (by intro x; simp)

/-- Evaluate a corrected table entry selected in superposition by simulator
state, apply it as a control on the rest of the simulator, and uncompute.
The path register, rate register and public-port ancillas all return clean. -/
noncomputable def selected (sel : U → Domain T) (act : Rate → Equiv.Perm U) :
    Circuit X Y (Scratch T U) :=
  let addr : Circuit X Y (Scratch T U) := .localOp ((Equiv.refl _).prodCongr (route sel))
  let read : Circuit X Y (Scratch T U) := (A.simulate L base xorAnswer).frame
  let use : Circuit X Y (Scratch T U) := .localOp ((Equiv.refl _).prodCongr (useAnswer act))
  .seq addr (.seq read (.seq use (.seq read.reverse addr)))

theorem selected_cost (sel : U → Domain T) (act : Rate → Equiv.Perm U) :
    (A.selected L base sel act).cost ≤ 8*L+4 := by
  simp only [selected,Circuit.cost,Circuit.reverse_cost,Circuit.frame_cost]
  have := A.simulate_cost (T := T) L base xorAnswer
  omega

theorem selected_clean (sel : U → Domain T) (act : Rate → Equiv.Perm U)
    (stable : ∀ r u, sel (act r u) = sel u) (H : X → Y) (u : U) :
    (A.selected L base sel act).run H ((base,0),scratch u) =
      ((base,0),scratch (act (transform (A.value L H) (List.ofFn (sel u).2)) u)) := by
  classical
  let v := transform (A.value L H) (List.ofFn (sel u).2)
  have sim : (A.simulate L base xorAnswer).run H ((base,0),((sel u,0) : Data T)) =
      ((base,0),(sel u,v)) := by
    rw [simulate_clean]
    simp only [v,blocks,xorAnswer,Function.Involutive.toPerm]
    congr 2
    funext i
    simp [rateXor]
  have fwd (u' : U) : ((A.simulate L base xorAnswer).frame).run H ((base,0),((sel u,0),u')) =
      ((base,0),((sel u,v),u')) := by rw [Circuit.frame_run,sim]
  have back (u' : U) : (((A.simulate L base xorAnswer).frame).run H).symm ((base,0),((sel u,v),u')) =
      ((base,0),((sel u,0),u')) := (((A.simulate L base xorAnswer).frame).run H).symm_apply_eq.mpr (fwd u').symm
  simp [selected,Circuit.run,route,Function.Involutive.toPerm,scratch,fwd,useAnswer,
    Circuit.run_reverse,back,stable]
  rfl

open PQ.Interactive OracleSpec OracleComp Quantum Classical
variable [Fintype X] [Fintype Y] [Fintype U] [DecidableEq Y] [DecidableEq U]

/-- Born semantics of one selected corrected table query, in the exact
program interface used by the signature theorem and in the presence of a signer. -/
theorem selected_close_weight {ι σ α : Type} {sp : OracleSpec ι}
    (sel : U → Domain T) (act : Rate → Equiv.Perm U)
    (stable : ∀ r u, sel (act r u) = sel u) (H : X → Y)
    (impl : QueryImpl sp (StateT σ ProbComp)) (s : σ)
    (k : QOC (Register X Y (Scratch T U)) (portSpec + sp) α) (ev : α × σ → Prop) [DecidablePred ev]
    (M : Matrix U U ℂ) :
    qWeight ev (close impl (compileQ H ((A.selected L base sel act).program k)) s)
        (MatrixMap.conj (basisMatrix (fun u => (((base,(0:Y)),scratch (T := T) u),()))) M) =
      qWeight ev (close impl (compileQ H k) s)
        (MatrixMap.conj (basisMatrix (fun u =>
          (((base,(0:Y)),scratch (T := T) (act (transform (A.value L H) (List.ofFn (sel u).2)) u)),()))) M) := by
  rw [Circuit.program_close_weight,Circuit.transport_embedding]
  simp only [selected_clean A L base sel act stable H]

end Access
end Reduction.ShakePermutation.Fix
#print axioms Reduction.ShakePermutation.Fix.Access.selected_clean
#print axioms Reduction.ShakePermutation.Fix.Access.selected_cost
#print axioms Reduction.ShakePermutation.Fix.Access.selected_close_weight
