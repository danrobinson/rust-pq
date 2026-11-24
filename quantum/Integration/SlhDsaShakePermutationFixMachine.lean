import Integration.SlhDsaShakePermutationFixWorkspace
import PQ.Interactive.QromBridgeTcr

/-! The bounded raw public oracle can run a simulator that chooses a corrected
sponge path coherently between arbitrary instruments, sampling and signing
queries. Instrument outcomes and signing queries are preserved verbatim. -/
namespace Reduction.ShakePermutation.Fix.Machine
open Quantum PQ.Interactive OracleSpec OracleComp Classical
open scoped ComplexOrder
variable {T : ℕ} {X Y U α β σ ι : Type} {sp : OracleSpec ι}
variable [Fintype X] [Fintype Y] [Fintype U] [DecidableEq X] [DecidableEq Y] [DecidableEq U] [AddCommGroup Y]

structure Read (U : Type) (T : ℕ) where
  sel : U → Domain T
  act : Rate → Equiv.Perm U
  stable : ∀ v u, sel (act v u) = sel u

abbrev reads (U : Type) (T : ℕ) : OracleSpec (Read U T) := fun _ => Unit
abbrev Source (U : Type) (T : ℕ) [Fintype U] (sp : OracleSpec ι) := QOC U (reads U T + sp)
variable (A : Access X Y) (L : ℕ) (base : X)

def effective (r : Read U T) (f : List Rate → Rate) : Equiv.Perm U where
  toFun u := r.act (f (List.ofFn (r.sel u).2)) u
  invFun u := (r.act (f (List.ofFn (r.sel u).2))).symm u
  left_inv u := by
    let val := fun p : Domain T => f (List.ofFn p.2)
    change (r.act (val (r.sel (r.act (val (r.sel u)) u)))).symm _ = u
    rw [r.stable,Equiv.symm_apply_apply]
  right_inv u := by
    have h (v : Rate) : r.sel ((r.act v).symm u) = r.sel u := by
      have := r.stable v ((r.act v).symm u)
      simpa using this.symm
    let val := fun p : Domain T => f (List.ofFn p.2)
    change r.act (val (r.sel ((r.act (val (r.sel u))).symm u))) _ = u
    rw [h,Equiv.apply_symm_apply]

noncomputable def idealImpl (f : List Rate → Rate) :
    QueryImpl (instrSpec U + (reads U T + sp)) (QOC U sp)
  | .inl j => liftM ((instrSpec U + sp).query (.inl j))
  | .inr (.inl r) => do
    let _ ← (instrSpec U + sp).query (.inl (unitaryIdx (basisMatrix (effective r f))
      (conjTranspose_basisMatrix_mul_self (effective r f).injective)))
    pure ()
  | .inr (.inr i) => liftM ((instrSpec U + sp).query (.inr i))

noncomputable def rawImpl (A : Access X Y) (L : ℕ) (base : X) : QueryImpl (instrSpec U + (reads U T + sp))
    (QOC (Workspace.W X Y T U) (portSpec + sp))
  | .inl j => liftM ((instrSpec (Workspace.W X Y T U) + (portSpec + sp)).query (.inl (Workspace.liftIdx (X := X) (Y := Y) (T := T) j)))
  | .inr (.inl r) => (A.selected L base r.sel r.act).program (pure ())
  | .inr (.inr t) => liftM ((instrSpec (Workspace.W X Y T U) + (portSpec + sp)).query (.inr (.inr t)))

noncomputable def ideal (f : List Rate → Rate) (p : Source U T sp α) := simulateQ (idealImpl f) p
noncomputable def raw (p : Source U T sp α) := simulateQ (rawImpl A L base) p

omit [AddCommGroup Y] in
theorem program_bind {Z : Type} [Fintype Z] [DecidableEq Z] (c : Circuit X Y Z)
    (p : QOC (Register X Y Z) (portSpec + sp) α) (k : α → QOC _ (portSpec + sp) β) :
    c.program p >>= k = c.program (p >>= k) := by
  induction c generalizing p with
  | localOp => simp [Circuit.program,bind_assoc]
  | port => simp [Circuit.program,bind_assoc]
  | seq a b ha hb => simp [Circuit.program,ha,hb]

/-- The raw signing-oracle execution has the exact outcome and state weights
of the ideal corrected-table execution, for every public table. -/
theorem weight (H : X → Y) (p : Source U T sp α) (ev : α × σ → Prop) [DecidablePred ev]
    (impl : QueryImpl sp (StateT σ ProbComp)) (s : σ) (M : Matrix U U ℂ) :
    qWeight ev (close impl (compileQ H (raw A L base p)) s) (Workspace.state base M) =
      qWeight ev (close impl (ideal (transform (A.value L H)) p) s) M := by
  unfold raw ideal
  induction p using OracleComp.inductionOn generalizing s M with
  | pure a => simp [compileQ,Workspace.state_trace]
  | query_bind t k ih =>
    rw [simulateQ_bind,simulateQ_spec_query,simulateQ_bind,simulateQ_spec_query]
    rcases t with j | r | t
    · simp only [rawImpl,idealImpl]
      erw [compileQ_instr_bind H (Workspace.liftIdx (X := X) (Y := Y) (T := T) j) (fun i => simulateQ (rawImpl A L base) (k i))]
      rw [close_instr_bind,close_instr_bind,qWeight_instr_bind,qWeight_instr_bind]
      exact Finset.sum_congr rfl fun i _ => (congrArg _ (Workspace.lift_branch base j i M)).trans (ih i s _)
    · simp only [rawImpl,idealImpl,program_bind,pure_bind,bind_assoc]
      erw [Access.selected_close_weight A L base r.sel r.act r.stable H impl s _ ev M]
      rw [close_instr_bind,qWeight_instr_bind]
      rw [Fin.sum_univ_one]
      let f := transform (A.value L H)
      let e := effective r f
      change qWeight ev _ (MatrixMap.conj (basisMatrix ((Workspace.embed base) ∘ e)) M) = _
      rw [basisMatrix_comp,MatrixMap.conj_mul,LinearMap.comp_apply]
      exact ih () s _
    · simp only [rawImpl,idealImpl]
      erw [compileQ_query_bind H t (fun v => simulateQ (rawImpl A L base) (k v))]
      rw [close_query_bind,close_query_bind]
      rw [qWeight_liftU_bind_tsum,qWeight_liftU_bind_tsum]
      exact tsum_congr fun z => congrArg _ (ih z.1 z.2 M)

end Reduction.ShakePermutation.Fix.Machine
#print axioms Reduction.ShakePermutation.Fix.Machine.weight
