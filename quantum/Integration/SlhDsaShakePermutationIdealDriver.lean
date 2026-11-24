import Integration.SlhDsaShakePermutationFixBound
import Integration.SlhDsaShakePermutationPlayer
import Integration.SlhDsaShakePermutationRelabel
import Integration.SlhDsaShakePermutationGraph
import QuantumFoundations.SubInstrument.Relabel

/-! Ideal execution of the expanded two-bank permutation forger. The capacity
masks live in one compressed database. A head query on a reached capacity
uses the corrected external XOF on its selected path. Unreached capacities
use an independent private mask. -/
namespace Reduction.ShakePermutation.IdealDriver
open Classical Quantum OracleSpec OracleComp PQ.Interactive Fix Fix.Machine RoundPort Player Tails
open Matrix
open scoped ComplexOrder
set_option maxRecDepth 8192
abbrev Db := Database MaskAddr Capacity
abbrev State (E : Type) := Big E × Db
abbrev BehindMask (E : Type) := Old E × HeadReg × Words
abbrev BehindHead (E : Type) := Old E × MaskReg × Words

def maskSplit (E : Type) : State E ≃ (MaskReg × Db) × BehindMask E where
  toFun s := ((s.1.2.1,s.2),(s.1.1,s.1.2.2.1,s.1.2.2.2))
  invFun s := ((s.2.1,s.1.1,s.2.2.1,s.2.2.2),s.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def headSplit (E : Type) : State E ≃ ((Db × Capacity) × Rate) × BehindHead E where
  toFun s := (((s.2,s.1.2.2.1.1),s.1.2.2.1.2),(s.1.1,s.1.2.1,s.1.2.2.2))
  invFun s := ((s.2.1,s.2.2.1,(s.1.1.2,s.1.2),s.2.2.2),s.1.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

variable {E : Type} [Fintype E] [DecidableEq E] (π : Permutation) (T : ℕ) (h : RateMask)

private noncomputable def oneIdx {V : Type} [Fintype V] (step : SubInstrument V V Unit) (hs : step.Lossless) : InstrIdx V :=
  ⟨0,step.comap (fun _ : Fin 1 => ()) fin1_bijective.injective,
    DSubInstrument.Lossless.comap hs fin1_bijective⟩

private noncomputable def inFrame {V Z W : Type} [Fintype V] [Fintype Z] [Fintype W]
    (j : InstrIdx V) (e : V × Z ≃ W) : InstrIdx W :=
  ⟨j.1,(j.2.1.frame Z).reindex e e,(j.2.2.frame Z).reindex e e⟩

/-- The only oracle consulted by a mask-bank call is the simulator's private
compressed capacity-mask database. -/
noncomputable def maskIdx : InstrIdx (State E) :=
  inFrame (oneIdx (compressedQuery MaskAddr Capacity) (lossless_compressedQuery (X := MaskAddr) (Y := Capacity))) (maskSplit E).symm

noncomputable def pick (key : Db × Capacity) : Option (Relabel.Path T × Rate) :=
  Relabel.chosen π (half key.1 false) (half key.1 true) T key.2

noncomputable def path (key : Db × Capacity) : Domain T :=
  ((pick π T key).map Prod.fst).getD Access.zeroPath

noncomputable def maskedValue (v : Rate) (key : Db × Capacity) : Rate :=
  match pick π T key with
  | none => h key.2
  | some (_,head) => rateXor v head

noncomputable def driveHead : Read (State E) T where
  sel s := path π T ((headSplit E s).1.1)
  act v := (headSplit E).trans (((oracleEquiv (maskedValue π T h v)).prodCongr (Equiv.refl _)).trans (headSplit E).symm)
  stable _ _ := rfl

omit [Fintype E] [DecidableEq E] in
/-- A selected read implements the routed additive head port on arbitrary
coherent database and query labels. -/
theorem head_action (f : List Rate → Rate) (s : State E) :
    headSplit E (effective (driveHead (E := E) π T h) f s) =
      let (key,y) := (headSplit E s).1
      let val := match pick π T key with
        | none => h key.2
        | some (p,head) => rateXor (f (List.ofFn p.2)) head
      ((key,y+val),(headSplit E s).2) := by
  change (headSplit E) ((headSplit E).symm _) = _
  rw [Equiv.apply_symm_apply]
  change (((headSplit E s).1.1,(headSplit E s).1.2 +
    maskedValue π T h (f (List.ofFn (path π T (headSplit E s).1.1).2)) (headSplit E s).1.1),(headSplit E s).2) = _
  cases he : pick π T ((headSplit E s).1.1) with
  | none => simp [maskedValue,he]
  | some p =>
    have pa : path π T ((headSplit E s).1.1) = p.1 := by simp [path,he]
    rw [pa]
    simp [maskedValue,he]

variable {ι α : Type} {sp : OracleSpec ι}

noncomputable def lower : QueryImpl (instrSpec (Big E) + Banks sp) (Source (State E) T sp)
  | .inl j => liftM ((instrSpec (State E) + (reads (State E) T + sp)).query
      (.inl ⟨j.1,j.2.1.frame Db,j.2.2.frame Db⟩))
  | .inr (.inl ()) => do
    let _ ← (instrSpec (State E) + (reads (State E) T + sp)).query (.inl maskIdx)
    pure ()
  | .inr (.inr (.inl ())) => liftM ((instrSpec (State E) + (reads (State E) T + sp)).query (.inr (.inl (driveHead π T h))))
  | .inr (.inr (.inr i)) => liftM ((instrSpec (State E) + (reads (State E) T + sp)).query (.inr (.inr i)))

noncomputable def run (p : Driver E sp α) := simulateQ (lower π T h) p

def start (w : WS Port Words E) : State E :=
  ((w.1,(baseMask,0),(0,0),0),Database.empty)

noncomputable def forger (F : PortForger Port Words E) : Machine.Forger (State E) T where
  main pk := run π T h (expanded π (F.main pk))
  initial := MatrixMap.conj (basisMatrix start) F.ρ₀
  pos := (MatrixMap.isCP_conj _).posSemidef F.posSemidef
  trace := by
    have inj : Function.Injective (start (E := E)) := fun _ _ eq => Prod.ext (congrArg (fun w => w.1.1) eq) (Subsingleton.elim ..)
    rw [MatrixMap.conj_apply,Matrix.trace_mul_cycle,conjTranspose_basisMatrix_mul_self inj,Matrix.one_mul,F.trace_eq_one]

end Reduction.ShakePermutation.IdealDriver
#print axioms Reduction.ShakePermutation.IdealDriver.head_action
