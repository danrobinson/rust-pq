import Reduction.Gen.Final
open OracleComp OracleSpec ENNReal
#check ([]ₒ : OracleSpec PEmpty)
noncomputable instance : OracleSpec.AnswerMeasure ([]ₒ : OracleSpec PEmpty) :=
  @PFunctor.AnswerMeasure.mk ([]ₒ : OracleSpec PEmpty).toPFunctor (fun _ ↦ ⊤) (fun d ↦ d.elim) (fun d ↦ d.elim)
instance (d : PEmpty) : Fintype (([]ₒ : OracleSpec PEmpty).Range d) := d.elim
example : type_of% @Reduction.slhdsa_bytes_suf_cma_final := by
  intros
  exact Reduction.slhdsa_bytes_suf_cma_final ‹_› ‹_›
