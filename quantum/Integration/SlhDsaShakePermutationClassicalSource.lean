import Integration.SlhDsaShakePermutationClassicalByteGame

namespace Reduction.ShakePermutation.Classic
open Classical OracleSpec OracleComp MLink SLHDSA PQ.Interactive
open Honest (ByteMessage ByteSig)
open SetOracle (uniformMean)
open scoped ENNReal
noncomputable section
set_option maxRecDepth 8192

abbrev Source (S : Sha2Set) (N : ℕ) := Compression.ClassicalPort.Reads (ShakeApi.Input N) (Bytes S.vp.params.m) SignSpec

variable (S : Sha2Set) (N T : ℕ) (cap : Completion.blockCap N ≤ T)
    (g : Completion.Private T) (caps : Fix.Domain T → Capacity) (side : Port → Words)

def rowCall {Z : Type} (j : Row T) (cont : Words → OracleComp (Source S N) Z) : OracleComp (Source S N) Z :=
  match j with
  | .inr u => cont (side u)
  | .inl a =>
    match ShakeXof.locate (Completion.address cap) a with
    | none => cont (join (Completion.equiv.symm (g a)) (caps a))
    | some x => (Source S N).query (.inl x) >>= fun v => cont
        (join (Completion.equiv.symm (ShakeXof.replaceHead (g a) v)) (caps a))

def sourceProgram {Z : Type} (P : OracleComp (Compression.ClassicalPort.Reads Port Words SignSpec) Z) :
    EdgeTrace Words → OracleComp (Source S N) Z :=
  OracleComp.construct (C := fun _ => EdgeTrace Words → OracleComp (Source S N) Z)
    (fun z _ => pure z) (fun i _ k t => match i with
      | .inl (d,x) => if h : old t d x then k h.choose t else
        rowCall S N T cap g caps side (publicRow T t d x) (fun y => k y (edge d x y::t))
      | .inr i => (Source S N).query (.inr i) >>= fun y => k y t) P

def sourceForger (F : CForger Port Words) : CForger (ShakeApi.Input N) (Bytes S.vp.params.m) :=
  fun pk => sourceProgram S N T cap g caps side (F pk) []

variable (raw : ShakeApi.RawTable S N)
local notation "WORLD" => banks T (Completion.complete S cap g raw) caps side

theorem row_value (A : Scheme ProbComp) (pk sk : List SLHDSA.Byte) (fresh : Fresh) (j : Row T)
    (cont : Words → OracleComp (Source S N) Claim) (log : Log) :
    playerValue (fun x (s : Unit) => (raw x,s)) A pk sk fresh (rowCall S N T cap g caps side j cont) () log =
      playerValue (fun x (s : Unit) => (raw x,s)) A pk sk fresh (cont (WORLD j)) () log := by
  cases j with
  | inr u => rfl
  | inl a =>
    cases e : ShakeXof.locate (Completion.address cap) a with
    | none => simp only [rowCall,e,banks,Sum.elim_inl,Completion.complete,ShakeXof.write,Option.elim_none]
    | some x =>
      simp only [rowCall,e,banks,Sum.elim_inl,Completion.complete,ShakeXof.write,Option.elim_some]
      rfl

theorem source_value (A : Scheme ProbComp) (pk sk : List SLHDSA.Byte) (fresh : Fresh)
    (P : OracleComp (Compression.ClassicalPort.Reads Port Words SignSpec) Claim) (t : EdgeTrace Words) (log : Log) :
    playerValue (fun x (s : Unit) => (raw x,s)) A pk sk fresh (sourceProgram S N T cap g caps side P t) () log =
      playerValue (fun x t => visible T WORLD t x.1 x.2) A pk sk fresh P t log := by
  induction P using OracleComp.inductionOn generalizing t log with
  | pure => rfl
  | query_bind i k ih =>
    rcases i with ⟨d,x⟩|n|msg
    · change playerValue _ _ _ _ _ (if known : old t d x then sourceProgram _ _ _ _ _ _ _ (k known.choose) t else
          rowCall _ _ _ _ _ _ _ _ (fun y => sourceProgram _ _ _ _ _ _ _ (k y) (edge d x y::t))) () log =
        playerValue _ _ _ _ _ (k (visible T WORLD t d x).1) (visible T WORLD t d x).2 log
      unfold visible
      split
      · exact ih _ _ _
      · rw [row_value]
        exact ih _ _ _
    · exact congrArg (@uniformMean (Fin (n+1)) _) (funext fun v => ih v t log)
    · exact congrArg (fun f => coinValue f (A.sign pk sk msg)) (funext fun sig => ih sig t _)

theorem byte_ideal (fixed : ShakeApi.Xof S) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    (F : CForger Port Words) (fresh : Fresh) :
    let attacker := liftClassical (BList.ofList [] (by simp)) (sourceForger S N T cap g caps side F)
    idealOuter S N T WORLD raw (fun v => hit (v=true))
      (byteGame S N (Honest.rawScheme S N fixed rand seeds) F fresh) [] =
        qWeight (·=true) (qSigExperiment fresh (ShakeApi.rawForger S N rand seeds attacker raw)) attacker.ρ₀ := by
  let attacker := sourceForger S N T cap g caps side F
  change _ = qWeight _ (qSigExperiment fresh ((liftClassical _ attacker).at raw (ShakeApi.scheme S rand seeds (ShakeApi.extend raw)))) _
  rw [ideal_mixed,service_game,Honest.runRaw,lift_value]
  unfold sigValue
  apply congrArg (fun f => coinValue f (ShakeApi.scheme S rand seeds (ShakeApi.extend raw)).keygen)
  funext ks
  exact (source_value S N T cap g caps side raw _ ks.1 ks.2 fresh (F ks.1) [] []).symm

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.byte_ideal
