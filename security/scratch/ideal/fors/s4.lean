import Ideal.Realize.ForsAdv
import Ideal.Realize.ForsBound
open OracleComp OracleSpec SLHDSA SLHDSA.Security Reduction TweakableHash
namespace Ideal.Realize.Fors
open Ideal.Transport Reduction.Open Ideal.Realize

def Q1 : Prop := IsQueryBoundP (forsPhase1 Link.vp P₀) (fun t => isChal0 t = true) (openPreTargets Link.vp)
theorem q3 (h : Q1) : Q1 := h
theorem q4 : Q1 := forsPhase1_chal
theorem q5 : Q1 := by unfold Q1; exact forsPhase1_chal
end Ideal.Realize.Fors
