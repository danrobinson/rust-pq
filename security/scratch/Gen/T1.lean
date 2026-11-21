import Reduction.Linear
open OracleComp OracleSpec ENNReal MeasureTheory

#check @prEvent_bind_eq_lintegral_of_discrete
#check @evalDist_liftM_query_apply
#check @prEvent_eq_evalDist_singleton
#check @prEvent_pure
#check @QueryImpl.simulateQ_compose
#check @simulateQ_spec_query
#check @evalDist_bind
#check @Reduction.prTrue_bind_congr
#check @evalDist_map
#check @prEvent_bind_eq_tsum
#check @probOutput_bind_eq_tsum
#check @OracleComp.inductionOn
#check @OracleComp.construct
example (g : ProbComp Bool) : 𝒟[g] {true} = Pr{let x ← g}[x = true] := by exact?
