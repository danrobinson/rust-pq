import Ideal.Games.TcrDefs
open OracleComp OracleSpec ENNReal
#check @prEvent_eq_evalDist_of_discrete
#check @prEvent_eq_evalDist_singleton
#check @prEvent_pure
#check @prEvent_map
#check @prEvent_mono
#check @prEvent_le_one
#check @prEvent_eq_zero_of_forall_not
#check @prEvent_bind_le_prEvent_add
#check @prEvent_bind_le_prEvent_add_of_support
#check @prEvent_bind_le_of_forall_le_of_support
#check @QueryImpl.simulateQ_compose
#check @OracleComp.simulateQ_run_simulateQ_run_preservesInv
#check @OracleComp.run_simulateQ_query_bind
#check @OracleSpec.simulateQ_romImpl_liftM_run
#check @randomOracle.run_eq
#check @prEvent_uniformSample_eq_singleton
#check @prEvent_congr
#check @OracleComp.mem_support_bind_iff
#check @isQueryBoundP_query_bind_iff
#check @roSim.run_apply_inl
#check @QueryCache.cacheQuery_of_ne
example {St Blk} [DecidableEq St] [DecidableEq Blk] [SampleableType St] (x : ProbComp Bool) : 𝒟[x] {true} = Pr{let b ← x}[b = true] := by
  rw [prEvent_eq_evalDist_singleton]
