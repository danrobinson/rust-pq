import Ideal.Realize.WotsRealize
open Lean Meta Elab Command
elab "#size " n:ident : command => do
  let env ← getEnv
  let some ci := env.find? n.getId | throwError "no"
  logInfo m!"{ci.type.approxDepth} {ci.type.sizeWithoutSharing}"
#size Ideal.Realize.Wots.rUd_pick_chal
#size Ideal.Realize.Wots.rPre_choose_chal
#size Ideal.Realize.Wots.udSim_chal
#size Ideal.Realize.Wots.rTcrT_choose_chal
