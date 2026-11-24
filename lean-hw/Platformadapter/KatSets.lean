import Platformadapter.Kat
import Platformadapter.Errors
open Aeneas Aeneas.Std Result
open slh_dsa
namespace slh_dsa.Kat

local macro "set_checks " alg:ident err:ident coreId:ident pn:ident param:ident spec:ident pEq:ident n:term:max : command => do
  let kg := Lean.mkIdent (coreId.getId ++ `keygen_seeds)
  let sign := Lean.mkIdent (coreId.getId ++ `sign_internal)
  let verify := Lean.mkIdent (coreId.getId ++ `verify_internal)
  let context := Lean.mkIdent (coreId.getId ++ `sign)
  `(section
    theorem $alg : Algorithms $coreId $spec := by
      rw [←$pEq:term]
      apply kat_algorithms _ _ $pn (by decide) (by decide) (by rw [$pEq:term]; decide) rfl rfl rfl
      · funext a b c sk pk
        change $kg:ident a b c sk pk = _
        unfold $kg:ident
        simp only [$param:term,bind_ok,scrub_returns]
        exact Std.bind_pure _
      · intro m sk r dest
        change $sign:ident m sk r dest = _
        unfold $sign:ident
        cases r <;> simp only [params.split,$param:term,lift,bind_ok,uncurry,scrub_returns,
          Option.isSome, Option.getD]
        all_goals exact Std.bind_pure _
      · funext m sig pk
        change $verify:ident m sig pk = _
        unfold $verify:ident
        simp [$param:term]
    theorem $err : ContextErrors $coreId (UScalar.val $n) := by
      apply context_errors (N:=$n) $coreId _ rfl rfl
      intro m ctx sk r dest
      change $context:ident m ctx sk r dest = _
      unfold $context:ident
      cases r <;> simp only [params.split,$param:term,lift,bind_ok,uncurry,scrub_returns,
        Option.isSome, Option.getD]
      all_goals exact Std.bind_pure _
    end)

set_checks sha2_128s_algorithms sha2_128s_errors params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856
  _root_.slhdsa.sha2_128s.pn slh_dsa.slhdsa.sets.sha2_128s.params.PARAMS
  Spec.sha2_128s _root_.slhdsa.sha2_128s.hP 16#usize

set_checks sha2_128f_algorithms sha2_128f_errors params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088
  _root_.slhdsa.sha2_128f.pn slh_dsa.slhdsa.sets.sha2_128f.params.PARAMS
  Spec.sha2_128f _root_.slhdsa.sha2_128f.hP 16#usize

set_checks sha2_192s_algorithms sha2_192s_errors params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224
  _root_.slhdsa.sha2_192s.pn slh_dsa.slhdsa.sets.sha2_192s.params.PARAMS
  Spec.sha2_192s _root_.slhdsa.sha2_192s.hP 24#usize

set_checks sha2_192f_algorithms sha2_192f_errors params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664
  _root_.slhdsa.sha2_192f.pn slh_dsa.slhdsa.sets.sha2_192f.params.PARAMS
  Spec.sha2_192f _root_.slhdsa.sha2_192f.hP 24#usize

set_checks sha2_256s_algorithms sha2_256s_errors params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792
  _root_.slhdsa.sha2_256s.pn slh_dsa.slhdsa.sets.sha2_256s.params.PARAMS
  Spec.sha2_256s _root_.slhdsa.sha2_256s.hP 32#usize

set_checks sha2_256f_algorithms sha2_256f_errors params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856
  _root_.slhdsa.sha2_256f.pn slh_dsa.slhdsa.sets.sha2_256f.params.PARAMS
  Spec.sha2_256f _root_.slhdsa.sha2_256f.hP 32#usize
end slh_dsa.Kat
