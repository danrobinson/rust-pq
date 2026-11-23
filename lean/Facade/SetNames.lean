import Facade.Funs

/-! Readable names for the dictionaries Aeneas extracts from specialized
RustCrypto family types. The typenum indices occur in their Rust item names. -/
open Lean
namespace slh_dsa

private abbrev SetOf {P Sk Vk Sig : Type} (_ : params.Core P Sk Vk Sig) := P

local macro "named_set " short:ident " from " long:ident " using " coreId:ident : command => do
  let src := long.getId ++ `Insts
  let dest := short.getId ++ `Insts
  let coreSrc := mkIdent (src ++ coreId.getId)
  let coreDest := mkIdent (dest ++ coreId.getId)
  let source := mkIdent src
  let target := mkIdent dest
  let algorithm := mkIdent `Slh_dsaParamsDerAlgorithm
  let methods := #[`N, `sign, `verify, `keygen_seeds, `sk_from, `sig_from, `with_pkcs8, `with_spki].map mkIdent
  `(section
    abbrev $short := SetOf $coreSrc
    namespace $target
    export $source ($coreId $algorithm)
    end $target
    namespace $coreDest
    export $coreSrc ($methods*)
    end $coreDest
    end)

named_set params.Sha2_128s from
  params.Sha2L1UIntUIntUIntUIntUIntUTermB1B0B0B0B0UIntUIntUIntUIntUIntUTermB1B1B1B1B0
  using Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856
named_set params.Shake128s from
  params.ShakeUIntUIntUIntUIntUIntUTermB1B0B0B0B0UIntUIntUIntUIntUIntUTermB1B1B1B1B0
  using Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856
named_set params.Sha2_128f from
  params.Sha2L1UIntUIntUIntUIntUIntUTermB1B0B0B0B0UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B1B0
  using Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088
named_set params.Shake128f from
  params.ShakeUIntUIntUIntUIntUIntUTermB1B0B0B0B0UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B1B0
  using Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088
named_set params.Sha2_192s from
  params.Sha2L35UIntUIntUIntUIntUIntUTermB1B1B0B0B0UIntUIntUIntUIntUIntUIntUTermB1B0B0B1B1B1
  using Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224
named_set params.Shake192s from
  params.ShakeUIntUIntUIntUIntUIntUTermB1B1B0B0B0UIntUIntUIntUIntUIntUIntUTermB1B0B0B1B1B1
  using Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224
named_set params.Sha2_192f from
  params.Sha2L35UIntUIntUIntUIntUIntUTermB1B1B0B0B0UIntUIntUIntUIntUIntUIntUTermB1B0B1B0B1B0
  using Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664
named_set params.Shake192f from
  params.ShakeUIntUIntUIntUIntUIntUTermB1B1B0B0B0UIntUIntUIntUIntUIntUIntUTermB1B0B1B0B1B0
  using Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664
named_set params.Sha2_256s from
  params.Sha2L35UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0UIntUIntUIntUIntUIntUIntUTermB1B0B1B1B1B1
  using Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792
named_set params.Shake256s from
  params.ShakeUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0UIntUIntUIntUIntUIntUIntUTermB1B0B1B1B1B1
  using Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792
named_set params.Sha2_256f from
  params.Sha2L35UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0UIntUIntUIntUIntUIntUIntUTermB1B1B0B0B0B1
  using Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856
named_set params.Shake256f from
  params.ShakeUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0UIntUIntUIntUIntUIntUIntUTermB1B1B0B0B0B1
  using Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856

end slh_dsa
