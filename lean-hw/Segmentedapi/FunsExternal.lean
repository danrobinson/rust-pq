module
public import Segmentedapi.Types
public import Segmented.Funs
public import Slhdsa.Funs
@[expose] public section
open Aeneas Aeneas.Std Result

namespace SegmentedApiRust
abbrev hash.mgf1_sha256 := slhdsa.hash.mgf1_sha256
abbrev hash.mgf1_sha512 := slhdsa.hash.mgf1_sha512
abbrev sha256.compress := slhdsa.sha256.compress
abbrev sha256.sha256_from := slhdsa.sha256.sha256_from
abbrev sha512.compress := slhdsa.sha512.compress
abbrev sha512.sha512_from := slhdsa.sha512.sha512_from

abbrev slh.message.continued := @SegmentedRust.slh.message.continued

end SegmentedApiRust
