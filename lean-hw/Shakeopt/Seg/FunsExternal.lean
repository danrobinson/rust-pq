module
public import Shakeopt.Seg.Types
public import Slhdsa.Funs
@[expose] public section
open Aeneas Aeneas.Std Result

namespace ShakeoptSeg

abbrev shake256.Sponge.new := slhdsa.shake256.Sponge.new
abbrev shake256.Sponge.absorb := slhdsa.shake256.Sponge.absorb
abbrev shake256.Sponge.finish := slhdsa.shake256.Sponge.finish
abbrev shake.ht.ht_sign := @slhdsa.shake.ht.ht_sign
abbrev shake.ht.ht_verify := @slhdsa.shake.ht.ht_verify
abbrev shake.slh.digest_tree := slhdsa.shake.slh.digest_tree
abbrev shake.slh.digest_leaf := slhdsa.shake.slh.digest_leaf
abbrev shake.slh.slh_sign_internal := @slhdsa.shake.slh.slh_sign_internal
abbrev shake.slh.slh_verify_internal := slhdsa.shake.slh.slh_verify_internal
abbrev shake.slh.with_context := slhdsa.shake.slh.with_context
abbrev shake.fors.fors_sign := @slhdsa.shake.fors.fors_sign
abbrev shake.fors.fors_pk_from_sig := @slhdsa.shake.fors.fors_pk_from_sig
abbrev util.block := slhdsa.util.block

end ShakeoptSeg
