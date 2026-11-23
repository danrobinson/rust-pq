import Segmented.Continued
import Segmented.Models
import Segmentedapi.Funs
open Aeneas Aeneas.Std Result
namespace slhdsa.Segmented

abbrev impl256 := SegmentedApiRust.slh.message.Sha256.Insts.SlhdsaSlhMessageMessageHashArrayU328ArrayU83264

@[step] theorem continued256 (st : Std.Array U32 8#usize) (pre : Usize) (front msg : Slice U8)
    (aligned : pre.val%64=0)
    (space : Room (pre.val+front.length+msg.length) 72) :
    SegmentedApiRust.slh.message.continued impl256 st pre front msg ⦃ out =>
      bytes out.val = ser (hashFrom (wv st.val) (padFrom pre.val (bytes (front.val++msg.val)))) ⦄ := by
  apply continued_spec (model256) 64#usize (by decide)
  · apply block256
    exact compress_spec
  · exact aligned
  · exact Nat.le_trans (Nat.le_add_right _ _) space.1
  · intro state pos input align eq
    apply sha256_from_spec
    · exact align
    · rwa [eq]

abbrev impl512 := SegmentedApiRust.slh.message.Sha512.Insts.SlhdsaSlhMessageMessageHashArrayU648ArrayU864128

@[step] theorem continued512 (st : Std.Array U64 8#usize) (pre : Usize) (front msg : Slice U8)
    (aligned : pre.val%128=0)
    (space : pre.val+front.length+msg.length+144≤Usize.max) :
    SegmentedApiRust.slh.message.continued impl512 st pre front msg ⦃ out =>
      bytes out.val = S512.ser (S512.hashFrom (S512.wv st.val) (S512.padFrom pre.val (bytes (front.val++msg.val)))) ⦄ := by
  apply continued_spec (model512) 128#usize (by decide)
  · apply block512
    exact S512.compress_spec
  · exact aligned
  · omega
  · intro state pos input align eq
    apply S512.sha512_from_spec
    rwa [eq]

end slhdsa.Segmented
