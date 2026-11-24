import Segmented.Loop
import Armstream.Proof
open Aeneas Aeneas.Std Result
namespace slhdsa.Segmented

def model256 : Hash (Std.Array U32 8#usize) (Std.Array U8 32#usize) Spec.Bytes where
  digest st pre input := ser (hashFrom (wv st.val) (padFrom pre (bytes input)))
  output out := bytes out.val

theorem block256 {H} (alg : Impl H (Std.Array U32 8#usize) (Std.Array U8 32#usize) 64#usize)
    (compress : ∀ st (data : Slice U8) (off : Usize), off.val+64≤data.length →
      alg.compress st data off ⦃ out => wv out.val =
        Spec.SHA256.compress (wv st.val) (((bytes data.val).drop off.val).take 64) ⦄) :
    BlockRule model256 alg := by
  intro st data off room
  change off.val+64≤data.length at room
  apply WP.spec_mono (compress st data off room)
  intro next eq prior suffix
  have len : (((bytes data.val).drop off.val).take 64).length=64 := by
    simp only [List.length_take,List.length_drop,bytes_length]
    change min 64 (data.length-off.val)=64
    omega
  simp only [show (64#usize).val = 64 from rfl, model256,bytes,List.map_append,List.map_take,List.map_drop]
  simp only [bytes] at eq len
  rw [padFrom_append64 _ _ _ len,hashFrom_append64 _ _ _ len,eq]

def model512 : Hash (Std.Array U64 8#usize) (Std.Array U8 64#usize) Spec.Bytes where
  digest st pre input := S512.ser (S512.hashFrom (S512.wv st.val) (S512.padFrom pre (bytes input)))
  output out := bytes out.val

theorem block512 {H} (alg : Impl H (Std.Array U64 8#usize) (Std.Array U8 64#usize) 128#usize)
    (compress : ∀ st (data : Slice U8) (off : Usize), off.val+128≤data.length →
      alg.compress st data off ⦃ out => S512.wv out.val =
        Spec.SHA512.compress (S512.wv st.val) (((bytes data.val).drop off.val).take 128) ⦄) :
    BlockRule model512 alg := by
  intro st data off room
  change off.val+128≤data.length at room
  apply WP.spec_mono (compress st data off room)
  intro next eq prior suffix
  have len : (((bytes data.val).drop off.val).take 128).length=128 := by
    simp only [List.length_take,List.length_drop,bytes_length]
    change min 128 (data.length-off.val)=128
    omega
  simp only [show (128#usize).val = 128 from rfl, model512,bytes,List.map_append,List.map_take,List.map_drop]
  simp only [bytes] at eq len
  rw [S512.padFrom_append128 _ _ _ len,S512.hashFrom_append128 _ _ _ len,eq]

end slhdsa.Segmented
