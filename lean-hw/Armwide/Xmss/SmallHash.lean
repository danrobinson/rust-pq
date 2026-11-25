import Armwide.SignBlocks
import Armwide.SignLoad

open Aeneas Aeneas.Std Result
namespace slhdsa.ArmXmss
open Armwide Armwide.Transitions Spec.SHA256
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def finish16 (both : Bool) (state : List Word) (blk : Spec.Bytes) (head : Arm.V × Arm.V × Arm.V) :=
  let out := Kernel.finishFromR4 both state head.2.1 head.2.2 head.1 (beV blk 16) (beV blk 32) (beV blk 48)
  Kernel.storeN 16 out.1 out.2

private theorem finish16_spec (both : Bool) (st : List Word) (hs : st.length=8)
    (blk : Spec.Bytes) (size : blk.length=64) :
    finish16 both st blk (Kernel.makeHead st blk) = (ser (compress st blk)).take 16 := by
  have first (lo hi : Arm.V) : (Kernel.storeN 32 lo hi).take 16=Kernel.storeN 16 lo hi := by rfl
  cases both with
  | false =>
    have check := Kernel.finishFromR4_storeN_eq_fips 16 (by decide) st hs blk size
    generalize Kernel.makeHead st blk = head at check ⊢
    rcases head with ⟨m,a,e⟩
    generalize Kernel.finishFromR4 false st a e m (beV blk 16) (beV blk 32) (beV blk 48) = out at check ⊢
    exact check
  | true =>
    have check := Kernel.finishFromR4_storeN_eq_fips 32 (by decide) st hs blk size
    generalize Kernel.makeHead st blk = head at check ⊢
    rcases head with ⟨m,a,e⟩
    unfold finish16
    change (let out := Kernel.finishFromR4 true st a e m (beV blk 16) (beV blk 32) (beV blk 48)
            Kernel.storeN 32 out.1 out.2) = _ at check
    generalize Kernel.finishFromR4 true st a e m (beV blk 16) (beV blk 32) (beV blk 48) = out at check ⊢
    simpa only [first,List.take_take,show min 16 32 = 16 by decide,ser] using congrArg (List.take 16) check

/-- The 4-lane path computes both output registers. The 2- and 1-lane paths
only compute the register used by the 16-byte parent store. -/
def smallHash (both : Bool) (state : List Word) (a : Spec.Adrs) (index : Nat) (left right : Spec.Bytes) :=
  let lo := (loadDigest 16 left).1
  let hi := (loadDigest 16 right).1
  let block := nativeBlock 32 a a.word2 index lo hi
  let head := Kernel.makeHead state {a with word2:=0,word3:=0}.compress
  finish16 both state block head

theorem smallHash_fips (p : Spec.Params) [Fact (p.family=.sha2)] (width : p.n=16) (pk : Spec.Bytes)
    (seedSize : pk.length=16) (a : Spec.Adrs) (height : a.word2<65536) (index : Nat)
    (left right : Spec.Bytes) (hl : left.length=16) (hr : right.length=16) (both : Bool) :
    smallHash both (seedState 16 pk) a index left right = Spec.H p pk {a with word3 := index} (left++right) := by
  let lo := (loadDigest 16 left).1
  let hi := (loadDigest 16 right).1
  let st := seedState 16 pk
  let blk := nativeBlock 32 a a.word2 index lo hi
  have payload : Kernel.storeN 32 lo hi=left++right := by
    change Kernel.storeN 16 lo (loadDigest 16 left).2 ++ Kernel.storeN 16 hi (loadDigest 16 right).2=_
    rw [show Kernel.storeN 16 lo (loadDigest 16 left).2=left from load_content 16 (by decide) left hl,
      show Kernel.storeN 16 hi (loadDigest 16 right).2=right from load_content 16 (by decide) right hr]
  have padded : blk=padFrom 64 ({a with word3:=index}.compress++(left++right)) := by
    simpa only [payload] using native_block_padded 32 (by decide) a a.word2 index height lo hi
  have length : blk.length=64 := by
    rw [padded,padFrom_short _ _ (adrs_compress_length _) (by simp [hl,hr])]
    simp [adrs_compress_length,hl,hr]
  have shared : Kernel.makeHead st {a with word2:=0,word3:=0}.compress=Kernel.makeHead st blk := by
    unfold Kernel.makeHead blk nativeBlock
    rw [compress_eq]
    rfl
  have hst : st.length=8 := by simp [st,seedState,compress]
  have headEq := congrArg (finish16 both st blk) shared
  have tweak : (ser (compress st blk)).take 16 = th256 16 pk {a with word3:=index} (left++right) := by
    rw [padded]
    exact th256_one 16 pk seedSize (by decide) _ _ (by simp [hl,hr])
  have fips : th256 16 pk {a with word3:=index} (left++right) =
      Spec.H p pk {a with word3:=index} (left++right) := by simp only [H_eq,width,ite_true]
  exact headEq.trans ((finish16_spec both st hst blk length).trans (tweak.trans fips))

end slhdsa.ArmXmss
