import Armwide.LoadProgram
import Armwide.SignStores
import Slhdsa.Proofs.Hw.ChainModel
namespace slhdsa.Armwide.Transitions
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def loadedWord (n : Nat) (src : Spec.Bytes) (i : Nat) : BitVec 32 :=
  let bytes := fun k => let off := (loadIndices n)[k]!; if off = 255 then 0#8 else src[off]!
  Arm.beWord (bytes i) (bytes (i+1)) (bytes (i+2)) (bytes (i+3))

def loadDigest (n : Nat) (src : Spec.Bytes) : Arm.V × Arm.V :=
  let w := loadedWord n src
  (⟨w 0,w 4,w 8,w 12⟩,⟨w 16,w 20,w 24,w 28⟩)

theorem load_content (n : Nat) (hn : n=16 ∨ n=24 ∨ n=32) (src : Spec.Bytes) (size : src.length = n) :
    Kernel.storeN n (loadDigest n src).1 (loadDigest n src).2 = src := by
  have cells : Kernel.storeN n (loadDigest n src).1 (loadDigest n src).2 =
      (List.range n).map (fun i => src[i]!) := by
    rcases hn with rfl|rfl|rfl <;>
      simp only [Kernel.storeN,loadDigest,vwords,List.flatMap_cons,List.flatMap_nil,loadedWord,Arm.beWord,beBytes_concat] <;> rfl
  rw [cells]
  apply List.ext_getElem (by simp [size])
  intro i hi hj
  simp [hj]

end slhdsa.Armwide.Transitions
