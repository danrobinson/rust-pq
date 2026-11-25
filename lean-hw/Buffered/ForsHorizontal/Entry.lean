import Buffered.ForsHorizontal.Blocks
import Buffered.ForsHorizontal.Flush
import Buffered.ForsHorizontal.Indices
open Aeneas Aeneas.Std Result
namespace slhdsa.ForsHorizontal
open ShakeBatch NativeVerify Buffered
set_option maxHeartbeats 1500000
variable [kernel : Fused.Kernel]

/-- The extracted horizontal SHAKE FORS routine returns its FIPS subtree root at
every height used by Algorithm 16, including trees crossing the first 16K leaves. -/
theorem subtree_spec {N : Usize} (p : params.Params) (hp : PN p N)
    (sk seed : Array U8 N) (a : address.Adrs) (idx height : U32) (domain : Domain a)
    (lo : 3≤height.val) (hi : height.val≤14) (room : (idx.val+1)*2^height.val≤1048576)
    (perm : ActiveCorrect (Fused.machine kernel) kernel.active) :
    subtree sk seed a idx height ⦃ out => bytes out.val =
      Spec.forsNode (Shake.params p) (bytes sk.val) idx.val height.val (bytes seed.val) (adrsS a) ⦄ := by
  let z := UScalar.cast .Usize height
  have width : z.val=height.val := by dsimp [z];scalar_tac
  have fits : z ≤ 15#usize := by scalar_tac
  unfold subtree
  simp only [lift,bind_ok,show UScalar.cast .Usize height ≤ 15#usize from fits,decide_true,massert,ite_true]
  step as ⟨tag,_,tagEq⟩
  step as ⟨tree,treeEq⟩
  have dom : adrsS tree=adrsS a := by
    obtain ⟨typ,w2,w3⟩ := domain
    simp [treeEq,tagEq,adrsS,typ,w2,w3]
  simp only [core.ops.range.RangeInclusive.new,bind_ok]
  step with init_indices idx z _ (by omega) (by simpa only [width] using room) as ⟨indices,initial⟩
  step as ⟨shift,shiftVal⟩
  step as ⟨num,numVal,_⟩
  step as ⟨first,firstVal,_⟩
  have smallPow : 2^height.val≤1048576 := (Nat.le_mul_of_pos_left _ (Nat.succ_pos idx.val)).trans room
  have batch : num.val=2^(z.val-3) := by
    rw [numVal,Nat.shiftLeft_eq,Nat.one_mul,Nat.mod_eq_of_lt,shiftVal,width]
    have h := (Nat.pow_le_pow_right (by decide : 0<2) (show shift.val≤height.val by omega)).trans smallPow
    exact h.trans_lt (by scalar_tac : 1048576<U32.size)
  have offset : first.val=idx.val*2^z.val := by
    rw [firstVal,Nat.shiftLeft_eq,Nat.mod_eq_of_lt,width]
    exact (Nat.mul_le_mul_right _ (Nat.le_succ idx.val)).trans_lt (room.trans_lt (by scalar_tac : 1048576<U32.size))
  let zeros := Array.repeat N 0#u8
  let buf := Array.repeat 16#usize (Array.repeat 16#usize zeros)
  let len := Array.repeat 16#usize 0#usize
  let scratch := Array.repeat 8#usize tree
  let row := Array.repeat 8#usize zeros
  have empty : Grid (fors p sk seed a) idx.val z.val (produced 0) buf len indices := by
    constructor
    · intro h hh
      simp only [len,Array.repeat_val,List.getElem!_replicate _ (show h<(16#usize).val by change h<16;omega)]
      simp [waiting,produced]
    · intro h hh;rw [initial h hh];simp [nextBase,levelBase,produced,width]
    · intro h hh j live;simp [waiting,produced] at live
  step with blocks p hp sk seed a tree idx.val z num first buf len indices scratch row row (by omega) (by omega)
    (by simpa only [width] using room) batch offset dom empty domain perm as ⟨b,l,c,as',ls,rs,g⟩
  step with flush p hp sk seed a tree idx.val z b l c as' ls rs (by omega) (by omega)
    (by simpa only [width] using room) dom (batch ▸ g) perm as ⟨out,root⟩
  step as ⟨r,rRead⟩
  step as ⟨v,vRead⟩
  rw [vRead,←getElem!_pos,rRead,←getElem!_pos]
  exact root.trans (show fors p sk seed a z.val idx.val = _ by rw [fors,width])

end slhdsa.ForsHorizontal
