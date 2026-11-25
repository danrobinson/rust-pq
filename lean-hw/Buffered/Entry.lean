import Buffered.Large
import Buffered.Small
open Aeneas Aeneas.Std Result
namespace slhdsa.Buffered
open ShakeBatch NativeVerify
set_option linter.concreteInstances false
variable [kernel : Kernel]

theorem subtree_spec {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (idx height : U32) (a : address.Adrs) (lo : 1≤height.val) (hi : height.val≤9)
    (room : (idx.val+1)*2^height.val≤512) (small : SmallLeaves p sk seed a)
    (active : ActiveCorrect (machine kernel) kernel.active)
    (process : 3≤height.val → ProcessAt p sk seed a idx height) :
    subtree sk seed idx height a ⦃ out => bytes out.val =
      Spec.xmssNode (Shake.params p) (bytes sk.val) idx.val height.val (bytes seed.val) (adrsS a) ⦄ := by
  by_cases h1 : height=1#u32
  · subst height
    exact height_one p hp sk seed idx a small (by change (idx.val+1)*2≤512 at room; omega)
  by_cases h2 : height=2#u32
  · subst height
    exact height_two p hp sk seed idx a small (by change (idx.val+1)*4≤512 at room; omega) active
  have enough : 3≤height.val := by
    have one : height.val≠1 := fun e => h1 (UScalar.eq_of_val_eq e)
    have two : height.val≠2 := fun e => h2 (UScalar.eq_of_val_eq e)
    omega
  exact large_spec p sk seed a idx height enough hi room (process enough)

end slhdsa.Buffered
