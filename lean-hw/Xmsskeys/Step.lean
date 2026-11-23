import Xmsskeys.Batch
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.XmssKeys
abbrev Groups (N : Usize) := core.iter.adapters.enumerate.Enumerate (XmssKeysRust.core.slice.iter.ChunksMut (Array U8 N))
abbrev Back (N : Usize) := Groups N → Groups N
abbrev nextGroup {N} := XmssKeysRust.core.iter.adapters.enumerate.IteratorEnumerate.next
  (XmssKeysRust.core.slice.iter.ChunksMut.Insts.CoreIterTraitsIteratorIteratorMutASlice (Array U8 N))

private theorem bindRight {α β : Type} (x : Result α) {f g : α → Result β} (h : ∀ a,f a=g a) : Std.bind x f = Std.bind x g := by rw [funext h]

theorem group_body {N} (G L : Usize) (seed : XmssKeysRust.hash.Seed N) (sk : Array U8 N)
    (a : XmssKeysRust.address.Adrs) (first : U32) (len group : Usize) (out : Wots.Rows N)
    (it next : Groups N) (back : Back N) (restore : Groups N → Option (Usize × Wots.Rows N) → Groups N)
    (more : nextGroup it = ok (some (group,out),next,restore)) :
    XmssKeysRust.xmss.wide.keys_loop0.body G L seed sk a first len it back =
      (do let keys ← oneGroup G L seed sk a first len group out
          ok (ControlFlow.cont (next,fun e => back (restore e (some (group,keys)))))) := by
  unfold XmssKeysRust.xmss.wide.keys_loop0.body
  change XmssKeysRust.core.iter.adapters.enumerate.IteratorEnumerate.next _ it = _ at more
  rw [more]
  unfold oneGroup prepareAll digestPrefix
  by_cases width : N=16#usize <;> simp only [width,ite_true,ite_false,lift,bind_tc_eq,Std.bind_assoc,bind_ok]
  all_goals
    repeat' (apply bindRight; intro x; try rcases x with ⟨_,_⟩)
    rfl
end slhdsa.X86.XmssKeys
