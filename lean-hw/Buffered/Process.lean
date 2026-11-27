import Buffered.Blocks
import Buffered.Flush
import Buffered.Run
open Aeneas Aeneas.Std Result
namespace slhdsa.Buffered
open ShakeBatch NativeVerify
variable [kernel : Kernel]

/-- Arbitrary input bytes, initial scratch and reachable root addresses.
Each buffered subtree is evaluated by the extracted populate, carry and flush loops. -/
theorem process_at {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (a : address.Adrs) (idx height : U32) (lo : 3≤height.val) (hi : height.val≤9)
    (room : (idx.val+1)*2^height.val≤512) (leaves : FullLeaves p sk seed a)
    (perm : ActiveCorrect (machine kernel) kernel.active) : ProcessAt p sk seed a idx height := by
  intro tree z num first buf len cur as' ls rs domain hz batch firstEq empty beginAt
  rw [← hz] at lo hi room batch firstEq ⊢
  have initial : Grid (xmss p sk seed a) idx.val z.val (produced 0) buf len cur := by
    constructor
    · intro h bound;rw [empty h bound];simp [waiting,produced]
    · intro h bound;rw [beginAt h bound];simp [nextBase,produced,levelBase]
    · intro h bound j inside;simp [waiting,produced] at inside
  unfold runBlocks
  step with blocks p hp sk seed a tree idx.val z num first buf len cur as' ls rs lo hi room batch firstEq
    domain initial leaves perm as ⟨v,ready⟩
  obtain ⟨buf',len',cur',as'',ls',rs'⟩ := v
  exact flush p hp sk seed a tree idx.val z buf' len' cur' as'' ls' rs' lo hi room domain (batch ▸ ready) perm

end slhdsa.Buffered
