import Chainx86.Funs
import Chainavx2.Top
import Chainwide.Top
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Dispatch
open ChainX86Rust.sha256.x86

theorem chains_spec (N : Usize) (state : Array U32 8#usize) (blocks : Intel.Chain.Rows) (starts ends : Slice U32)
    (hn : N.val ≤ 32) (hs : blocks.length ≤ starts.length) (he : blocks.length ≤ ends.length) :
    chain_blocks N state blocks starts ends ⦃ r => Intel.Chain.Ended N state blocks r starts ends ⦄ := by
  have narrow := Avx2.Chain.chains_spec N state blocks starts ends hn hs he
  have pair := Intel.Chain.chains_spec N state blocks starts ends hn hs he
  have portable := chain_blocks_portable_spec N hn state blocks starts ends hs he
  unfold chain_blocks
  simp only [if_neg (show ¬ N > 32#usize by scalar_tac),
    if_neg (show ¬ starts.len < blocks.len by scalar_tac),if_neg (show ¬ ends.len < blocks.len by scalar_tac)]
  split
  all_goals simp only [bind_ok,Bool.false_eq_true,ite_true,ite_false,has_avx512.get,sha_ni.get,
    ChainWideRust.sha256.x86.sha_ni.get,has_avx2.get]
  all_goals split_ifs <;> first
    | exact narrow
    | exact pair
    | exact portable
    | apply Chain.chains_spec N state blocks starts ends (by omega) hs he

/-- The original portable operation is selected even on malformed dimension inputs. -/
theorem fallback_eq (N : Usize) (state : Array U32 8#usize) (blocks : Intel.Chain.Rows) (starts ends : Slice U32)
    (bad : N.val > 32 ∨ starts.length < blocks.length ∨ ends.length < blocks.length) :
    chain_blocks N state blocks starts ends = hash.chain_blocks_portable N state blocks starts ends := by
  by_cases width : N > 32#usize
  · simp only [chain_blocks,if_pos width]
  by_cases start : starts.len < blocks.len
  · simp only [chain_blocks,if_neg width,if_pos start]
  have stop : ends.len < blocks.len := by rcases bad with h|h|h <;> scalar_tac
  simp only [chain_blocks,if_neg width,if_neg start,if_pos stop]
end slhdsa.X86.Dispatch
