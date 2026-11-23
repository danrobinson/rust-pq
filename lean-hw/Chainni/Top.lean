import Chainni.Initial
open Aeneas Aeneas.Std Result
namespace slhdsa.Intel.Chain

def run (N : Usize) (state : Array U32 8#usize) (blocks : Rows) (start «end» : Slice U32)
    (iv : Array Reg 2#usize) := do
  let i16 := Slice.len blocks
  let pairs ← i16 / 2#usize
  let blocks1 ←
    ChainNiRust.sha256.x86.chains_loop0 N { start := 0#usize, «end» := pairs } state
      blocks start «end» iv
  let offset ← 2#usize * pairs
  let i17 := Slice.len blocks1
  if offset < i17
  then
    let (s, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeFromUsizeSlice (Array Std.U8
        64#usize)) blocks1 { start := offset }
    let s1 ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U32) start
        { start := offset }
    let s2 ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U32) «end»
        { start := offset }
    let s3 ← ChainNiRust.hash.chain_blocks_portable N state s s1 s2
    ok (index_mut_back s3)
  else ok blocks1

theorem chains_spec (N : Usize) (state : Array U32 8#usize) (blocks : Rows) (start «end» : Slice U32)
    (hn : N.val ≤ 32) (hs : blocks.length ≤ start.length) (he : blocks.length ≤ «end».length) :
    ChainNiRust.sha256.x86.chains N state blocks start «end» ⦃ out => Ended N state blocks out start «end» ⦄ := by
  unfold ChainNiRust.sha256.x86.chains
  conv => lhs; equals (pack state >>= run N state blocks start «end») =>
    unfold pack run
    simp only [bind_tc_eq,Std.bind_assoc,bind_ok]
    rfl
  apply WP.spec_bind (pack_spec state)
  intro iv hinit
  unfold run
  step as ⟨pairs,hp⟩
  have pairs_ok : pairs.val = blocks.length/2 := hp
  step with groups_spec N state iv blocks start «end» pairs hn hinit (by omega) hs he as ⟨buf,processed⟩
  have len := processed.1
  step as ⟨off,hoff⟩
  split
  · step as ⟨dest,hbuf,hsize,hback⟩
    obtain ⟨tail,back⟩ := dest
    simp only at hbuf hsize hback
    step as ⟨ss,hss,ls⟩
    step as ⟨es,hes,le⟩
    step with chain_blocks_portable_spec N hn state tail ss es (by omega) (by omega) as ⟨r,hr,done⟩
    have h : InPlace.Processed (expected N state blocks start «end») blocks (back r) blocks.length := by
      rw [show blocks.length = 2*pairs.val+r.length by omega]
      apply InPlace.advance _ _ _ _ _ _ processed (by omega)
      · simp only [hback,Slice.setSlice!_val,hoff]
      · intro k hk
        have actual := done k (by omega)
        have old := processed.2 (off.val+k) (by omega)
        rw [if_neg (by omega)] at old
        simp only [hbuf,hss,hes,List.getElem!_drop] at actual
        rw [old] at actual
        simpa only [expected,hoff] using actual
    exact ⟨h.1,fun i hi => by simpa only [if_pos hi,expected] using h.2 i hi⟩
  · rename_i full
    have all : 2*pairs.val = blocks.length := by
      change ¬ off.val < buf.length at full
      omega
    apply (WP.spec_ok _).2
    refine ⟨len,fun i hi => ?_⟩
    simpa only [all,if_pos hi,expected] using processed.2 i hi

end slhdsa.Intel.Chain
