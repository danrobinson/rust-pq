import Armwide.XmssNode
import Slhdsa.Proofs.Slh
import Cachepath.BuilderSha2
open Aeneas Aeneas.Std Result
namespace slhdsa.Armwide.XmssLeaves.Generate
open Keygen Public.Dispatcher
noncomputable section
section
variable [Cpu] [Features]

abbrev xmss.xmss_node {N : Usize} := @Node.xmss.xmss_node _ _ N

def slh.slh_keygen_internal
  {N : Std.Usize} (p : params.Params) (sk_seed : Array Std.U8 N)
  (sk_prf : Array Std.U8 N) (pk_seed : Array Std.U8 N) (sk : Slice Std.U8)
  (pk : Slice Std.U8) :
  Result ((Slice Std.U8) × (Slice Std.U8))
  := do
  let a ← address.Adrs.new
  let i ← p.d - 1#u32
  let adrs ← address.Adrs.with_layer a i
  let seed ← hash.seed_ctx pk_seed
  let pk_root ← xmss.xmss_node sk_seed 0#u32 p.hp seed adrs
  let (s, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) sk
      { start := 0#usize, «end» := N }
  let s1 ← lift (Array.to_slice sk_seed)
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  let sk1 := index_mut_back s2
  let i1 ← 2#usize * N
  let (s3, index_mut_back1) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) sk1
      { start := N, «end» := i1 }
  let s4 ← lift (Array.to_slice sk_prf)
  let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
  let sk2 := index_mut_back1 s5
  let i2 ← 3#usize * N
  let (s6, index_mut_back2) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) sk2
      { start := i1, «end» := i2 }
  let s7 ← lift (Array.to_slice pk_seed)
  let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
  let sk3 := index_mut_back2 s8
  let i3 ← 4#usize * N
  let (s9, index_mut_back3) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) sk3
      { start := i2, «end» := i3 }
  let s10 ← lift (Array.to_slice pk_root)
  let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
  let (s12, index_mut_back4) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) pk
      { start := 0#usize, «end» := N }
  let s13 ← lift (Array.to_slice pk_seed)
  let s14 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s12 s13
  let pk1 := index_mut_back4 s14
  let (s15, index_mut_back5) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) pk1
      { start := N, «end» := i1 }
  let s16 ← lift (Array.to_slice pk_root)
  let s17 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s15 s16
  let sk4 := index_mut_back3 s11
  let pk2 := index_mut_back5 s17
  ok (sk4, pk2)
end

theorem keygen_eq_scalar [Cpu] [Features] {N : Usize} (p : params.Params) (hp : PN p N)
    (skSeed skPrf pkSeed : Array U8 N) (sk pk : Slice U8) :
    slh.slh_keygen_internal p skSeed skPrf pkSeed sk pk =
      slhdsa.slh.slh_keygen_internal p skSeed skPrf pkSeed sk pk := by
  have hd := hp.valid.d_ge
  change 2≤p.d.val at hd
  obtain ⟨seed,hs,_,valid⟩ := spec_imp_exists (seed_ctx_spec hp.nok pkSeed)
  have cap : 2^p.hp.val≤512 := Nat.pow_le_pow_right (by decide) hp.valid.hp_le
  have sub := spec_imp_exists (U32.sub_spec (x:=p.d) (y:=1#u32) (by scalar_tac))
  obtain ⟨last,oklast,_⟩ := sub
  unfold slh.slh_keygen_internal slhdsa.slh.slh_keygen_internal
  simp only [address.Adrs.new,address.Adrs.with_layer,oklast,hs,bind_ok,xmss.xmss_node]
  rw [Node.node_eq_scalar p hp skSeed seed valid _ 0#u32 p.hp (by simp;omega)]

theorem keygen_fips [Cpu] [Features] {N : Usize} (p : params.Params) (hp : PN p N)
    (skSeed skPrf pkSeed : Array U8 N) (sk pk : Slice U8)
    (skLen : sk.length=4*N.val) (pkLen : pk.length=2*N.val) :
    slh.slh_keygen_internal p skSeed skPrf pkSeed sk pk ⦃ r =>
      (slhdsa.bytes r.1.val,slhdsa.bytes r.2.val) =
        Spec.slhKeygenInternal (paramsS p) (slhdsa.bytes skSeed.val) (slhdsa.bytes skPrf.val) (slhdsa.bytes pkSeed.val)
        ∧ r.1.length=4*N.val ∧ r.2.length=2*N.val ⦄ := by
  rw [keygen_eq_scalar p hp]
  exact slhdsa.slh_keygen_internal_spec p hp skSeed skPrf pkSeed sk pk skLen pkLen

end
end slhdsa.Armwide.XmssLeaves.Generate
