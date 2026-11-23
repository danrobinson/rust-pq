import Treehash.Funs
import X86remainder.Proof
import Slhdsa.Proofs.Xmss
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.TreeHash
set_option maxHeartbeats 2000000
def addr (a : TreeHashRust.address.Adrs) : address.Adrs := ⟨a.layer,a.tree,a.typ,a.keypair,a.word2,a.word3⟩
def seedOf {N} (s : TreeHashRust.hash.Seed N) : hash.Seed N := ⟨s.pk_seed,s.state,s.state512⟩

theorem block256 (st : Array U32 8#usize) (blk : Array U8 64#usize) :
    TreeHashRust.sha256.compress st blk.to_slice 0#usize = sha256.compress st blk.to_slice 0#usize := by
  have room : (0#usize).val+64≤blk.to_slice.length := by simp
  obtain ⟨x,hx,sx⟩ := spec_imp_exists (Stream.single256 st _ _ room)
  obtain ⟨y,hy,sy⟩ := spec_imp_exists (slhdsa.compress_spec st _ _ room)
  rw [show TreeHashRust.sha256.compress = X86RemainderRust.sha256.compress from rfl,hx,hy]
  congr 1
  apply Aeneas.Std.Array.ext
  have words := congrArg (List.map (fun v : BitVec 32 => (⟨v⟩ : U32))) (sx.trans sy.symm)
  simpa [wv,List.map_map,Function.comp_def] using words

theorem block512 (st : Array U64 8#usize) (blk : Array U8 128#usize) :
    TreeHashRust.sha512.compress st blk.to_slice 0#usize = sha512.compress st blk.to_slice 0#usize := by
  have room : (0#usize).val+128≤blk.to_slice.length := by simp
  obtain ⟨x,hx,sx⟩ := spec_imp_exists (Stream.single512 st _ _ room)
  obtain ⟨y,hy,sy⟩ := spec_imp_exists (S512.compress_spec st _ _ room)
  rw [show TreeHashRust.sha512.compress = X86RemainderRust.sha512.compress from rfl,hx,hy]
  congr 1
  apply Aeneas.Std.Array.ext
  have words := congrArg (List.map (fun v : BitVec 64 => (⟨v⟩ : U64))) (sx.trans sy.symm)
  simpa [S512.wv,List.map_map,Function.comp_def] using words

theorem hash2_eq {N} (seed : TreeHashRust.hash.Seed N) (a : TreeHashRust.address.Adrs)
    (l r : Array U8 N) : TreeHashRust.xmss.hash2 seed a l r = xmss.hash2 (seedOf seed) (addr a) l r := by
  unfold TreeHashRust.xmss.hash2 xmss.hash2 TreeHashRust.hash.thash_pair hash.thash_pair
  simp only [lift,bind_tc_eq,bind_ok,seedOf]
  simp only [block256,block512]
  rfl

theorem hash2_fips {N} (p : params.Params) (hp : PN p N) (seed : TreeHashRust.hash.Seed N)
    (hs : SeedOk (seedOf seed)) (a : TreeHashRust.address.Adrs) (l r : Array U8 N) :
    TreeHashRust.xmss.hash2 seed a l r ⦃ out => bytes out.val =
      Spec.H (paramsS p) (bytes seed.pk_seed.val) (adrsS (addr a)) (bytes l.val ++ bytes r.val) ⦄ := by
  rw [hash2_eq]
  exact hash2_spec p hp _ hs _ _ _
end slhdsa.X86.TreeHash
