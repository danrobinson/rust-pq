import X86key.Funs
import Wotsapi.Fallback
import Xmssroot.Top
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Key
open X86KeyRust (wideSeed wideAddr)
open Wots.Wide
def addr (a : X86KeyRust.address.Adrs) := coreAddress (wideAddr a)
def seedOf {N} (s : X86KeyRust.hash.Seed N) := coreSeed (wideSeed s)
def paramsOf (p : X86KeyRust.params.Params) : params.Params := ⟨p.n,p.h,p.d,p.hp,p.a,p.k,p.m⟩

theorem sk_eq {N} (sk : Array U8 N) (seed : X86KeyRust.hash.Seed N) (a : X86KeyRust.address.Adrs) :
    X86KeyRust.wots.sk_blocks sk seed a = wots.sk_blocks sk (seedOf seed) (addr a) := by
  have loopEq (b : X86KeyRust.address.Adrs) (len : Usize) :
      X86KeyRust.wots.sk_blocks_loop0 sk len b = wots.sk_blocks_loop0 sk len (addr b) := by
    funext arr i
    unfold X86KeyRust.wots.sk_blocks_loop0 wots.sk_blocks_loop0
    congr 1
    funext ⟨blocks,k⟩
    unfold X86KeyRust.wots.sk_blocks_loop0.body wots.sk_blocks_loop0.body
    simp only [X86KeyRust.address.Adrs.with_word2,address.Adrs.with_word2,lift,bind_tc_eq,bind_ok]
    split <;> rfl
  unfold X86KeyRust.wots.sk_blocks wots.sk_blocks
  simp only [X86KeyRust.address.Adrs.with_type,X86KeyRust.address.Adrs.with_keypair,address.Adrs.with_type,
    address.Adrs.with_keypair,bind_ok,loopEq,X86KeyRust.sha256.x86.chain_blocks,Wots.Api.chain_eq]
  with_unfolding_all rfl

private theorem finish_eq {N} (width : NOk N) (seed : X86KeyRust.hash.Seed N)
    (a : X86KeyRust.address.Adrs) (arr : Array (Array U8 64#usize) 67#usize)
    (len : Usize) (count : len.val=2*N.val+3) :
    (do let b ← core.array.Array.index (core.ops.index.IndexSlice
            (core.slice.index.SliceIndexRangeUsizeSlice (Array U8 64#usize))) arr ⟨0#usize,len⟩
        X86KeyRust.hash.thash_values seed a b) =
    (do let b ← core.array.Array.index (core.ops.index.IndexSlice
            (core.slice.index.SliceIndexRangeUsizeSlice (Array U8 64#usize))) arr ⟨0#usize,len⟩
        hash.thash_values (seedOf seed) (addr a) b) := by
  have hn := width.le32
  obtain ⟨b,eq,_,length⟩ := spec_imp_exists (Array.index_SliceIndexRangeUsizeSlice.step arr ⟨0#usize,len⟩
    (by scalar_tac) (by scalar_tac))
  simp only [eq,bind_tc_eq,bind_ok]
  apply thash_eq (wideSeed seed) (wideAddr a) b width
  simpa [count] using length

theorem leaf_eq {N} (width : NOk N) (sk : Array U8 N) (seed : X86KeyRust.hash.Seed N)
    (a : X86KeyRust.address.Adrs) :
    X86KeyRust.wots.wots_pk_gen sk seed a = wots.wots_pk_gen sk (seedOf seed) (addr a) := by
  unfold X86KeyRust.wots.wots_pk_gen wots.wots_pk_gen
  simp only [sk_eq,X86KeyRust.sha256.x86.chain_blocks,Wots.Api.chain_eq,X86KeyRust.address.Adrs.with_type,
    X86KeyRust.address.Adrs.with_keypair,address.Adrs.with_type,address.Adrs.with_keypair,bind_ok]
  have finish (arr : Array (Array U8 64#usize) 67#usize) (len : Usize) (hl : len.val=2*N.val+3) :=
    finish_eq width seed {a with typ:=X86KeyRust.address.WOTS_PK,word2:=0#u32,word3:=0#u32} arr len hl
  obtain ⟨twice,e1,h1⟩ := spec_imp_exists (Usize.mul_spec (x:=2#usize) (y:=N) (by have := width.le32; scalar_tac))
  obtain ⟨len,e2,h2⟩ := spec_imp_exists (Usize.add_spec (x:=twice) (y:=3#usize) (by have := width.le32; scalar_tac))
  have count : len.val=2*N.val+3 := by rw [h2,h1]; rfl
  simp only [bind_tc_eq] at finish
  simp only [e1,X86KeyRust.params.LEN2,params.LEN2,e2,bind_ok,finish _ _ count]
  with_unfolding_all rfl

end slhdsa.X86.Key
