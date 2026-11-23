module
public import Rcavx.Types
public import Chainavx2.Chunks
@[expose] public section
open Aeneas Aeneas.Std Result
namespace RcAvxRust
open core.core_arch.x86
abbrev Lane := __m128i
abbrev Wide := __m256i

def zip (f : BitVec 64 → BitVec 64 → BitVec 64) (a b : Lane) : Lane :=
  (f a.1 b.1,f a.2 b.2)
def map (f : BitVec 64 → BitVec 64) (a : Lane) : Lane := (f a.1,f a.2)
def align (imm : I32) (a b : Lane) : Lane :=
  let input := (a.2 ++ a.1) ++ (b.2 ++ b.1)
  let offset := 8*(imm.bv.toNat%256)
  (input.extractLsb' offset 64,input.extractLsb' (offset+64) 64)
def core.core_arch.x86.sse2._mm_add_epi64 (a b : Lane) : Result Lane := ok (zip (· + ·) a b)
def core.core_arch.x86.sse2._mm_xor_si128 (a b : Lane) : Result Lane := ok (zip (· ^^^ ·) a b)
def core.core_arch.x86.sse2._mm_slli_epi64 (i : I32) (a : Lane) : Result Lane := ok (map (· <<< (i.bv.toNat%256)) a)
def core.core_arch.x86.sse2._mm_srli_epi64 (i : I32) (a : Lane) : Result Lane := ok (map (· >>> (i.bv.toNat%256)) a)
def core.core_arch.x86.ssse3._mm_alignr_epi8 (i : I32) (a b : Lane) : Result Lane := ok (align i a b)
def core.core_arch.x86.avx._mm256_set_m128i (hi lo : Lane) : Result Wide := ok (lo,hi)
def core.core_arch.x86.avx2._mm256_extracti128_si256 (i : I32) (a : Wide) : Result Lane :=
  ok (if i.bv.toNat%2=0 then a.1 else a.2)
def core.core_arch.x86.avx2._mm256_add_epi64 (a b : Wide) : Result Wide :=
  ok (zip (· + ·) a.1 b.1,zip (· + ·) a.2 b.2)
def core.core_arch.x86.avx2._mm256_xor_si256 (a b : Wide) : Result Wide :=
  ok (zip (· ^^^ ·) a.1 b.1,zip (· ^^^ ·) a.2 b.2)
def core.core_arch.x86.avx2._mm256_slli_epi64 (i : I32) (a : Wide) : Result Wide :=
  ok (map (· <<< (i.bv.toNat%256)) a.1,map (· <<< (i.bv.toNat%256)) a.2)
def core.core_arch.x86.avx2._mm256_srli_epi64 (i : I32) (a : Wide) : Result Wide :=
  ok (map (· >>> (i.bv.toNat%256)) a.1,map (· >>> (i.bv.toNat%256)) a.2)
def core.core_arch.x86.avx2._mm256_alignr_epi8 (i : I32) (a b : Wide) : Result Wide :=
  ok (align i a.1 b.1,align i a.2 b.2)
-- The extraction instantiates size_of only for u64.
def core.mem.size_of (_ : Type) : Result Usize := ok 8#usize
def roundConstants : List (BitVec 64) := [
0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
    0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
    0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
    0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
    0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817,
]
def sha512.x86_avx2.rk (i : Usize) : Result Lane :=
  if i.val+2 ≤ roundConstants.length then ok (roundConstants[i.val]!,roundConstants[i.val+1]!) else fail .arrayOutOfBounds
def cast {n : Usize} (a : Array Lane n) (len : Usize) : Result (Array U64 len) := do
  let xs := a.val.flatMap (fun x => ([⟨x.1⟩,⟨x.2⟩] : List U64))
  if h : xs.length=len.val then ok (Array.from xs h) else fail .panic
def sha512.x86_avx2.cast_ms (a : Array Lane 8#usize) := cast a 16#usize
def sha512.x86_avx2.cast_rs (a : Array Lane 40#usize) := cast a 80#usize

def core.core_arch.x86.sse2._mm_setzero_si128 : Result Lane := ok (0,0)
def core.core_arch.x86.avx._mm256_setzero_si256 : Result Wide := ok ((0,0),(0,0))
def core.core_arch.x86.__m128i.Insts.CoreCloneClone.clone (a : Lane) : Result Lane := ok a
def core.core_arch.x86.__m256i.Insts.CoreCloneClone.clone (a : Wide) : Result Wide := ok a

-- The only raw pointer in this caller is a shared pointer into the input block.
def core.slice.Slice.as_ptr (b : Slice U8) : Result (List U8) := ok b.val
def core.ptr.const_ptr.RawPtrConstT.cast (_ : Type) (p : List U8) : Result (List U8) := ok p

def core.slice.Slice.as_rchunks {α : Type u} (n : Usize) (b : Slice α) : Result (Slice α × Slice (Array α n)) :=
  if n.val = 0 then fail .panic else
    let boundary := b.length % n.val
    let head := Slice.from (b.val.take boundary) (by have := b.property; simp <;> omega)
    let tail := Slice.from (b.val.drop boundary) (by have := b.property; simp <;> omega)
    ok (head,ChainAvx2Rust.fullChunks n tail)

def lanes {α : Type} (f : Nat → α) := Array.make 8#usize [f 0,f 1,f 2,f 3,f 4,f 5,f 6,f 7]
def unpack (data : List U8) (vector : Nat) (mask : BitVec 128) : Lane :=
  let byte (i : Nat) : BitVec 8 :=
    let selector := mask.extractLsb' (8*i) 8
    if selector.msb then 0 else data[16*vector+selector.toNat%16]!.bv
  let word (k : Nat) := byte (k+7) ++ byte (k+6) ++ byte (k+5) ++ byte (k+4) ++ byte (k+3) ++ byte (k+2) ++ byte (k+1) ++ byte k
  (word 0,word 8)
def mask128 := (0x08090A0B#32 ++ 0x0C0D0E0F#32) ++ (0x00010203#32 ++ 0x04050607#32)
def mask256half := 0x08090A0B0C0D0E0F#64 ++ 0x0001020304050607#64
def constantsAt (i : Nat) : Lane := (roundConstants[2*i]!,roundConstants[2*i+1]!)
def sha512.x86_avx2.load_data_avx (_ _ : Array Lane 8#usize) (ptr : List U8) : Result (Array Lane 8#usize × Array Lane 8#usize) :=
  if ptr.length < 128 then fail .arrayOutOfBounds else
  let input i := unpack ptr i mask128
  ok (lanes input,lanes (fun i => zip (· + ·) (input i) (constantsAt i)))
def sha512.x86_avx2.load_data_avx2 (_ : Array Wide 8#usize) (_ : Array Lane 8#usize) (old : Array Lane 40#usize)
    (blocks : Array (Array U8 128#usize) 2#usize) : Result (Array Wide 8#usize × Array Lane 8#usize × Array Lane 40#usize) :=
  let ptr := blocks.val.flatMap (·.val)
  let a i := unpack ptr i mask256half
  let b i := unpack ptr (8+i) mask256half
  let second := lanes (fun i => zip (· + ·) (b i) (constantsAt i))
  let saved := Array.from (second.val ++ old.val.drop 8) (by simp)
  ok (lanes (fun i => (a i,b i)),lanes (fun i => zip (· + ·) (a i) (constantsAt i)),saved)

end RcAvxRust
