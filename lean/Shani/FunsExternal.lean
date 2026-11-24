module
public import Shani.Types
@[expose] public section
open Aeneas Aeneas.Std Result
/- SHA-NI operand ordering follows the Intel SHA Extensions programming reference.
https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sha-extensions.html -/
namespace slhdsa.Intel
abbrev Word := BitVec 32
abbrev State := Word × Word × Word × Word × Word × Word × Word × Word
def ch (e f g : Word) := (e &&& f) ^^^ (~~~e &&& g)
def maj (a b c : Word) := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
def bsig0 (x : Word) := x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22
def bsig1 (x : Word) := x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25
def ssig0 (x : Word) := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)
def ssig1 (x : Word) := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)
abbrev Reg := core.core_arch.x86.__m128i

def get (s : Reg) (i : Nat) : Word := match i % 4 with
  | 0 => s.w0 | 1 => s.w1 | 2 => s.w2 | _ => s.w3

def decode (abef cdgh : Reg) : State :=
  (abef.w3,abef.w2,cdgh.w3,cdgh.w2,abef.w1,abef.w0,cdgh.w1,cdgh.w0)

def abef (s : State) : Reg :=
  let (a,b,_,_,e,f,_,_) := s
  ⟨f,e,b,a⟩

/-- Intel SHA256RNDS2 takes the pre-added message word and round constant. -/
def intelRound (s : State) (wk : Word) : State :=
  let (a,b,c,d,e,f,g,h) := s
  let t := ch e f g + bsig1 e + wk + h
  (t + maj a b c + bsig0 a, a,b,c,t+d,e,f,g)
end slhdsa.Intel

namespace core.core_arch.x86
open slhdsa.Intel
def sha._mm_sha256msg1_epu32 (a b : Reg) : Result Reg := ok
  ⟨a.w0 + ssig0 a.w1, a.w1 + ssig0 a.w2, a.w2 + ssig0 a.w3, a.w3 + ssig0 b.w0⟩
def sha._mm_sha256msg2_epu32 (a b : Reg) : Result Reg :=
  let w0 := a.w0 + ssig1 b.w2
  let w1 := a.w1 + ssig1 b.w3
  ok ⟨w0,w1,a.w2 + ssig1 w0,a.w3 + ssig1 w1⟩
def sha._mm_sha256rnds2_epu32 (cdgh abef0 wk : Reg) : Result Reg :=
  ok (abef (intelRound (intelRound (decode abef0 cdgh) wk.w0) wk.w1))
def sse2._mm_add_epi32 (a b : Reg) : Result Reg := ok
  ⟨a.w0+b.w0, a.w1+b.w1, a.w2+b.w2, a.w3+b.w3⟩
def sse2._mm_set_epi32 (d c b a : I32) : Result Reg := ok ⟨a.bv,b.bv,c.bv,d.bv⟩
def sse2._mm_shuffle_epi32 (imm : I32) (a : Reg) : Result Reg :=
  let n := imm.bv.toNat
  ok ⟨get a n, get a (n/4), get a (n/16), get a (n/64)⟩
def sse41._mm_extract_epi32 (imm : I32) (a : Reg) : Result I32 := ok ⟨get a imm.bv.toNat⟩
def ssse3._mm_alignr_epi8 (imm : I32) (hi lo : Reg) : Result Reg :=
  let n := imm.bv.toNat % 256
  let word i := if i < 4 then get lo i else if i < 8 then get hi (i-4) else 0
  let shifted i := let r := 8*(n%4)
                   (word (i+n/4) >>> r) ||| (word (i+n/4+1) <<< (32-r))
  ok ⟨shifted 0, shifted 1, shifted 2, shifted 3⟩
end core.core_arch.x86
