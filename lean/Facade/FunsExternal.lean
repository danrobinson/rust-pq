module
public import Facade.Types
public import Slhdsa.Funs
@[expose] public section
open Aeneas Aeneas.Std Result

namespace slh_dsa
def core.bool.Bool.then_some {T : Type} (b : Bool) (x : T) : Result (Option T) :=
  ok (if b then some x else none)
def signature.error.Error.new : Result signature.error.Error := ok ()

/-- Functional effect of overwriting a value in the zeroize crate. -/
def zeroize.Zeroize.Blanket.zeroize {Z : Type} (z : zeroize.DefaultIsZeroes Z) (_ : Z) :
    Result Z := z.coredefaultDefaultInst.default

def Slice.Insts.ZeroizeZeroize.zeroize {Z : Type} (z : zeroize.DefaultIsZeroes Z)
    (s : Slice Z) : Result (Slice Z) := do
  let value ← z.coredefaultDefaultInst.default
  ok (Slice.from (List.replicate s.val.length value) (by simpa using s.property))

def Array.Insts.ZeroizeZeroize.zeroize {Z : Type} {N : Usize} (z : zeroize.Zeroize Z)
    (a : Std.Array Z N) : Result (Std.Array Z N) := do
  let xs ← List.mapM_with_length z.zeroize a.val
  ok (Std.Array.from xs.val (xs.property.trans a.property))

abbrev slhdsa.sets.sha2_128s.params.N := Result.ok _root_.slhdsa.sets.sha2_128s.params.N
abbrev slhdsa.sets.sha2_128s.params.PARAMS := Result.ok _root_.slhdsa.sets.sha2_128s.params.PARAMS
abbrev slhdsa.sets.sha2_128s.PKCS8_PREFIX := Result.ok _root_.slhdsa.sets.sha2_128s.PKCS8_PREFIX
abbrev slhdsa.sets.sha2_128s.SPKI_PREFIX := Result.ok _root_.slhdsa.sets.sha2_128s.SPKI_PREFIX
abbrev slhdsa.sets.sha2_128f.params.N := Result.ok _root_.slhdsa.sets.sha2_128f.params.N
abbrev slhdsa.sets.sha2_128f.params.PARAMS := Result.ok _root_.slhdsa.sets.sha2_128f.params.PARAMS
abbrev slhdsa.sets.sha2_128f.PKCS8_PREFIX := Result.ok _root_.slhdsa.sets.sha2_128f.PKCS8_PREFIX
abbrev slhdsa.sets.sha2_128f.SPKI_PREFIX := Result.ok _root_.slhdsa.sets.sha2_128f.SPKI_PREFIX
abbrev slhdsa.sets.sha2_192s.params.N := Result.ok _root_.slhdsa.sets.sha2_192s.params.N
abbrev slhdsa.sets.sha2_192s.params.PARAMS := Result.ok _root_.slhdsa.sets.sha2_192s.params.PARAMS
abbrev slhdsa.sets.sha2_192s.PKCS8_PREFIX := Result.ok _root_.slhdsa.sets.sha2_192s.PKCS8_PREFIX
abbrev slhdsa.sets.sha2_192s.SPKI_PREFIX := Result.ok _root_.slhdsa.sets.sha2_192s.SPKI_PREFIX
abbrev slhdsa.sets.sha2_192f.params.N := Result.ok _root_.slhdsa.sets.sha2_192f.params.N
abbrev slhdsa.sets.sha2_192f.params.PARAMS := Result.ok _root_.slhdsa.sets.sha2_192f.params.PARAMS
abbrev slhdsa.sets.sha2_192f.PKCS8_PREFIX := Result.ok _root_.slhdsa.sets.sha2_192f.PKCS8_PREFIX
abbrev slhdsa.sets.sha2_192f.SPKI_PREFIX := Result.ok _root_.slhdsa.sets.sha2_192f.SPKI_PREFIX
abbrev slhdsa.sets.sha2_256s.params.N := Result.ok _root_.slhdsa.sets.sha2_256s.params.N
abbrev slhdsa.sets.sha2_256s.params.PARAMS := Result.ok _root_.slhdsa.sets.sha2_256s.params.PARAMS
abbrev slhdsa.sets.sha2_256s.PKCS8_PREFIX := Result.ok _root_.slhdsa.sets.sha2_256s.PKCS8_PREFIX
abbrev slhdsa.sets.sha2_256s.SPKI_PREFIX := Result.ok _root_.slhdsa.sets.sha2_256s.SPKI_PREFIX
abbrev slhdsa.sets.sha2_256f.params.N := Result.ok _root_.slhdsa.sets.sha2_256f.params.N
abbrev slhdsa.sets.sha2_256f.params.PARAMS := Result.ok _root_.slhdsa.sets.sha2_256f.params.PARAMS
abbrev slhdsa.sets.sha2_256f.PKCS8_PREFIX := Result.ok _root_.slhdsa.sets.sha2_256f.PKCS8_PREFIX
abbrev slhdsa.sets.sha2_256f.SPKI_PREFIX := Result.ok _root_.slhdsa.sets.sha2_256f.SPKI_PREFIX
end slh_dsa
