module
public import Aeneas
@[expose] public section
/-- Four doublewords in increasing register bit order. -/
structure slhdsa.Intel.Xmm where
  w0 : BitVec 32
  w1 : BitVec 32
  w2 : BitVec 32
  w3 : BitVec 32
  deriving Inhabited, DecidableEq

abbrev core.core_arch.x86.__m128i := slhdsa.Intel.Xmm
