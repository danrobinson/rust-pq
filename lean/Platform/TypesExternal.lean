module
public import Aeneas
@[expose] public section

/-- Sixteen 32-bit words, in Intel register lane order. -/
abbrev core.core_arch.x86.__m512i := Fin 16 → BitVec 32
