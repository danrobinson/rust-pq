import Parallel.SignJoinValues
namespace slhdsa.ParallelSignJoin
structure PhysicalRows where
  n : Nat
  d : Nat
  forest : List (Nat × Nat)
  auth : List (Nat × Nat)
  wots : List (Nat × Nat)
  deriving DecidableEq
/-- Source replay after the real pool join. Each pair is (first reference row, count). -/
def observed : List PhysicalRows := [
  ⟨16,7,[(0,182)],[(0,63)],[(0,7)]⟩,
  ⟨16,22,[(0,231)],[(0,66)],[(0,22)]⟩,
  ⟨24,7,[(0,255)],[(0,63)],[(0,7)]⟩,
  ⟨24,22,[(0,297)],[(0,66)],[(0,22)]⟩,
  ⟨32,8,[(0,330)],[(0,64)],[(0,8)]⟩,
  ⟨32,17,[(0,350)],[(0,68)],[(0,17)]⟩]
end slhdsa.ParallelSignJoin
