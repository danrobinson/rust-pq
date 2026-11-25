import Parallel.SignJoinRows
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelSignJoin
open ParallelSigning ParallelFused
/-- The values read from the three cells after a successful join. The completed
FORS vector, each authentication node, and each individual WOTS output have
independent contracts. The caller supplies no resulting signature bytes. -/
structure Ready {N : Usize} (p : Spec.Params) (md sk pk : Spec.Bytes) (a : Spec.Adrs)
    (tree leaf : Nat) (forest : alloc.vec.Vec U8) (auth : alloc.vec.Vec (Array U8 N))
    (wots : alloc.vec.Vec (Option (alloc.vec.Vec U8))) : Prop where
  forestRows : bytes forest.val = (ParallelCached.forsRows p md sk pk a).flatten
  authSize : p.d*p.hp ≤ auth.length
  wotsSize : p.d ≤ wots.length
  authRow (j : Nat) (jl : j < p.d) (h : Nat) (hl : h < p.hp) :
    let pos := loc p.hp tree leaf j
    bytes (authRows auth p.hp j h) = Spec.xmssNode p sk ((pos.2 / 2^h) ^^^ 1) h pk (addr j pos.1)
  wotsRow (j : Nat) (jl : j < p.d) : ∃ row, wots.val[j]! = some row ∧
    let pos := loc p.hp tree leaf j
    let first := Spec.forsPkFromSig p (bytes forest.val) md pk a
    bytes row.val = Spec.wotsSign p (message p first sk pk tree leaf j) sk pk
      {(addr j pos.1).setTypeAndClear Spec.WOTS_HASH with keypair := pos.2}

def Joined (N : Usize) (p : Spec.Params) (md sk pk : Spec.Bytes) (a : Spec.Adrs) (tree leaf : Nat)
    (cells : Cells N) : Prop :=
  ∃ forest auth, cells.1=some forest ∧ cells.2.1=some auth ∧ Ready p md sk pk a tree leaf forest auth cells.2.2

theorem layers_fips {N : Usize} {p : Spec.Params} {md sk pk : Spec.Bytes} {a : Spec.Adrs}
    {tree leaf : Nat} {forest : alloc.vec.Vec U8} {auth : alloc.vec.Vec (Array U8 N)}
    {wots : alloc.vec.Vec (Option (alloc.vec.Vec U8))} (valid : p.Valid) (bounded : leaf < 2^p.hp)
    (good : Ready p md sk pk a tree leaf forest auth wots) :
    bytes (through (layers auth wots p.hp) p.d) =
      Spec.htSign p (Spec.forsPkFromSig p (bytes forest.val) md pk a) sk pk tree leaf := by
  rw [← ParallelFused.hypertree _ valid _ _ _ _ _ bounded]
  simp only [bytes,through,List.map_flatMap]
  apply List.flatMap_congr
  intro j hj
  have jl := List.mem_range.mp hj
  obtain ⟨row,present,value⟩ := good.wotsRow j jl
  simp only [layers,List.map_append,wotsRows,present,Option.map_some,Option.getD_some,
    ParallelFused.layer,Spec.xmssSign,through,List.map_flatMap]
  rw [show row.val.map (·.bv)=_ from value]
  congr 1
  apply List.flatMap_congr
  intro h hh
  exact good.authRow j jl h (List.mem_range.mp hh)

end slhdsa.ParallelSignJoin
