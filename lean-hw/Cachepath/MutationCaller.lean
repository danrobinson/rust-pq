import Cachepath.MutationPrimitives

open Aeneas Aeneas.Std Result
namespace CacheopsRust

/-- Aeneas translation with the external tree builders passed as parameters.
The replay checks every token of this definition against a fresh extraction. -/
def cache.TopTreeCache.lookup_or_populate_d2
  {N : Std.Usize} (sha2 shake : cache.mutation.Builder N) (self : cache.TopTreeCache N) (p : params.Params)
  (sk_seed : Array Std.U8 N) (pk_seed : Array Std.U8 N) (tree_d2 : Std.U64) :
  Result ((Option (Slice (Array Std.U8 N))) × (cache.TopTreeCache N))
  := do
  if self.layer_d2_capacity = 0#usize
  then
    let b ← alloc.vec.Vec.is_empty self.layer_d2
    if b
    then ok (none, self)
    else
      let s := alloc.vec.Vec.deref self.layer_d2
      let o ← cache.mutation.find s tree_d2
      match o with
      | none =>
        if self.layer_d2_capacity = 0#usize
        then ok (none, self)
        else
          if p.d < 2#u32
          then ok (none, self)
          else
            let (hf, nodes) ←
              match self.family with
              | cache.HashFamily.Sha2 =>
                do
                let i ← p.d - 2#u32
                let nodes1 ←
                  sha2 p.hp i tree_d2 sk_seed pk_seed
                ok (cache.HashFamily.Sha2, nodes1)
              | cache.HashFamily.Shake =>
                do
                let i ← p.d - 2#u32
                let nodes1 ←
                  shake p.hp i tree_d2 sk_seed
                    pk_seed
                ok (cache.HashFamily.Shake, nodes1)
            let i := alloc.vec.Vec.len self.layer_d2
            let v ←
              if i >= self.layer_d2_capacity
              then
                do
                let (_, v1) ←
                  cache.mutation.pop alloc.alloc.Global self.layer_d2
                ok v1
              else ok self.layer_d2
            let v1 ←
              cache.mutation.insert v 0#usize ({ tree_index := tree_d2, nodes }
                : cache.LayerD2Entry N)
            let lde ←
              alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
                (cache.LayerD2Entry N)) v1 0#usize
            let s1 := alloc.vec.Vec.deref lde.nodes
            ok (some s1, { self with family := hf, layer_d2 := v1 })
      | some pos =>
        if pos != 0#usize
        then
          let i := alloc.vec.Vec.len self.layer_d2
          let i1 ← 1#usize <<< p.hp
          if i < i1
          then
            let (entry, v) ←
              cache.mutation.remove alloc.alloc.Global self.layer_d2 pos
            let v1 ← cache.mutation.insert v 0#usize entry
            let lde ←
              alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
                (cache.LayerD2Entry N)) v1 0#usize
            let s1 := alloc.vec.Vec.deref lde.nodes
            ok (some s1, { self with layer_d2 := v1 })
          else
            let lde ←
              alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
                (cache.LayerD2Entry N)) self.layer_d2 pos
            let s1 := alloc.vec.Vec.deref lde.nodes
            ok (some s1, self)
        else
          let lde ←
            alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
              (cache.LayerD2Entry N)) self.layer_d2 pos
          let s1 := alloc.vec.Vec.deref lde.nodes
          ok (some s1, self)
  else
    let s := alloc.vec.Vec.deref self.layer_d2
    let o ← cache.mutation.find s tree_d2
    match o with
    | none =>
      if self.layer_d2_capacity = 0#usize
      then ok (none, self)
      else
        if p.d < 2#u32
        then ok (none, self)
        else
          let (hf, nodes) ←
            match self.family with
            | cache.HashFamily.Sha2 =>
              do
              let i ← p.d - 2#u32
              let nodes1 ←
                sha2 p.hp i tree_d2 sk_seed pk_seed
              ok (cache.HashFamily.Sha2, nodes1)
            | cache.HashFamily.Shake =>
              do
              let i ← p.d - 2#u32
              let nodes1 ←
                shake p.hp i tree_d2 sk_seed pk_seed
              ok (cache.HashFamily.Shake, nodes1)
          let i := alloc.vec.Vec.len self.layer_d2
          let v ←
            if i >= self.layer_d2_capacity
            then
              do
              let (_, v1) ←
                cache.mutation.pop alloc.alloc.Global self.layer_d2
              ok v1
            else ok self.layer_d2
          let v1 ←
            cache.mutation.insert v 0#usize ({ tree_index := tree_d2, nodes } :
              cache.LayerD2Entry N)
          let lde ←
            alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
              (cache.LayerD2Entry N)) v1 0#usize
          let s1 := alloc.vec.Vec.deref lde.nodes
          ok (some s1, { self with family := hf, layer_d2 := v1 })
    | some pos =>
      if pos != 0#usize
      then
        let i := alloc.vec.Vec.len self.layer_d2
        let i1 ← 1#usize <<< p.hp
        if i < i1
        then
          let (entry, v) ←
            cache.mutation.remove alloc.alloc.Global self.layer_d2 pos
          let v1 ← cache.mutation.insert v 0#usize entry
          let lde ←
            alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
              (cache.LayerD2Entry N)) v1 0#usize
          let s1 := alloc.vec.Vec.deref lde.nodes
          ok (some s1, { self with layer_d2 := v1 })
        else
          let lde ←
            alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
              (cache.LayerD2Entry N)) self.layer_d2 pos
          let s1 := alloc.vec.Vec.deref lde.nodes
          ok (some s1, self)
      else
        let lde ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
            (cache.LayerD2Entry N)) self.layer_d2 pos
        let s1 := alloc.vec.Vec.deref lde.nodes
        ok (some s1, self)

end CacheopsRust
