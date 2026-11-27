import Armplatform.WideForsCompress

namespace slhdsa.WideFors
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

/-- The full group computes both pairs of result registers. Tails at width
16 consume the same first four result words. Wide rows use paired SHA-512 up
to its returned prefix, followed by the scalar authentication-path routine. -/
def parentAt (p : Spec.Params) (paired : Bool) (t h : Nat) (pk : Spec.Bytes)
    (a : Spec.Adrs) (pos : Nat) (node sibling : Spec.Bytes) :=
  let (left,right) := if pos%2=0 then (node,sibling) else (sibling,node)
  let adr := {a with word2 := h+1}
  if p.n=16 then
    ArmXmss.smallHash (decide (t < p.k/4*4)) (seedState 16 pk) adr (pos/2) left right
  else if paired && decide (t < p.k/2*2) then parent512 p pk {adr with word3:=pos/2} left right
  else Spec.H p pk {adr with word3:=pos/2} (left++right)

private theorem parentAt_eq (p : Spec.Params) [Fact (p.family = .sha2)] (valid : p.Valid)
    (paired : Bool) (t h : Nat) (hh : h<p.a) (pk : Spec.Bytes) (hp : pk.length=p.n)
    (a : Spec.Adrs) (pos : Nat) (node sib : Spec.Bytes) (hn : node.length=p.n) (hs : sib.length=p.n) :
    parentAt p paired t h pk a pos node sib =
      Spec.H p pk {a with word2:=h+1,word3:=pos/2} (pairMsg node sib pos) := by
  have merge (x y : Spec.Bytes) (hx : x.length=p.n) (hy : y.length=p.n) :
      (if p.n=16 then ArmXmss.smallHash (decide (t < p.k/4*4)) (seedState 16 pk) {a with word2:=h+1} (pos/2) x y
       else if paired && decide (t<p.k/2*2) then parent512 p pk {a with word2:=h+1,word3:=pos/2} x y
       else Spec.H p pk {a with word2:=h+1,word3:=pos/2} (x++y)) =
      Spec.H p pk {a with word2:=h+1,word3:=pos/2} (x++y) := by
    by_cases pn : p.n=16
    · rw [if_pos pn]
      exact ArmXmss.smallHash_fips p pn pk (by omega) {a with word2:=h+1}
        (by have := valid.a_le; change h+1<65536; omega) (pos/2) x y (by omega) (by omega) _
    · rw [if_neg pn]
      split
      · apply parent512_eq _ _ _ _ _ _ hp hx hy
        rcases valid.n_cases with eq|eq <;> tauto
      · rfl
  by_cases eq : pos%2=0
  · simpa only [parentAt,pairMsg,if_pos eq] using merge node sib hn hs
  · simpa only [parentAt,pairMsg,if_neg eq] using merge sib node hs hn

def physicalRows (p : Spec.Params) (paired : Bool) (sig pk : Spec.Bytes) (a : Spec.Adrs)
    (dig : List Nat) : Nat → Nat → Spec.Bytes × Nat
  | 0,t =>
    let i := t*2^p.a + dig[t]!
    (leaf256 p.n pk a i (Spec.block p sig (t*(p.a+1))), i)
  | h+1,t =>
    let (node,pos) := physicalRows p paired sig pk a dig h t
    let sibling := Spec.block p sig (t*(p.a+1)+1+h)
    (parentAt p paired t h pk a pos node sibling, pos/2)

private theorem block_size (p : Spec.Params) (sig : Spec.Bytes)
    (hs : sig.length=p.k*(1+p.a)*p.n) (i : Nat) (hi : i < p.k*(1+p.a)) :
    (Spec.block p sig i).length=p.n := by
  have bound := Nat.mul_le_mul_right p.n (show i+1 ≤ p.k*(1+p.a) by omega)
  simp only [Spec.block,List.length_take,List.length_drop,hs]
  rw [Nat.add_mul,Nat.one_mul] at bound; omega

theorem physical_rows (p : Spec.Params) [Fact (p.family=.sha2)] (valid : p.Valid) (paired : Bool)
    (sig pk : Spec.Bytes) (hs : sig.length=p.k*(1+p.a)*p.n) (hp : pk.length=p.n)
    (a : Spec.Adrs) (dig : List Nat) (h t : Nat) (hh : h≤p.a) (ht : t<p.k) :
    physicalRows p paired sig pk a dig h t = rows p sig pk a dig h t ∧
      (rows p sig pk a dig h t).1.length=p.n := by
  have bound := Nat.mul_le_mul_right (p.a+1) (show t+1 ≤ p.k by omega)
  rw [Nat.add_mul,Nat.one_mul] at bound
  induction h with
  | zero =>
    simp only [physicalRows,rows]
    rw [leaf_eq p valid pk hp _ _ _ (block_size p sig hs _ (by rw [Nat.add_comm 1 p.a]; omega))]
    exact ⟨rfl,Spec.F_length p valid ..⟩
  | succ h ih =>
    obtain ⟨same,size⟩ := ih (by omega)
    simp only [physicalRows,rows,same]
    rw [parentAt_eq p valid _ _ _ (by omega) _ hp _ _ _ _ size (block_size p sig hs _ (by rw [Nat.add_comm 1 p.a]; omega))]
    exact ⟨rfl,Spec.H_length p valid ..⟩

/-- Recovered bytes, including the choice of final single-stream or scalar
SHA-512 compression after the contiguous root serialization. -/
def hardwareRecover (p : Spec.Params) (paired multi : Bool) (sig md pk : Spec.Bytes) (a : Spec.Adrs) :=
  let digits := Spec.base2b md p.a p.k
  let roots := (List.range p.k).flatMap (fun t => (physicalRows p paired sig pk a digits p.a t).1)
  final p pk {a.setTypeAndClear Spec.FORS_ROOTS with keypair:=a.keypair} roots multi

theorem hardware_recover_fips (p : Spec.Params) [Fact (p.family=.sha2)] (valid : p.Valid)
    (paired multi : Bool) (sig md pk : Spec.Bytes) (hs : sig.length=p.k*(1+p.a)*p.n)
    (hp : pk.length=p.n) (a : Spec.Adrs) :
    hardwareRecover p paired multi sig md pk a = Spec.forsPkFromSig p sig md pk a := by
  rw [← recover_fips]
  unfold hardwareRecover recover
  rw [final_eq p valid _ hp]
  apply congrArg (Spec.T p pk _)
  apply List.flatMap_congr
  intro t ht
  rw [(physical_rows p valid paired sig pk hs hp a _ p.a t (by omega) (List.mem_range.mp ht)).1]

end slhdsa.WideFors
