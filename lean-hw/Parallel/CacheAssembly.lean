import Parallel.CacheCompletion
import Parallel.Signing
import Cachepath.EndToEnd

open Spec slhdsa slhdsa.cache.endtoend
namespace ParallelCached
/-- The joined values of jobs that compute their specified output. This works for
grouped jobs and is independent of the unstable sort's ordering of equal weights. -/
theorem joined_value {V : Type} (jobs : List (List Nat)) (total : Nat) (want : Nat → V)
    (owns : jobs.flatten.Perm (List.range total)) {cells}
    (run : Run jobs.length (planWrites jobs (fun _ => want)) jobs.length [] cells) (index : Nat) (inside : index<total) :
    cells index=some (want index) := by
  apply (joined run index (want index)).mpr
  have present := owns.mem_iff.mpr (List.mem_range.mpr inside)
  obtain ⟨row,mem,slot⟩ := List.mem_flatten.mp present
  obtain ⟨j,valid,rowEq⟩ := List.mem_iff_getElem.mp mem
  refine ⟨j,valid,?_⟩
  simp only [planWrites,List.getElem?_eq_getElem valid,Option.getD_some,rowEq]
  exact List.mem_map_of_mem (f:=fun i => (i,want i)) slot

private abbrev State := Bytes × Bytes × Nat × Nat

def activeLayers (p : Params) (hit : Option (List Bytes)) := p.d - (if hit.isSome ∧ 2≤p.d then 2 else 1)

def xmssValue (p : Params) (sk pk : Bytes) (tree leaf slot : Nat) : Bytes :=
  let layer := slot/p.hp
  let h := slot%p.hp
  let (t,l) := ParallelSigning.loc p.hp tree leaf layer
  xmssNode p sk ((l/2^h) ^^^ 1) h pk (layerAdrs layer t)

def forsRows (p : Params) (md sk pk : Bytes) (a : Adrs) : List Bytes :=
  (List.range p.k).flatMap fun t =>
    let digit := (base2b md p.a p.k)[t]!
    forsSkGen p sk pk a (t*2^p.a+digit) :: (List.range p.a).map (forsAuth p sk pk a t digit)

theorem fors_length (p : Params) (md sk pk : Bytes) (a : Adrs) :
    (forsRows p md sk pk a).length=p.k*(1+p.a) := by
  unfold forsRows
  simp [List.length_flatMap,Nat.add_comm]

theorem fors_bytes (p : Params) (md sk pk : Bytes) (a : Adrs) :
    (forsRows p md sk pk a).flatten = forsSign p md sk pk a := by
  rw [slhdsa.forsSign_eq]
  unfold forsRows
  rw [List.flatten_eq_flatMap,List.flatMap_assoc]
  apply List.flatMap_congr
  intro t _
  simp only [List.flatMap_cons,List.flatMap_map,id_eq,forsSignTree]

def assembleLayer (p : Params) (sk pk : Bytes) (top : List Bytes) (hit : Option (List Bytes))
    (cells : Nat → Option Bytes) (st : State) (j : Nat) : State :=
  let (sig,root,t,l) := st
  let a := layerAdrs j t
  let wots := wotsSign p root sk pk {a.setTypeAndClear WOTS_HASH with keypair:=l}
  let uncached := (List.range p.hp).flatMap fun h => (cells (j*p.hp+h)).getD []
  let usePath := fun auth =>
    let part := wots++auth
    (sig++part,xmssPkFromSig p l part root pk a,t >>> p.hp,t%2^p.hp)
  if j=p.d-1 then
    (sig++(wots++cachedAuthPath p top l),root,t >>> p.hp,t%2^p.hp)
  else if j+2=p.d then match hit with
    | some tree => (sig++(wots++cachedAuthPath p tree l),tree[tree.length-1]!,t >>> p.hp,t%2^p.hp)
    | none => usePath uncached
  else usePath uncached

private theorem step_eq (p : Params) (valid : p.Valid) (sk pk : Bytes) (t l : Nat)
    (top : List Bytes) (hit : Option (List Bytes)) (cells : Nat → Option Bytes)
    (reads : ∀ i<activeLayers p hit*p.hp, cells i=some (xmssValue p sk pk t l i))
    (st : State) (j : Nat) (layer : j<p.d) (pos : st.2.2=ParallelSigning.loc p.hp t l j) :
    assembleLayer p sk pk top hit cells st j = cachedHtLayer p sk pk top hit st j := by
  obtain ⟨sig,root,tree,leaf⟩ := st
  simp only at pos
  have auth (live : j<activeLayers p hit) : (List.range p.hp).flatMap (fun h => (cells (j*p.hp+h)).getD []) =
      (List.range p.hp).flatMap (fun h => xmssNode p sk ((leaf/2^h) ^^^ 1) h pk (layerAdrs j tree)) := by
    apply List.flatMap_congr
    intro h hh
    have hlt := List.mem_range.mp hh
    have block := Nat.mul_le_mul_right p.hp (show j+1≤activeLayers p hit by omega)
    rw [Nat.add_mul,one_mul] at block
    rw [reads _ (by omega)]
    have div : (j*p.hp+h)/p.hp=j := by rw [Nat.mul_comm j p.hp,Nat.mul_add_div valid.hp_pos,Nat.div_eq_of_lt hlt,Nat.add_zero]
    have md : (j*p.hp+h)%p.hp=h := by simp [Nat.add_mod,Nat.mod_eq_of_lt hlt]
    simp only [Option.getD_some,xmssValue,div,md,← pos]
  unfold assembleLayer cachedHtLayer
  by_cases last : j=p.d-1
  · simp [last,layerAdrs]
  · simp only [ite_eq_right last]
    by_cases pen : j+2=p.d
    · cases pick : hit with
      | some tree => simp [pen,layerAdrs]
      | none =>
        rw [ite_eq_left pen,ite_eq_left pen]
        have bound : j<activeLayers p hit := by simp [activeLayers,pick];omega
        simp only [pick] at auth ⊢
        rw [auth (pick ▸ bound)]
        rfl
    · simp only [ite_eq_right pen]
      have bound : j<activeLayers p hit := by unfold activeLayers;split_ifs <;> omega
      rw [auth bound]
      rfl


private theorem advance_pos (p : Params) (sk pk : Bytes) (top : List Bytes) (hit : Option (List Bytes))
    (st : State) (j : Nat) :
    (cachedHtLayer p sk pk top hit st j).2.2 = (st.2.2.1 >>> p.hp,st.2.2.1%2^p.hp) := by
  obtain ⟨sig,root,tree,leaf⟩ := st
  unfold cachedHtLayer
  split_ifs <;> first | rfl | (cases hit <;> rfl)

def desired (p : Params) (md sk pk : Bytes) (a : Adrs) (tree leaf : Nat) (hit : Option (List Bytes))
    (slot : Nat) : Bytes :=
  let xmss := activeLayers p hit*p.hp
  if slot<xmss then xmssValue p sk pk tree leaf slot else (forsRows p md sk pk a)[slot-xmss]!

def assemble (p : Params) (r md sk pk : Bytes) (a : Adrs) (tree leaf : Nat)
    (top : List Bytes) (hit : Option (List Bytes)) (cells : Nat → Option Bytes) : Bytes :=
  let offset := activeLayers p hit*p.hp
  let fors := (List.range (p.k*(1+p.a))).flatMap (fun i => (cells (offset+i)).getD [])
  let root := forsPkFromSig p fors md pk a
  r++fors++((List.range p.d).foldl (assembleLayer p sk pk top hit cells) ([],root,tree,leaf)).1

theorem assemble_fips (p : Params) (valid : p.Valid) (r md sk pk : Bytes) (a : Adrs) (tree leaf : Nat)
    (top : List Bytes) (hit : Option (List Bytes)) (treeBound : tree<2^(p.h-p.hp)) (leafBound : leaf<2^p.hp)
    (topValid : SpecTreeOk p sk pk (layerAdrs (p.d-1) 0) top)
    (hitValid : ∀ d2, hit=some d2 → SpecTreeOk p sk pk (layerAdrs (p.d-2) (tree >>> ((p.d-2)*p.hp))) d2)
    (jobs : List (List Nat)) (geometry : jobs.flatten.Perm (List.range (activeLayers p hit*p.hp+p.k*(1+p.a))))
    {cells} (run : Run jobs.length (planWrites jobs (fun _ => desired p md sk pk a tree leaf hit)) jobs.length [] cells) :
    assemble p r md sk pk a tree leaf top hit cells = r++forsSign p md sk pk a++
      htSign p (forsPkFromSig p (forsSign p md sk pk a) md pk a) sk pk tree leaf := by
  let base := activeLayers p hit*p.hp
  have cellsOk := joined_value jobs _ (desired p md sk pk a tree leaf hit) geometry run
  have reads (i : Nat) (lt : i<base) : cells i=some (xmssValue p sk pk tree leaf i) := by
    rw [cellsOk i (by dsimp [base] at lt;omega)]
    dsimp only [base] at lt
    simp [desired,lt]
  let rows := forsRows p md sk pk a
  have len : rows.length=p.k*(1+p.a) := fors_length ..
  have collected : (List.range (p.k*(1+p.a))).flatMap (fun i => (cells (base+i)).getD []) = rows.flatten := by
    rw [List.flatMap_def]
    apply congrArg List.flatten
    apply List.ext_getElem
    · simp [len]
    · intro i hi hj
      have ok : i<p.k*(1+p.a) := by rw [← len];exact hj
      simp only [List.getElem_map,List.getElem_range]
      rw [cellsOk _ (by simp only [base];omega)]
      change (if base+i<base then _ else rows[base+i-base]!)=rows[i]
      rw [ite_eq_right (by omega),Nat.add_sub_cancel_left,getElem!_pos rows i hj]
  change _ = r++forsSign p md sk pk a++_
  unfold assemble
  change r++_++_=_
  rw [show (List.range (p.k*(1+p.a))).flatMap (fun i => (cells (activeLayers p hit*p.hp+i)).getD []) = forsSign p md sk pk a
    from collected.trans (fors_bytes ..)]
  let root := forsPkFromSig p (forsSign p md sk pk a) md pk a
  let cached := cachedHtLayer p sk pk top hit
  let packed := assembleLayer p sk pk top hit cells
  let initial : State := ([],root,tree,leaf)
  have inv (c : Nat) (hc : c≤p.d) :
      (List.range c).foldl packed initial=(List.range c).foldl cached initial ∧
      ((List.range c).foldl cached initial).2.2=ParallelSigning.loc p.hp tree leaf c := by
    induction c with
    | zero => exact ⟨rfl,rfl⟩
    | succ c ih =>
      obtain ⟨equal,pos⟩ := ih (by omega)
      simp only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,equal]
      refine ⟨step_eq p valid sk pk tree leaf top hit cells reads _ c (by omega) pos,?_⟩
      rw [show cached = cachedHtLayer p sk pk top hit by rfl,advance_pos]
      simp [ParallelSigning.loc,← pos,cached]
  have final := congrArg Prod.fst (inv p.d (Nat.le_refl _)).1
  change r++_++((List.range p.d).foldl packed initial).1 = _
  rw [final,← cached_htSign_eq_fips p valid root sk pk tree leaf treeBound leafBound top hit topValid hitValid]
  rfl

end ParallelCached

namespace ParallelCached

/-- Worker inputs from the FIPS internal signer, for both pure and pre-hash framing. -/
structure SignInputs where
  randomizer : Bytes
  md : Bytes
  tree : Nat
  leaf : Nat
  address : Adrs

def signInputs (p : Params) (msg sk addrnd : Bytes) : SignInputs :=
  let r := PRFmsg p (block p sk 1) addrnd msg
  let digest := Hmsg p r (block p sk 2) (block p sk 3) msg
  let tree := digestTree p digest
  let leaf := digestLeaf p digest
  ⟨r,digest.take p.mdBytes,tree,leaf,
    { { Adrs.zero with tree := tree }.setTypeAndClear FORS_TREE with keypair := leaf }⟩

/-- From any reachable partial schedule, workers can finish. Every such completion
gives the same FIPS signature, including the message-dependent randomizer. -/
theorem complete_signature (p : Params) (valid : p.Valid) (msg sk addrnd : Bytes)
    (top : List Bytes) (hit : Option (List Bytes)) (jobs : List (List Nat))
    (geometry : jobs.flatten.Perm (List.range (activeLayers p hit*p.hp+p.k*(1+p.a))))
    (topValid : SpecTreeOk p (block p sk 0) (block p sk 2) (layerAdrs (p.d-1) 0) top)
    (hitValid : ∀ d2, hit=some d2 → SpecTreeOk p (block p sk 0) (block p sk 2)
      (layerAdrs (p.d-2) ((signInputs p msg sk addrnd).tree >>> ((p.d-2)*p.hp))) d2) :
    let input := signInputs p msg sk addrnd
    let writes := planWrites jobs (fun _ => desired p input.md (block p sk 0) (block p sk 2)
      input.address input.tree input.leaf hit)
    ∀ {t pending cells}, Run jobs.length writes t pending cells → t≤jobs.length →
      (∃ out, Completion jobs.length writes t pending cells out) ∧
      ∀ out, Completion jobs.length writes t pending cells out →
        assemble p input.randomizer input.md (block p sk 0) (block p sk 2) input.address
          input.tree input.leaf top hit out = slhSignInternal p msg sk addrnd := by
  intro input writes t pending cells run issued
  obtain ⟨out,steps,_⟩ := plan_completion jobs _ _ geometry run issued
  refine ⟨⟨out,steps⟩,?_⟩
  intro result completion
  have height : p.h/p.d=p.hp := by
    have dpos : 0<p.d := by have := valid.d_ge; omega
    rw [valid.h_eq,Nat.mul_div_cancel_left _ dpos]
  exact assemble_fips p valid _ _ _ _ _ _ _ top hit
    (by dsimp [input,signInputs]; rw [← height]; exact digestTree_lt p _)
    (digestLeaf_lt p valid _) topValid hitValid jobs geometry (completion.joined run)

end ParallelCached
