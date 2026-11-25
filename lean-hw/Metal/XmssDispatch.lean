import Metal.ReducerBytes

namespace MetalXmssDispatch
open Spec MetalPipeline MetalChainDispatch MetalLeafDispatch
open MetalWotsOutput (Context context)

def leaves (p : Params) (words : Nat) (mem : Memory) (row i : Nat) :=
  readNode words mem (row*2^p.hp+i)

def state (p : Params) (keys : Keys) (trees : Trees) (words : Nat) (mem : Memory)
    (row height i : Nat) : Bytes :=
  let d := trees row
  metalXmssReduceState p (keys d.keyIdx).2 { Adrs.zero with layer := d.layer, tree := d.tree }
    (leaves p words mem row) height i

theorem leaf_value (p : Params) (hv : p.Valid) (mode : XmssMode) (rs : List BatchSignReq)
    (words size : Nat) (geom : p.n=words*size) (mem : Memory)
    (correct : Matches (rs.length*p.d*2^p.hp) words size mem (metalXmssLeaves mode p (MetalHostValues.keys p rs)
        (MetalHostValues.trees p rs))) (s : Fin rs.length) (j : Fin p.d) (i : Nat) (hi : i < 2^p.hp) :
    let x := context p rs[s]
    leaves p words mem (s.val*p.d+j.val) i = xmssNode p x.sk i 0 x.pk (MetalWotsOutput.adrs p x j) := by
  intro x
  let row := s.val*p.d+j.val
  let dictionary := MetalHostValues.keys p rs
  let table := MetalHostValues.trees p rs
  have rowBound := MetalCommandValues.active s.val j.val p.d rs.length s.isLt j.isLt
  have gidBound := MetalCommandValues.active row i (2^p.hp) (rs.length*p.d) rowBound hi
  have target := metalXmssLeaves_eq_fips mode p hv dictionary table row i hi
  dsimp only at target
  have len : (metalXmssLeaves mode p dictionary table (row*2^p.hp+i)).length = words*size := by
    rw [target,xmssNode_length p hv,geom]
  rw [leaves,readNode_spec _ _ _ _ _ correct _ gidBound len]
  rw [target]
  simp only [x,table,dictionary,row,MetalHostValues.trees,MetalHostValues.layer_at p rs s j,
    MetalHostValues.key_selected p rs s,MetalWotsOutput.adrs]

theorem state_value (p : Params) (hv : p.Valid) (mode : XmssMode) (rs : List BatchSignReq)
    (words size : Nat) (geom : p.n=words*size) (mem : Memory)
    (correct : Matches (rs.length*p.d*2^p.hp) words size mem (metalXmssLeaves mode p (MetalHostValues.keys p rs)
        (MetalHostValues.trees p rs))) (s : Fin rs.length) (j : Fin p.d) (h i : Nat)
    (hh : h≤p.hp) (hi : i<2^(p.hp-h)) :
    let x := context p rs[s]
    state p (MetalHostValues.keys p rs) (MetalHostValues.trees p rs) words mem (s.val*p.d+j.val) h i =
      xmssNode p x.sk i h x.pk (MetalWotsOutput.adrs p x j) := by
  intro x
  simp only [state,MetalHostValues.trees,MetalHostValues.layer_at p rs s j,MetalHostValues.key_selected p rs s]
  exact metal_xmss_reduce_level_eq_fips p x.sk x.pk (MetalWotsOutput.adrs p x j) _
    (leaf_value p hv mode rs words size geom mem correct s j) h hh i hi

def rootVal (p : Params) (keys : Keys) (trees : Trees) (words : Nat) (mem : Memory) (row : Nat) :=
  state p keys trees words mem row p.hp 0

def authVal (p : Params) (keys : Keys) (trees : Trees) (words : Nat) (mem : Memory) (row h : Nat) :=
  let d := trees row
  state p keys trees words mem row h (((d.targetLeaf.getD 0) >>> h) ^^^ 1)

theorem auth_value (p : Params) (hv : p.Valid) (mode : XmssMode) (rs : List BatchSignReq)
    (words size : Nat) (geom : p.n=words*size) (mem : Memory)
    (correct : Matches (rs.length*p.d*2^p.hp) words size mem (metalXmssLeaves mode p (MetalHostValues.keys p rs)
        (MetalHostValues.trees p rs))) (s : Fin rs.length) (j : Fin p.d) (h : Fin p.hp) :
    authVal p (MetalHostValues.keys p rs) (MetalHostValues.trees p rs) words mem (s.val*p.d+j.val) h =
      MetalReducerBytes.auth p (context p rs[s]) j h := by
  let x := context p rs[s]
  let leaf := (MetalWotsOutput.loc p x j).2
  have validLeaf : leaf < 2^p.hp := by
    unfold leaf MetalWotsOutput.loc
    cases eq : j.val with
    | zero => exact digestLeaf_lt p hv _
    | succ k => exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have sibling := (metal_xmss_reduce_auth_in_bounds p leaf h validLeaf h.isLt).1
  simp only [authVal,MetalHostValues.trees,MetalHostValues.layer_at p rs s j,Option.getD_some]
  rw [state_value p hv mode rs words size geom mem correct s j _ _ (by omega : h.val≤p.hp) sibling]
  simp only [MetalReducerBytes.auth,Nat.shiftRight_eq_div_pow,leaf,x]

theorem root_value (p : Params) (hv : p.Valid) (mode : XmssMode) (rs : List BatchSignReq)
    (words size : Nat) (geom : p.n=words*size) (mem : Memory)
    (correct : Matches (rs.length*p.d*2^p.hp) words size mem (metalXmssLeaves mode p (MetalHostValues.keys p rs)
        (MetalHostValues.trees p rs))) (s : Fin rs.length) (j : Fin p.d) :
    rootVal p (MetalHostValues.keys p rs) (MetalHostValues.trees p rs) words mem (s.val*p.d+j.val) =
      MetalWotsOutput.root p (context p rs[s]) j :=
  state_value p hv mode rs words size geom mem correct s j _ _ (by omega) (by simp)

def rootBuffer (p : Params) (count words size : Nat) (value : Nat → Bytes) (buf : Execution) (row : Nat) :=
  readNode words (run (count*p.d) words size value buf) row

theorem roots_read (p : Params) (hv : p.Valid) (mode : XmssMode) (rs : List BatchSignReq)
    (words size : Nat) (geom : p.n=words*size) (mem : Memory)
    (correct : Matches (rs.length*p.d*2^p.hp) words size mem (metalXmssLeaves mode p (MetalHostValues.keys p rs)
        (MetalHostValues.trees p rs))) (buf : Execution) (order : buf.schedule.Perm (grid (rs.length*p.d) words))
    (f : Nat → Bytes) (linked : ∀ t, f t = rootVal p (MetalHostValues.keys p rs) (MetalHostValues.trees p rs) words mem t)
    (s : Fin rs.length) (j : Fin p.d) :
    rootBuffer p rs.length words size f buf (s.val*p.d+j.val) = MetalWotsOutput.root p (context p rs[s]) j := by
  let row := s.val*p.d+j.val
  have value : f row = MetalWotsOutput.root p (context p rs[s]) j :=
    (linked row).trans (root_value p hv mode rs words size geom mem correct s j)
  have len : (f row).length = words*size := by rw [value]; exact (xmssNode_length p hv _ _ _ _ _).trans geom
  have allWords := matches_run (rs.length*p.d) words size f f buf (covers_grid order) (fun _ _ => rfl)
  exact (readNode_spec _ _ _ _ _ allWords row (MetalCommandValues.active _ _ _ _ s.isLt j.isLt) len).trans value

def values {p : Params} {rs : List BatchSignReq} {g : MetalSignatureLayout.Geometry}
    (f : Nat → Nat → Bytes) (other : MetalReducerBytes.Field g rs.length → Spec.Byte)
    (b : MetalReducerBytes.Field g rs.length) : Spec.Byte :=
  match b.val.2.1 with
  | .inr (.inr (j,.inr h)) => (f (b.val.1.val*p.d+j.val) h.val)[b.val.2.2.val]!
  | _ => other b

theorem sig_field (p : Params) (hv : p.Valid) (mode : XmssMode) (rs : List BatchSignReq)
    (words size : Nat) (geom : p.n=words*size) (mem : Memory)
    (leavesOk : Matches (rs.length*p.d*2^p.hp) words size mem (metalXmssLeaves mode p (MetalHostValues.keys p rs)
        (MetalHostValues.trees p rs)))
    (g : MetalSignatureLayout.Geometry) (nEq : g.n=p.n) (dEq : g.d=p.d) (hpEq : g.hp=p.hp)
    (cEq : g.wots=p.len) (sigEq : MetalSignatureLayout.signatureBytes g=p.sigBytes)
    (forsEq : MetalSignatureLayout.forsBytes g=p.forsSigBytes) (xmssEq : MetalSignatureLayout.xmssBytes g=p.xmssSigBytes)
    (f : Nat → Nat → Bytes) (linked : ∀ r h, f r h = authVal p (MetalHostValues.keys p rs) (MetalHostValues.trees p rs) words mem r h)
    (other : MetalReducerBytes.Field g rs.length → Spec.Byte)
    (w : MetalReducerBytes.Field g rs.length) (own : MetalCommandValues.owner g w.val.2.1 = .xmssAuth) :
    (metalBatchSignInternal mode p rs).flatten[MetalSignatureLayout.address g w.val]? =
      some (values (p:=p) (rs:=rs) f other w) := by
  rcases w with ⟨⟨s,node,b⟩,valid⟩
  rcases node with z | ⟨t, z | (l | a)⟩ | ⟨j, c | h⟩ <;> cases own
  let layer := Fin.cast dEq j; let height := Fin.cast hpEq h; let i := Fin.cast nEq b
  let off := MetalReducerBytes.xmssOffset p layer height i
  let coord : MetalSignatureLayout.Byte g rs.length := ⟨s,.inr (.inr (j,.inr h)),b⟩
  have at_ : MetalSignatureLayout.address g coord = s.val*p.sigBytes+off := by
    simp only [MetalSignatureLayout.address,coord,off,MetalReducerBytes.xmssOffset,sigEq,forsEq,xmssEq,cEq,nEq,
      layer,height,i,Fin.val_cast,Nat.add_assoc]
  have within : off < p.sigBytes := by
    have ah := MetalCommandValues.active height.val i.val p.n p.hp height.isLt i.isLt
    have iw : p.len*p.n+(height.val*p.n+i.val) < p.xmssSigBytes := by
      simp only [Params.xmssSigBytes,Nat.add_mul]; omega
    have aw := MetalCommandValues.active layer.val _ p.xmssSigBytes p.d layer.isLt iw
    have total := sigBytes_parts p hv
    unfold off MetalReducerBytes.xmssOffset; omega
  rw [metal_batch_sign_internal_eq_fips mode p hv]
  change (rs.map _).flatten[MetalSignatureLayout.address g coord]? = _
  rw [at_,MetalWotsOutput.batchByte _ _ _ (fun _ => slhSignInternal_length p hv _ _ _) s _ within,
    MetalReducerBytes.sigXmss_byte p hv rs[s] layer height i layer.isLt height.isLt i.isLt]
  change _ = some ((f (s.val*p.d+layer.val) height.val)[i.val]!)
  rw [linked,auth_value p hv mode rs words size geom mem leavesOk s layer height]
  have len : i.val < (MetalReducerBytes.auth p (context p rs[s]) layer height).length := by
    rw [MetalReducerBytes.auth,xmssNode_length p hv]; exact i.isLt
  simp only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem len,Option.getD_some]

open MetalCommand MetalCommandValues

theorem command (p : Params) (hv : p.Valid) (mode : XmssMode) (rs : List BatchSignReq)
    (words size : Nat) (geom : p.n=words*size) (mem : Memory)
    (g : MetalSignatureLayout.Geometry) (nEq : g.n=p.n) (dEq : g.d=p.d) (hpEq : g.hp=p.hp)
    (cEq : g.wots=p.len) (sigEq : MetalSignatureLayout.signatureBytes g=p.sigBytes)
    (forsEq : MetalSignatureLayout.forsBytes g=p.forsSigBytes) (xmssEq : MetalSignatureLayout.xmssBytes g=p.xmssSigBytes)
    (f : Nat → Nat → Bytes) (authLinked : ∀ r h, f r h = authVal p (MetalHostValues.keys p rs) (MetalHostValues.trees p rs) words mem r h)
    (root : Nat → Bytes) (rootLinked : ∀ r, root r = rootVal p (MetalHostValues.keys p rs) (MetalHostValues.trees p rs) words mem r)
    (buf : Execution) (order : buf.schedule.Perm (grid (rs.length*p.d) words))
    (wotsAt : MetalWotsOutput.Coord p rs.length → Nat) (wotsByte : MetalWotsOutput.Coord p rs.length → Spec.Byte)
    (wots : List (MetalWotsOutput.Coord p rs.length)) (atLinked : ∀ w, wotsAt w = MetalWotsOutput.addr w)
    (schedule : List (MetalReducerBytes.Field g rs.length))
    (authCovered : ∀ w : MetalReducerBytes.Field g rs.length, owner g w.val.2.1 = .xmssAuth → w ∈ schedule)
    (other : MetalReducerBytes.Field g rs.length → Spec.Byte) (initial : Nat → Spec.Byte) (capacity : Nat)
    (bound : rs.length*p.sigBytes ≤ capacity) (cmd : Access)
    (reads : .xmss_leaves ∈ cmd.reads) (writes : cmd.writes=[.xmss_roots,.xmssAuth]) (inv : Region → Prop)
    (leafInv : inv .xmss_leaves → Matches (rs.length*p.d*2^p.hp) words size mem
        (metalXmssLeaves mode p (MetalHostValues.keys p rs) (MetalHostValues.trees p rs)))
    (rootInv : (∀ s : Fin rs.length, ∀ j < p.d,
      rootBuffer p rs.length words size root buf (s.val*p.d+j) = MetalWotsOutput.root p (context p rs[s]) j) → inv .xmss_roots)
    (authInv : inv .xmssAuth) :
    let v := values (p:=p) (rs:=rs) f other
    let prior := MetalHostValues.afterMiddle (MetalReducerBytes.events schedule v) initial
    let pool := MetalWotsOutput.pool wotsAt wotsByte wots prior capacity
    let pred := correct g rs.length (pool.take (rs.length*p.sigBytes)) (metalBatchSignInternal mode p rs).flatten inv
    (∀ r ∈ cmd.reads, pred r) → ∀ r ∈ cmd.writes, pred r := by
  intro v prior pool pred inputs r hw
  have ok := leafInv (inputs _ reads).1
  rw [writes] at hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl|rfl
  · constructor
    · apply rootInv
      intro s j hj
      exact roots_read p hv mode rs words size geom mem ok buf order root rootLinked s ⟨j,hj⟩
    · rintro ⟨_, b, _⟩ own
      rcases b with z | ⟨t, z | (l | a)⟩ | ⟨j, c | a⟩ <;> cases own
  · refine ⟨authInv, ?_⟩
    intro b own
    let w : MetalReducerBytes.Field g rs.length := ⟨b,by simp [own]⟩
    have seen := authCovered w own
    have writesByte := MetalReducerBytes.survives g nEq dEq cEq sigEq forsEq xmssEq wotsAt wotsByte wots atLinked
      schedule v initial capacity bound w seen
    exact writesByte.trans (sig_field p hv mode rs words size geom mem ok g nEq dEq hpEq cEq sigEq forsEq xmssEq
      f authLinked other w own).symm

end MetalXmssDispatch
