import Parallel.XmssPlanProgram
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelXmssTicket
def target (hp : Nat) := if hp≥6 then 3 else 2
def depth (hp h : Nat) := h-target hp
def root (idx h : Nat) := (idx/2^h)^^^1

theorem chunk_bound (hp idx h c : Nat) (maxH : hp≤9) (below : h<hp)
    (leaf : idx<2^hp) (active : c<2^(depth hp h)) :
    (root idx h*2^(depth hp h)+c+1)*2^(h-depth hp h)≤512 := by
  have power : 2^(hp-h)*2^h=2^hp := by rw [←Nat.pow_add,Nat.sub_add_cancel below.le]
  have digit : idx/2^h<2^(hp-h) := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm,power];exact leaf)
  have room := Nat.xor_lt_two_pow digit (show 1<2^(hp-h) from lt_of_lt_of_le (by decide : 1<2^1)
    (Nat.pow_le_pow_right (by decide) (by omega)))
  have depthLe : depth hp h≤h := Nat.sub_le .. 
  calc
    _ ≤ ((root idx h+1)*2^(depth hp h))*2^(h-depth hp h) := Nat.mul_le_mul_right _ (by rw [Nat.add_mul,Nat.one_mul];omega)
    _ = (root idx h+1)*2^h := by rw [Nat.mul_assoc,←Nat.pow_add,Nat.add_sub_of_le depthLe]
    _ ≤ 2^(hp-h)*2^h := Nat.mul_le_mul_right _ room
    _ ≤ _ := power ▸ Nat.pow_le_pow_right (by decide) maxH

theorem chunk_spec (p : params.Params) (j : Usize) (index h : U32) (c start : Usize)
    (maxH : p.hp.val≤9) (below : h.val<p.hp.val) (leaf : index.val<2^p.hp.val)
    (layer : j.val<65536) (active : c.val<2^(depth p.hp.val h.val))
    (space : start.val+2^(depth p.hp.val h.val)≤Usize.max) :
    chunk p j index h c start ⦃ next r sp level first lj idx z slot =>
      next.val=start.val+2^(depth p.hp.val h.val) ∧ r.val=root index.val h.val ∧
      sp.val=depth p.hp.val h.val ∧ level=h ∧ first=start ∧ lj.val=j.val ∧
      idx.val=root index.val h.val*2^(depth p.hp.val h.val)+c.val ∧
      z.val=h.val-depth p.hp.val h.val ∧ slot.val=start.val+c.val ⦄ := by
  let chosen : U32 := if p.hp≥6#u32 then 3#u32 else 2#u32
  have choice : (if p.hp≥6#u32 then ok 3#u32 else ok 2#u32)=ok chosen := by simp [chosen];split <;> rfl
  have tv : chosen.val=target p.hp.val := by
    unfold chosen target; split <;> rename_i g <;> split <;> scalar_tac
  have sat : (core.num.U32.saturating_sub h chosen).val=depth p.hp.val h.val := by
    change (0 ⊔ (h.val-chosen.val)) % 2^32 = _
    rw [Nat.max_eq_right (Nat.zero_le _),Nat.mod_eq_of_lt (by omega),tv];rfl
  have dLe : depth p.hp.val h.val≤h.val := Nat.sub_le ..
  have platform := System.Platform.le_numBits
  have powLe := Nat.pow_le_pow_right (by decide : 0<2) (show depth p.hp.val h.val≤9 by omega)
  have bound := chunk_bound _ _ _ _ maxH below leaf active
  have pos := Nat.le_mul_of_pos_right (root index.val h.val*2^(depth p.hp.val h.val)+c.val+1)
    (Nat.two_pow_pos (h.val-depth p.hp.val h.val))
  unfold chunk
  rw [choice]
  simp only [bind_ok]
  step as ⟨high,hv,_⟩
  try simp only [lift,bind_ok]
  have rv : (high ^^^ 1#u32).val=root index.val h.val := by simp [root,UScalar.val_xor,hv,Nat.shiftRight_eq_div_pow]
  step as ⟨sub,sv⟩
  all_goals try scalar_tac
  step as ⟨groups,gv,_⟩
  all_goals try scalar_tac
  have groupEq : groups.val=2^(depth p.hp.val h.val) := by
    rw [gv,Nat.one_shiftLeft,sat,Nat.mod_eq_of_lt];scalar_tac
  step as ⟨next,nv⟩
  all_goals try scalar_tac
  try simp only [lift,bind_ok]
  step as ⟨base,bv,_⟩
  all_goals try scalar_tac
  have baseEq : base.val=root index.val h.val*2^(depth p.hp.val h.val) := by
    rw [bv,Nat.shiftLeft_eq,rv,sat,Nat.mod_eq_of_lt];rw [U32.size_eq];omega
  try simp only [lift,bind_ok]
  have castC := cast_u32_usize_val c (by omega)
  have castJ : (UScalar.cast .U16 j).val=j.val := by scalar_tac
  step as ⟨idx,iv⟩
  step as ⟨slot,loc⟩
  all_goals first | exact ⟨by rw [nv,groupEq],rv,sat,rfl,rfl,castJ,by rw [iv,baseEq,castC],by rw [sv,sat],loc⟩ | scalar_tac

/-- Execute the producer and consumer together. The returned destination and
digest identify the child chunk of the selected authentication sibling. -/
theorem issued_subtree {N : Usize} (p : params.Params) (hp : PN p N) (node : Node N)
    (law : NodeLaw p node 512) (layers : alloc.vec.Vec (address.Adrs × U32)) (j : Usize)
    (index h : U32) (c start : Usize) (sk seed : Array U8 N)
    (inside : j.val<layers.length) (selected : layers.val[j.val]!.2=index)
    (layer : j.val<65536) (below : h.val<p.hp.val) (leaf : index.val<2^p.hp.val)
    (active : c.val<2^(depth p.hp.val h.val)) (space : start.val+2^(depth p.hp.val h.val)≤Usize.max) :
    (do let (_,_,_,_,_,lj,i,z,dest) ← chunk p j layers.val[j.val]!.2 h c start
        subtree_ticket node layers lj i z dest sk seed) ⦃ (dest,r) =>
      dest.val=start.val+c.val ∧ bytes r.val=Spec.xmssNode (Shake.params p) (bytes sk.val)
        (root index.val h.val*2^(depth p.hp.val h.val)+c.val) (h.val-depth p.hp.val h.val)
        (bytes seed.val) (adrsS layers.val[j.val]!.1) ⦄ := by
  rw [selected]
  obtain ⟨⟨_,_,_,_,_,lj,i,z,slot⟩,run,_,_,_,_,_,layerEq,iEq,zEq,slotEq⟩ := spec_imp_exists
    (chunk_spec p j index h c start hp.valid.hp_le below leaf layer active space)
  simp only [run,bind_ok]
  have bound := chunk_bound _ _ _ _ hp.valid.hp_le below leaf active
  apply WP.spec_mono (subtree_spec p node 512 law layers lj i z slot sk seed
    (by rw [layerEq];exact inside) (by rw [iEq,zEq];exact bound))
  rintro ⟨dest,r⟩ ⟨rfl,val⟩
  exact ⟨slotEq,by simpa only [iEq,zEq,layerEq] using val⟩

end slhdsa.ParallelXmssTicket
