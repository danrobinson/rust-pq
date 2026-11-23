import Wots.Prefix
import Leaf256.Address
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots
open Spec.SHA256

private theorem type_change (a : Spec.Adrs) (sk : Spec.Bytes) (small : sk.length ≤ 33) (k : Nat) :
    Leaf.withType (fun i => word (padFrom 64 ({a with typ := 5}.compress ++ sk)) (4*i)) 0x50000 k =
      word (padFrom 64 ({a with typ := 0}.compress ++ sk)) (4*k) := by
  rw [padFrom_blk _ _ small,padFrom_blk _ _ small]
  let head := a.compress.take 9
  let tail := a.compress.drop 10 ++ (sk ++ padTail sk.length)
  have prf : {a with typ := 5}.compress ++ (sk ++ padTail sk.length) = head ++ (5#8 :: tail) := by
    simp only [head,tail,compress_eq]; rfl
  have hash : {a with typ := 0}.compress ++ (sk ++ padTail sk.length) = head ++ (0#8 :: tail) := by
    simp only [head,tail,compress_eq]; rfl
  rw [prf,hash]
  exact Leaf.type_word 5#8 0#8 head tail (by simp [head,adrs_compress_length]) k

/-- Each lane returns the Algorithm 6 endpoint for its own keypair and chain,
including PRF generation and all fifteen applications of F. -/
theorem batch_fips (P : Spec.Params) [Fact (P.family = .sha2)] (N len pos : Usize) (first : U32)
    (iv two : Hash) (base : Words) (pk sk : Spec.Bytes) (a : Spec.Adrs)
    (hn : N.val = P.n) (shape : P.n=16 ∨ P.n=24 ∨ P.n=32)
    (hpk : pk.length = P.n) (hsk : sk.length = P.n)
    (lo : 16 ≤ len.val) (hi : len.val ≤ 67) (safe : first.val+pos.val/len.val < 2^32)
    (seed : ∀ j, stateWords (laneState iv j) = seedState P.n pk)
    (ready : ∀ j k, k < 16 → base.val[k]! j =
      word (padFrom 64 ((a.setTypeAndClear Spec.WOTS_PRF).compress ++ sk)) (4*k))
    (prefixOK : Trace two (fun j => schedule (laneBlock base j)) (laneState iv) 2) :
    batch N len pos first (fun j => BitVec.ofNat 32 j.val) (fun _ => 0xffff)
      (fun _ => 0x50000) iv two base ⦃ out => ∀ j : Fin 16,
      let key := BitVec.ofNat 32 (first.val+(pos.val+j.val)/len.val)
      let id := (pos.val+j.val)%len.val
      let address := {a with typ := 0, keypair := key.toNat, word2 := id, word3 := 0}
      (ser (stateWords (laneState out j))).take P.n = Spec.chain P
        (Spec.PRF P pk sk {Spec.wotsSkAdrs address with word2 := id}) 0 15 pk address ⦄ := by
  unfold batch
  step with slot_regs_spec _ first pos len (fun _ => rfl) lo hi safe as ⟨pair,hslots⟩
  obtain ⟨keys,ids⟩ := pair
  simp only at hslots
  step with patch_spec base keys ids as ⟨w,hw⟩
  have length : sk.length ≤ 33 := by omega
  let id := fun j : Fin 16 => (pos.val+j.val)%len.val
  let key := fun j : Fin 16 => BitVec.ofNat 32 (first.val+(pos.val+j.val)/len.val)
  let narrow := fun j : Fin 16 => BitVec.ofNat 16 (id j)
  let A := fun j : Fin 16 => keyAddress (a.setTypeAndClear Spec.WOTS_PRF) (key j) ((narrow j).setWidth 32)
  have idSmall (j) : id j < 2^16 := by have := Nat.mod_lt (pos.val+j.val) (by omega : 0<len.val); dsimp [id]; omega
  have idVal (j) : ((narrow j).setWidth 32).toNat = id j := by simp only [narrow,BitVec.toNat_setWidth,BitVec.toNat_ofNat]; have := idSmall j; omega
  have idsOK (j) : ids j = (narrow j).setWidth 32 := by
    rw [(hslots j).2]; apply BitVec.eq_of_toNat_eq
    rw [idVal,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := idSmall j; dsimp [id] at this; omega)]
  let prfBlock := fun j => padFrom 64 ((A j).compress ++ sk)
  have prfLayout (j) : laneBlock w j = prfBlock j := by
    apply Eq.trans _ (key_address_layout (a.setTypeAndClear Spec.WOTS_PRF) sk (key j) (narrow j) length)
    apply Leaf.block_congr
    intro i hi
    change w.val[i]! j = _
    rw [hw _ hi,(hslots j).1,idsOK]
    unfold keyWords chainWords
    simp only [ready j 2 (by decide),ready j i hi]; rfl
  have trace : Trace two (fun j => schedule (laneBlock w j)) (laneState iv) 2 := by
    apply Leaf.transfer_prefix (by decide) _ prefixOK
    intro j k hk
    simp only [laneBlock,Leaf.word_blockOf _ _ (by omega : k < 16)]
    change _ = w.val[k]! j
    rw [hw _ (by omega)]; simp (disch := omega) only [keyWords,if_neg]
  step with prepare_spec w two iv trace as ⟨bundle,hpre,hx,hc,hd⟩
  obtain ⟨pre,x,c,d⟩ := bundle
  simp only at hpre hx hc hd
  step with compress_block_spec iv pre w (laneBlock w) hpre
    (fun k hk j => (Leaf.word_blockOf (chainWords w j) _ hk).symm) as ⟨secret,hs⟩
  rw [hx]
  step with switch_spec w two iv _ c d trace hc hd as ⟨bundle,hv,hfour⟩
  obtain ⟨v,four⟩ := bundle
  simp only at hv hfour
  let addr := fun j => {A j with typ := 0}
  have wordsOK (j k) (hk : k < 16) :
      v.val[k]! j = word (template (addr j) sk) (4*k) := by
    rw [hv _ hk]
    have eq (i) (h : i < 16) : chainWords w j i = word (prfBlock j) (4*i) := by
      rw [← prfLayout,laneBlock,Leaf.word_blockOf _ _ h]
    unfold Leaf.withType
    simp only [eq 2 (by decide),eq k hk]
    exact type_change (A j) sk length k
  step with endpoint_chain_fips P N pk iv four secret v addr (fun _ => sk) hn shape hpk (fun _ => hsk)
    seed wordsOK hfour as ⟨out,ho⟩
  rename_i j
  rw [ho,hs,seed,prfLayout]
  have skSpec := th256_one P.n pk hpk (by omega) (A j) sk length
  rw [← PRF_eq P] at skSpec
  change Spec.chain P ((ser (compress (seedState P.n pk) (prfBlock j))).take P.n) _ _ _ _ = _
  change (ser (compress (seedState P.n pk) (prfBlock j))).take P.n = Spec.PRF P pk sk (A j) at skSpec
  rw [skSpec]
  let target : Spec.Adrs := {a with typ := 0, keypair := (key j).toNat, word2 := id j, word3 := 0}
  have eq1 : addr j = target := by
    dsimp only [addr,A,keyAddress,Spec.Adrs.setTypeAndClear,target]; rw [idVal]
  have eq2 : A j = {Spec.wotsSkAdrs target with word2 := id j} := by
    dsimp only [A,keyAddress,Spec.Adrs.setTypeAndClear,target,Spec.wotsSkAdrs]; rw [idVal]
  change Spec.chain P (Spec.PRF P pk sk (A j)) 0 15 pk (addr j) =
    Spec.chain P (Spec.PRF P pk sk {Spec.wotsSkAdrs target with word2 := id j}) 0 15 pk target
  rw [eq1,eq2]

end slhdsa.X86.Wots
