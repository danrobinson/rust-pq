import Wots.RecoveryRows
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Wots
open Spec.SHA256
open WotsRust.sha256.x86.avx512

def endpointsInRows (N : Usize) (digits : Slice U32) (expect : Nat → Spec.Bytes) (base buf : Buffers) :=
  rowsSafe N digits.length base buf ∧ ∀ r < digits.length, rowComplete N expect base buf r

private def invariant (P : Spec.Params) (N : Usize) (pk : Spec.Bytes) (a : Spec.Adrs)
    (sig : Slice U8) (digits : Slice U32) (base : Buffers) (order : Order) (work : Usize)
    (s : RecoveryState) :=
  let (buf,w,ix,_,_,c,m,p,h) := s
  let expect i := chainAt P N pk a sig digits i 15
  rowsSafe N digits.length base buf ∧ p.val ≤ work.val ∧ laneStateOK P N pk a sig digits ix m c h w ∧
    (∀ r < digits.length, digits.val[r]!.val = 15 → rowComplete N expect base buf r) ∧
    ∃ owner, owns order ix m p.val owner ∧ accounted N expect base buf order p.val owner

private theorem prefix_of_chains {P N pk a sig digits ix m c h w} (base : Words)
    (lanes : laneStateOK P N pk a sig digits ix m c h w) (shape : N.val ≤ 32) (key : a.keypair < 2^32)
    (words : ∀ j k, k < 16 → base.val[k]! j = word (template {a with word2 := 0} (List.replicate N.val 0)) (4*k)) :
    samePrefix base w := by
  intro k hk j
  obtain ⟨small,ready,_⟩ := lanes j
  have eq := ready (fun _ => 0) 0 k (by omega)
  rw [packed_prefix _ _ _ _ k hk,packed_prefix _ _ _ _ k hk] at eq
  rw [words j k (by omega)]
  exact eq.trans (by rw [change_chain_word a _ 0 (chainIndex ix j) k key (by simp; omega) (by decide) small,
    if_neg (by omega)])

set_option maxHeartbeats 2000000 in
theorem loop_endpoints (P : Spec.Params) [Fact (P.family=.sha2)] (N : Usize)
    (pk : Spec.Bytes) (a : Spec.Adrs) (sig : Slice U8) (digits : Slice U32)
    (order : Order) (work : Usize) (base : Words) (iv pre : Hash) (original out : Buffers)
    (width : N.val=P.n) (shape : P.n=16 ∨ P.n=24 ∨ P.n=32) (hpk : pk.length=P.n)
    (key : a.keypair < 2^32) (seed : ∀ j, stateWords (laneState iv j)=seedState P.n pk)
    (words : ∀ j k, k < 16 → base.val[k]! j = word (template {a with word2 := 0} (List.replicate N.val 0)) (4*k))
    (initial : Trace pre (fun j => schedule (Leaf.blockOf (chainWords base j))) (laneState iv) 4)
    (small : digits.length ≤ 67) (rows : digits.length ≤ original.length) (available : N.val*digits.length ≤ sig.length)
    (ordered : ∀ i < digits.length, order.val[rank digits.val i]!.val = i)
    (valid : ∀ i < digits.length, digits.val[i]!.val < 16) (workload : work.val = digits.length-frequency digits.val 15)
    (safe0 : rowsSafe N digits.length original out)
    (bypass : ∀ r < digits.length, digits.val[r]!.val = 15 →
      rowComplete N (fun i => chainAt P N pk a sig digits i 15) original out r) :
    let z : Reg := fun _ => 0
    let empty := Array.repeat 16#usize 0#i32
    recover_loop5 N z sig digits out order work base iv pre (fun _ => 0xffff) Store.control empty empty z z
      0#u16 0#usize (Array.repeat 8#usize z) ⦃ buf =>
        endpointsInRows N digits (fun i => chainAt P N pk a sig digits i 15) original buf ⦄ := by
  dsimp only
  let expect i := chainAt P N pk a sig digits i 15
  have shapes : N.val=16 ∨ N.val=24 ∨ N.val=32 := width ▸ shape
  unfold recover_loop5
  apply loop.spec_decr_nat (measure := loopWork work) (inv := invariant P N pk a sig digits original order work)
  · rintro ⟨buf,w,ix,st,id,c,m,p,h⟩ ⟨safe,cap,lanes,doneRows,owner,owns0,prior⟩
    change recover_loop5.body N _ sig digits order work iv pre _ _ buf w ix st id c m p h ⦃ _ ⦄
    rw [cycle_body_eq]
    split
    next guard =>
      unfold iteration
      have queued (q) (lt : q < work.val) := (order_at digits order ordered q (by omega)).1
      step with refill_spec digits order work ix st m p cap (by omega) queued as ⟨s,fill,le,stop⟩
      obtain ⟨ix',st',mask,next,assigned⟩ := s
      dsimp only at le stop
      obtain ⟨owner',owns1,keepOwners,added⟩ := refill_owns owns0 fill
      have recorded := accounted_refill prior keepOwners added
      have round (loaded id' : Reg) (hash' : Hash) (w' : Words)
          (live : laneStateOK P N pk a sig digits ix' mask loaded hash' w')
          (keep : assigned=0#u16 → loaded=c) :
          cycle N iv pre (fun _ => 0xffff) buf ix' st' id' loaded mask next hash' w' ⦃ flow =>
            match flow with
            | done b => endpointsInRows N digits expect original b
            | cont s => invariant P N pk a sig digits original order work s ∧ loopWork work s < remainingWork work p m c ⦄ := by
        have same := prefix_of_chains base live (by omega) key words
        apply WP.spec_mono (cycle_chains P N pk a sig digits iv pre hash' w' ix' st' id' loaded mask next order owner' buf
          width shape hpk seed (recovery_prefix N hash' loaded iv pre same initial) owns1 ordered (by omega) small
          (safe.1 ▸ rows) live)
        rintro _ ⟨packed,digest,after,survivors,b,rfl,inc,bits,live',values,writes,correct⟩
        obtain ⟨safe',preserve,records⟩ := account_retirement original buf b values loaded after survivors expect owns1
          ordered (by omega) small rows safe recorded inc bits writes correct
        refine ⟨⟨safe',le,live',fun r hr d => preserve r (by omega) (doneRows r hr d),_,
          remaining_owns owns1 survivors (fun j on => ((bits j).mp on).1),records⟩,?_⟩
        exact recovery_descent fill work le stop guard c loaded after survivors keep (fun j on => ((lanes j).2.2 on).2.2.1) inc bits
      by_cases nz : assigned ≠ 0#u16
      · rw [if_pos (bne_iff_ne.mpr nz)]
        have below (q) (hq : q<next.val) := order_partition digits order valid ordered q (by omega)
        step with load_chains c (fun _ => 0) h w fill lanes key shapes
          (fun q hq => ⟨(below q hq).1,(below q hq).2.1.mp (by omega)⟩) nz small available as ⟨state,installed⟩
        obtain ⟨id',loaded,hash',w'⟩ := state
        apply WP.spec_mono (round loaded id' hash' w' installed (fun eq => (nz eq).elim))
        intro flow post; cases flow <;> exact post
      · rw [if_neg (fun b => nz (bne_iff_ne.mp b))]
        have zero := Classical.not_not.mp nz
        subst assigned
        apply WP.spec_mono (round c id h w (no_load_lanes fill lanes) (fun _ => rfl))
        intro flow post; cases flow <;> exact post
    next halt =>
      simp only [step_simps]
      have off : m = 0#u16 := Classical.not_not.mp (fun on => halt (Or.inl on))
      have exhausted : p.val=work.val := by
        have hp : ¬p<work := fun lt => halt (Or.inr lt)
        change ¬ p.val<work.val at hp; omega
      refine ⟨safe,?_⟩
      intro r hr
      by_cases d : digits.val[r]!.val = 15
      · exact doneRows r hr d
      · let q := rank digits.val r
        have hq := rank_bound digits.val r hr
        have read := ordered r hr
        have part := order_partition digits order valid ordered q hq
        have short := valid r hr
        have eq : order.val[q]!.val = r := read
        rw [eq] at part
        have consumed : q < p.val := by rw [exhausted,workload]; exact part.2.1.mpr (by omega)
        rcases prior q consumed with ⟨j,hj⟩|complete
        · have on := owns0.2 j; rw [hj] at on; have enabledJ := on.1; simp [off,enabled] at enabledJ
        · exact eq ▸ complete
  · refine ⟨safe0,by simp,?_,bypass,fun _ => none,⟨by simp,by simp [enabled]⟩,?_⟩
    · intro j
      have zero : chainIndex (Array.repeat 16#usize 0#i32) j = 0 := by fin_cases j <;> decide
      rw [zero]
      exact ⟨by decide,address_initial base N.val a shapes words j,by simp [enabled]⟩
    · intro q h; change q < 0 at h; omega

end slhdsa.X86.Wots
