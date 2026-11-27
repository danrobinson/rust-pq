import Armwide.XmssLeafDigests
import Armwide.XmssLeafPadding
import Armwide.Xmss.PhysicalParents
open Aeneas Aeneas.Std Result
namespace slhdsa.Armwide.XmssLeaves
open Keygen
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

abbrev Rows (G L : Usize) := Array (Array U8 L) G

def endpoints {N G L : Usize} (state : Array U32 8#usize) (sk : Array U8 N) (a : slhdsa.address.Adrs)
    (first : U32) (rows : Rows G L) : Rows G L :=
  .from (List.ofFn (fun k : Fin G.val => ArmXmss.row L <|
    (slhdsa.bytes rows.val[k.val]!.val).setSlice! 22
      (bytesAt N.val G.val (wv state.val) (slhdsa.bytes sk.val) (slhdsa.adrsS a) first.val k.val))) (by simp)

def message {G L : Usize} (rows : Rows G L) (i : Nat) := slhdsa.bytes rows.val[i]!.val

def digest512 {N G L : Usize} (hard : Bool) (st : Array U64 8#usize) (rows : Rows G L) (i : Nat) :=
  batched512 G.val i hard N.val (S512.wv st.val) (message rows)
def digest256 {G L : Usize} (st : Array U32 8#usize) (rows : Rows G L) (i : Nat) :=
  batched256 G.val i (wv st.val) (message rows)

theorem endpoint_message {N G L : Usize} (p : params.Params) (hp : PN p N) (seed : hash.Seed N) (hs : SeedOk seed)
    (sk : Array U8 N) (a : slhdsa.address.Adrs) (first : U32) (rows : Rows G L)
    (lanes : G.val=2 ∨ G.val=4) (k : Nat) (key : k<G.val)
    (ready : prepared N.val (slhdsa.adrsS a) (first.val+k) rows.val[k]!) :
    message (endpoints seed.state sk a first rows) k =
      padded N.val (leafAddr (slhdsa.adrsS a) (first.val+k)) (filled N.val
        (payload (paramsS p) (slhdsa.bytes seed.pk_seed.val) (slhdsa.bytes sk.val)
          (leafAddr (slhdsa.adrsS a) (first.val+k)) (2*N.val+3))) := by
  let P := paramsS p
  have state : wv seed.state.val = seedState P.n (slhdsa.bytes seed.pk_seed.val) := by rw [hp.n]; exact hs.1
  have values := payload_fips P hp.valid (slhdsa.bytes seed.pk_seed.val) (slhdsa.bytes sk.val)
    (by rw [hp.n];simp) (by rw [hp.n];simp) (slhdsa.adrsS a) first.val G.val k lanes key
  rw [hp.n] at values state
  simp only [message,endpoints,Array.from_val,List.getElem!_eq_getElem?_getD,List.getElem?_ofFn,key,↓reduceDIte,Option.getD_some]
  rw [ArmXmss.row_eq _ _ (by simp [slhdsa.bytes_length]),state,values]
  simpa only [List.getElem!_eq_getElem?_getD] using ready _ (by rw [payload_size P hp.valid,hp.n];rfl)

theorem leafValue {N G L : Usize} (p : params.Params) (hp : PN p N) (seed : hash.Seed N) (hs : SeedOk seed)
    (sk : Array U8 N) (a : slhdsa.address.Adrs) (first : U32) (rows : Rows G L)
    (lanes : G.val=2 ∨ G.val=4) (size : L.val=total N.val) (k : Nat) (key : k<G.val)
    (hard : Bool) (ready : prepared N.val (slhdsa.adrsS a) (first.val+k) rows.val[k]!) :
    let m := endpoints seed.state sk a first rows
    (if N.val=16 then digest256 seed.state m k else digest512 (N:=N) hard seed.state512 m k) =
      Spec.xmssNode (paramsS p) (slhdsa.bytes sk.val) (first.val+k) 0 (slhdsa.bytes seed.pk_seed.val) (slhdsa.adrsS a) := by
  let P:=paramsS p
  let addr:=leafAddr (slhdsa.adrsS a) (first.val+k)
  let m:=endpoints seed.state sk a first rows
  let msg:=payload P (slhdsa.bytes seed.pk_seed.val) (slhdsa.bytes sk.val) addr (2*N.val+3)
  have ps : msg.length=payLen P.n := by rw [payload_size P hp.valid,hp.n];rfl
  have wide (large : P.n≠16) : S512.wv seed.state512.val = H512.Multi.pkState512 P.n (slhdsa.bytes seed.pk_seed.val) := by
    rw [hp.n] at large ⊢;simpa only [H512.Multi.pkState512,toByte_zero] using hs.2 large
  have eq := compression_T P hp.valid (slhdsa.bytes seed.pk_seed.val) msg (by rw [hp.n];simp) ps addr hard _ wide
  rw [hp.n] at eq
  have data : message m k = padded N.val addr (filled N.val msg) := endpoint_message p hp seed hs sk a first rows lanes k key ready
  have sz (i : Nat) : (message m i).length=total N.val := by simp [message,size]
  have st : wv seed.state.val=seedState N.val (slhdsa.bytes seed.pk_seed.val) := hs.1
  change (if N.val=16 then digest256 seed.state m k else digest512 (N:=N) hard seed.state512 m k) = _
  calc
    _ = compression N.val hard (seedState N.val (slhdsa.bytes seed.pk_seed.val)) (S512.wv seed.state512.val) (message m k) := by
      by_cases small : N.val=16
      · simp only [small,ite_true,digest256,batched256_eq _ _ lanes key,st,compression]
        have route : (calls[hard.toNat]!)[group 16]! = [(256,640)] := by cases hard <;> decide
        have len : (message m k).length=640 := by rw [sz,small];rfl
        rw [route,len];rfl
      · have width : N.val=24 ∨ N.val=32 := hp.nok.resolve_left small
        have nst : (S512.wv seed.state512.val).length=8 := by simp [S512.wv]
        simp only [small,↓reduceIte,digest512,batched512_eq _ width _ _ lanes key _ _ nst _ (fun i _ => sz i),
          route512 _ width _ _ _ nst _ (sz k)]
    _ = Spec.T P (slhdsa.bytes seed.pk_seed.val) (Spec.wotsPkAdrs addr) msg := by rwa [data]
    _ = _ := by
      unfold Spec.xmssNode Spec.wotsPkGen
      rw [hp.len]
      have w : P.w=16 := by change (paramsS p).w=16; simp [Spec.Params.w,hp.valid.lgw_eq]
      change _ = Spec.T P _ _ _
      rw [w]
      rfl

end slhdsa.Armwide.XmssLeaves
