import Armwide.XmssLeavesProgram
import Armwide.KeyCompression
namespace slhdsa.Armwide.XmssLeaves
open Keygen Transitions Spec.SHA256
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def source (n g k c : Nat) := (writes[2*group n+(if g=2 then 0 else 1)]!)[k*(2*n+3)+c]!

private theorem coords (n g : Nat) (width : n=16 ∨ n=24 ∨ n=32) (lanes : g=2 ∨ g=4) :
    ∀ (k : Fin g) (c : Fin (2*n+3)), source n g k c = ⟨k,22+c.val*n,0,0⟩ := by
  rcases width with rfl|rfl|rfl <;> rcases lanes with rfl|rfl <;> decide

def leafAddr (a : Spec.Adrs) (key : Nat) : Spec.Adrs :=
  {a.setTypeAndClear Spec.WOTS_HASH with keypair:=key}

private def run (n : Nat) (st : List Word) (a : Spec.Adrs) (first k c : Nat)
    (digest : Arm.V × Arm.V) (op : Operation) :=
  runCall n st (leafAddr a (first+((k:Int)+op.keyDelta).toNat)) c digest ⟨op.tag,op.chainDelta,op.counter⟩

def value (n g : Nat) (st : List Word) (sk : Spec.Bytes) (a : Spec.Adrs) (first k c : Nat) :=
  let w := source n g k c
  let initial := if w.origin=0 then loadDigest n sk else (default,default)
  let r := (traces[w.trace]!).foldl (run n st a first k c) initial
  storedBytes n r.1 r.2

private def liftCall (op : Keygen.Call) : Operation := ⟨0,op.head,op.chainDelta,op.counter⟩
private def single := (⟨5,0,0⟩ : Keygen.Call)::(List.range 15).map (fun t => ⟨0,0,t⟩)
private theorem traced : traces[0]! = single.map liftCall := by decide

theorem endpoint_fips (p : Spec.Params) [Fact (p.family=.sha2)] (valid : p.Valid) (pk sk : Spec.Bytes)
    (plen : pk.length=p.n) (slen : sk.length=p.n) (a : Spec.Adrs) (first g k c : Nat)
    (lanes : g=2 ∨ g=4) (key : k<g) (chain : c<2*p.n+3) :
    value p.n g (seedState p.n pk) sk a first k c =
      reference p pk sk (leafAddr a (first+k)) c := by
  rw [← endpoint_eq p valid pk sk plen slen _ c chain,endpoint_program _ valid.n_cases _ _ _ _ chain]
  unfold value
  rw [coords p.n g valid.n_cases lanes ⟨k,key⟩ ⟨c,chain⟩]
  simp only [traced,↓reduceIte,List.foldl_map,run,liftCall,Int.add_zero,Int.toNat_natCast,single]

def bytesAt (n g : Nat) (st : List Word) (sk : Spec.Bytes) (a : Spec.Adrs) (first k : Nat) :=
  (List.range (2*n+3)).flatMap (value n g st sk a first k)

theorem payload_fips (p : Spec.Params) [Fact (p.family=.sha2)] (valid : p.Valid) (pk sk : Spec.Bytes)
    (plen : pk.length=p.n) (slen : sk.length=p.n) (a : Spec.Adrs) (first g k : Nat)
    (lanes : g=2 ∨ g=4) (key : k<g) :
    bytesAt p.n g (seedState p.n pk) sk a first k =
      payload p pk sk (leafAddr a (first+k)) (2*p.n+3) := by
  unfold bytesAt payload
  apply List.flatMap_congr
  intro c hc
  exact endpoint_fips p valid pk sk plen slen a first g k c lanes key (List.mem_range.mp hc)

end slhdsa.Armwide.XmssLeaves
