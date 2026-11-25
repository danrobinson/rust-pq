import Armwide.EndpointProgram
import Armwide.SignBlocks
import Armwide.SignLoad
import Spec.Correctness
import Slhdsa.Proofs.Encoding

namespace slhdsa.Armwide.Keygen
open Transitions Spec.SHA256
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def hashAddr (a : Spec.Adrs) : Spec.Adrs := {a.setTypeAndClear Spec.WOTS_HASH with keypair:=a.keypair}
def group (n : Nat) := if n=16 then 0 else if n=24 then 1 else 2
private def source (n i : Nat) := (stores[group n]!)[i]!
private def expected := (⟨5,0,0⟩ : Call)::(List.range 15).map (fun t => ⟨0,0,t⟩)

private theorem coordinate (n : Nat) (width : n=16 ∨ n=24 ∨ n=32) :
    ∀ i < 2*n+3, source n i = ⟨22+i*n,0,0⟩ := by
  have f16 : ∀ i : Fin 35, source 16 i = ⟨22+i.val*16,0,0⟩ := by decide
  have f24 : ∀ i : Fin 51, source 24 i = ⟨22+i.val*24,0,0⟩ := by decide
  have f32 : ∀ i : Fin 67, source 32 i = ⟨22+i.val*32,0,0⟩ := by decide
  intro i hi
  rcases width with rfl|rfl|rfl
  · exact f16 ⟨i,hi⟩
  · exact f24 ⟨i,hi⟩
  · exact f32 ⟨i,hi⟩

private theorem shape : traces[0]! = expected := by decide

private def runCall (n : Nat) (st : List Word) (a : Spec.Adrs) (c : Nat) (v : Arm.V × Arm.V) (op : Call) :=
  hashRegisters n st {a.setTypeAndClear op.head with keypair:=a.keypair}
    ((c:Int)+op.chainDelta).toNat op.counter v.1 v.2

def endpoint (n : Nat) (st : List Word) (sk : Spec.Bytes) (a : Spec.Adrs) (c : Nat) : Spec.Bytes :=
  let row := source n c
  let initial := if row.origin=0 then loadDigest n sk else (default,default)
  let v := (traces[row.trace]!).foldl (runCall n st a c) initial
  storedBytes n v.1 v.2

private theorem calls_fips (p : Spec.Params) [Fact (p.family=.sha2)] (valid : p.Valid) (pk : Spec.Bytes)
    (plen : pk.length=p.n) (a : Spec.Adrs) (c : Nat) (small : c<65536) (ts : List Nat) (v : Arm.V × Arm.V) :
    let r := (ts.map fun t => (⟨0,0,t⟩ : Call)).foldl (runCall p.n (seedState p.n pk) a c) v
    storedBytes p.n r.1 r.2 = ts.foldl (fun x t => Spec.F p pk {hashAddr a with word2:=c,word3:=t} x)
      (storedBytes p.n v.1 v.2) := by
  induction ts generalizing v with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons,List.foldl_cons,ih]
    congr 1
    rw [F_eq]
    have step := native_tweakable_hash p.n valid.n_cases pk plen (hashAddr a) c t small v.1 v.2
    simpa only [runCall,hashAddr,Spec.WOTS_HASH,Int.add_zero,Int.toNat_natCast,stored_eq p.n valid.n_cases] using step

def reference (p : Spec.Params) (pk sk : Spec.Bytes) (a : Spec.Adrs) (c : Nat) :=
  Spec.chain p (Spec.PRF p pk sk {Spec.wotsSkAdrs a with word2:=c}) 0 15 pk {hashAddr a with word2:=c}

/-- Every source-derived destination chain receives PRF followed by all fifteen FIPS steps. -/
theorem endpoint_eq (p : Spec.Params) [Fact (p.family=.sha2)] (valid : p.Valid) (pk sk : Spec.Bytes)
    (plen : pk.length=p.n) (slen : sk.length=p.n) (a : Spec.Adrs) (c : Nat) (hc : c<2*p.n+3) :
    endpoint p.n (seedState p.n pk) sk a c = reference p pk sk a c := by
  have small : c<65536 := by have := valid.n_cases; omega
  unfold endpoint
  rw [coordinate p.n valid.n_cases c hc]
  simp only [shape,expected,List.foldl_cons,↓reduceIte]
  rw [calls_fips p valid pk plen a c small]
  have prf := native_tweakable_hash p.n valid.n_cases pk plen (Spec.wotsSkAdrs a) c 0 small
    (loadDigest p.n sk).1 (loadDigest p.n sk).2
  rw [load_content p.n valid.n_cases sk slen] at prf
  unfold reference Spec.chain
  simp only [PRF_eq,Nat.zero_add,runCall,Int.add_zero,Int.toNat_natCast]
  congr 1

def payload (p : Spec.Params) (pk sk : Spec.Bytes) (a : Spec.Adrs) (k : Nat) :=
  (List.range k).flatMap (reference p pk sk a)

theorem ref_size (p : Spec.Params) (valid : p.Valid) (pk sk : Spec.Bytes) (a : Spec.Adrs) (c : Nat) :
    (reference p pk sk a c).length=p.n :=
  Spec.chain_length p valid _ (Spec.PRF_length p valid ..) .. 

theorem payload_size (p : Spec.Params) (valid : p.Valid) (pk sk : Spec.Bytes) (a : Spec.Adrs) (k : Nat) :
    (payload p pk sk a k).length=k*p.n := by
  induction k with
  | zero => simp [payload]
  | succ k ih =>
    simp only [payload,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.length_append,ref_size p valid,Nat.succ_mul] at *
    exact congrArg (·+p.n) ih

def writeEndpoints (n : Nat) (st : List Word) (sk : Spec.Bytes) (a : Spec.Adrs) (buf : Spec.Bytes) :=
  (List.range (2*n+3)).foldl (fun b i => b.setSlice! (source n i).offset (endpoint n st sk a i)) buf

theorem write_size (n : Nat) (st : List Word) (sk : Spec.Bytes) (a : Spec.Adrs) (buf : Spec.Bytes) :
    (writeEndpoints n st sk a buf).length=buf.length := by
  unfold writeEndpoints
  generalize List.range (2*n+3) = ids
  induction ids generalizing buf with
  | nil => rfl
  | cons i ids ih => rw [List.foldl_cons,ih,List.length_setSlice!]

theorem written (p : Spec.Params) [Fact (p.family=.sha2)] (valid : p.Valid) (pk sk : Spec.Bytes)
    (plen : pk.length=p.n) (slen : sk.length=p.n) (a : Spec.Adrs) (total : Nat)
    (room : 22+(2*p.n+3)*p.n ≤ total) :
    writeEndpoints p.n (seedState p.n pk) sk a (List.replicate total 0#8) =
      List.replicate 22 0#8 ++ payload p pk sk a (2*p.n+3) ++ List.replicate (total-22-(2*p.n+3)*p.n) 0#8 := by
  unfold writeEndpoints
  generalize len_eq : 2*p.n+3 = len
  have go (k : Nat) (le : k≤len) :
      (List.range k).foldl (fun b i => b.setSlice! (source p.n i).offset (endpoint p.n (seedState p.n pk) sk a i))
        (List.replicate total 0#8) =
      List.replicate 22 0#8 ++ payload p pk sk a k ++ List.replicate (total-22-k*p.n) 0#8 := by
    induction k with
    | zero =>
      simp only [List.range_zero,List.foldl_nil,payload,List.flatMap_nil,List.append_nil,Nat.zero_mul,Nat.sub_zero,
        ← List.replicate_add]; congr 1; omega
    | succ k ih =>
      rw [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,ih (by omega),
        coordinate p.n valid.n_cases k (by omega),endpoint_eq p valid pk sk plen slen a k (by omega)]
      have bound : 22+(k+1)*p.n ≤total := by
        calc
          _ ≤ 22+len*p.n := Nat.add_le_add_left (Nat.mul_le_mul_right _ le) _
          _ ≤ total := by rwa [←len_eq]
      have offset : 22+k*p.n=(List.replicate 22 0#8 ++ payload p pk sk a k).length := by simp only [List.length_append,List.length_replicate,payload_size p valid]
      have zeros : total-22-k*p.n = p.n + (total-22-(k+1)*p.n) := by rw [Nat.add_mul,Nat.one_mul] at bound ⊢; omega
      rw [zeros,List.replicate_add,←List.append_assoc,slhdsa.setSlice_mid' _ _ _ _ _ offset (by simp [ref_size p valid])]
      simp [payload,List.range_succ,List.append_assoc]
  exact go len (by omega)

end slhdsa.Armwide.Keygen
