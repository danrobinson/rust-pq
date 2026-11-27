import Armplatform.WideForsProtocol
import Armwide.SignLoad
import Armwide.SignBlocks
import Armwide.Xmss.SmallHash
import Paired.Multi
import Spec.Correctness

namespace slhdsa.WideFors
open Armwide Armwide.Transitions Spec.SHA256
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

def leaf256 (n : Nat) (pk : Spec.Bytes) (a : Spec.Adrs) (i : Nat) (m : Spec.Bytes) :=
  let v := loadDigest n m
  let out := hashRegisters n (seedState n pk) a 0 i v.1 v.2
  storedBytes n out.1 out.2

theorem leaf_eq (p : Spec.Params) [Fact (p.family=.sha2)] (valid : p.Valid)
    (pk : Spec.Bytes) (hp : pk.length = p.n) (a : Spec.Adrs) (i : Nat) (m : Spec.Bytes)
    (hm : m.length=p.n) :
    leaf256 p.n pk a i m = Spec.F p pk {a with word2 := 0,word3 := i} m := by
  unfold leaf256
  rw [native_tweakable_hash _ valid.n_cases _ hp _ _ _ (by decide),load_content _ valid.n_cases _ hm,F_eq]

def parent512 (p : Spec.Params) (pk : Spec.Bytes) (a : Spec.Adrs) (l r : Spec.Bytes) :=
  H512.Multi.compressParentHw p.n (H512.Multi.pkState512 p.n pk) (H512.Multi.parentBlock512 p.n a l r)

theorem parent512_eq (p : Spec.Params) [f : Fact (p.family=.sha2)] (wide : p.n=24 ∨ p.n=32)
    (pk : Spec.Bytes) (a : Spec.Adrs) (l r : Spec.Bytes) (hp : pk.length=p.n)
    (hl : l.length=p.n) (hr : r.length=p.n) :
    parent512 p pk a l r = Spec.H p pk a (l++r) :=
  H512.Multi.compressParentHw_eq_fips_H p f.out wide pk l r a hp hl hr

end slhdsa.WideFors
