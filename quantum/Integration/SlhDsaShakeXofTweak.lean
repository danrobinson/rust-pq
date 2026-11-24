import Integration.SlhDsaShakeXofPrf
import MIdeal.Thash512

namespace Reduction.ShakeXof
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
variable (S : Sha2Set) {N : ℕ}
abbrev Payload (xs : List S.Node) := MIdeal.Sha512.payload S xs
def thBytes (pk : S.Node) (a : Bytes 32) (xs : List S.Node) :=
  pk.toList ++ a.toList ++ Payload S xs

/-- Serialize one class of tweakable-hash messages. Its payload must identify the
selected message and fit within the raw public port. -/
def thEmb {M : Type} (pk : S.Node) (nodes : M → List S.Node) (hi : Function.Injective nodes)
    (hc : ∀ m, S.vp.params.n + 32 + S.vp.params.n * (nodes m).length ≤ N) : Bytes 32 × M ↪ ShakeApi.Input N :=
  bytesEmbedding (fun x => thBytes S pk x.1 (nodes x.2))
    (fun x => by simpa only [thBytes,List.length_append,Vector.length_toList,MIdeal.Sha512.payload_length] using hc x.2)
    (by
      rintro ⟨a,x⟩ ⟨b,y⟩ he
      change pk.toList ++ a.toList ++ Payload S (nodes x) = pk.toList ++ b.toList ++ Payload S (nodes y) at he
      obtain ⟨ha,hx⟩ := List.append_inj he (by simp)
      exact Prod.ext (Vector.toList_inj.mp (List.append_cancel_left ha)) (hi (MIdeal.Sha512.payload_injective S hx)))

theorem thash_apply (g : ShakeApi.RawTable S N) (pk : S.Node) (a : Bytes 32) (xs : List S.Node) :
    (ShakeApi.primitives S (ShakeApi.extend g)).Thash pk a xs =
    prefixBytes _ (ShakeApi.extend g (thBytes S pk a xs)) := by rfl

variable {M : Type} (pk : S.Node) (nodes : M → List S.Node) (hi : Function.Injective nodes)
    (hc : ∀ m, S.vp.params.n + 32 + S.vp.params.n * (nodes m).length ≤ N)

theorem thLeaf (g : ShakeApi.RawTable S N) (R : Bytes 32 × M → S.Node) (a : Bytes 32) (m : M) :
    (ShakeApi.primitives S (ShakeApi.extend (write (thEmb S pk nodes hi hc) g R))).Thash pk a (nodes m) = R (a,m) := by
  have h := congrFun (read_write (thEmb S pk nodes hi hc) (node_le_digest S) g R) (a,m)
  rw [thash_apply,ShakeApi.extend_apply _ _ (by simpa only [thBytes,List.length_append,Vector.length_toList,MIdeal.Sha512.payload_length] using hc m)]
  change prefixBytes _ _ = _
  exact (head_eq_prefix (node_le_digest S) _).symm.trans h

/-- An arbitrary collection query has the same answer whenever the two
replacement rows agree on its tweak. This also covers lists beyond the cap. -/
theorem thLocal (g : ShakeApi.RawTable S N) (R T : Bytes 32 × M → S.Node) (a : Bytes 32) (xs : List S.Node)
    (same : ∀ m, R (a,m) = T (a,m)) :
    (ShakeApi.primitives S (ShakeApi.extend (write (thEmb S pk nodes hi hc) g R))).Thash pk a xs =
    (ShakeApi.primitives S (ShakeApi.extend (write (thEmb S pk nodes hi hc) g T))).Thash pk a xs := by
  rw [thash_apply,thash_apply]
  apply congrArg
  by_cases hb : (thBytes S pk a xs).length ≤ N
  · rw [ShakeApi.extend_apply _ _ hb,ShakeApi.extend_apply _ _ hb]
    apply local_at
    rintro ⟨b,m⟩ h
    have e := congrArg (fun x : ShakeApi.Input N => List.ofFn x.2) (located _ h)
    have hm : (thBytes S pk b (nodes m)).length ≤ N := by
      simpa only [thBytes,List.length_append,Vector.length_toList,MIdeal.Sha512.payload_length] using hc m
    change List.ofFn (BList.ofList (thBytes S pk b (nodes m)) hm).2 =
      List.ofFn (BList.ofList (thBytes S pk a xs) hb).2 at e
    rw [BList.ofFn_ofList,BList.ofFn_ofList] at e
    unfold thBytes at e
    have he := (List.append_inj e (by simp)).1
    rw [Vector.toList_inj.mp (List.append_cancel_left he)]
    exact same m
  · simp [ShakeApi.extend,hb]

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.thLeaf
#print axioms Reduction.ShakeXof.thLocal
