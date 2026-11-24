import Integration.SlhDsaCompressionCost
import MIdeal.Itsr512

namespace Reduction.Compression
open MLink Ideal SLHDSA SLHDSA.Concrete OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open VCVio.Algorithms.Sha2

private theorem seqCost {C D : Type} {f : (Input → Output) → C} {k : C → (Input → Output) → D} {n m : ℕ}
    (hf : EvalCost (fun H => (pure (f H) : ProbComp C)) n)
    (hk : ∀ c, EvalCost (fun H => (pure (k c H) : ProbComp D)) m) :
    EvalCost (fun H => (pure (k (f H) H) : ProbComp D)) (n+m) := by
  simpa only [pure_bind] using EvalCost.bind hf hk

private theorem finishCost {C D : Type} {f : (Input → Output) → C} {n : ℕ}
    (hf : EvalCost (fun H => (pure (f H) : ProbComp C)) n) (k : C → D) :
    EvalCost (fun H => (pure (k (f H)) : ProbComp D)) n := by
  simpa only [map_pure] using hf.map k

def msgPrfCalls (S : Sha2Set) (ml : ℕ) :=
  if S.vp.params.n = 16 then (ml+24)/64+4 else (ml+S.vp.params.n+16)/128+4

private theorem hmac256_cost (k r : Bytes 16) (m : List Byte) :
    EvalCost (fun H => (pure ((primsG (liftC (tablesOf H).1)).PRFmsg k r m) : ProbComp (Bytes 16))) ((m.length+24)/64+4) := by
  have inner := fold256_cost IV128 (ikey k :: iblocks r m)
  have outer (s : St) := finishCost (fold256_cost IV128 [okey k,oblock s]) out16
  simp only [List.length_cons, List.length_nil] at outer
  have h := seqCost inner outer
  simp only [msgPrf_shape]
  simpa only [mdFold, List.foldl_cons, List.foldl_nil, List.length_cons, List.length_nil, iblocks_length,
    Nat.add_assoc] using h

theorem msgPrf_cost (S : Sha2Set) (k r : S.Node) (m : List Byte) :
    EvalCost (fun H => (pure ((tablePrimitives (tablesOf H) S.vp.params).PRFmsg k r m) : ProbComp S.Node))
      (msgPrfCalls S m.length) := by
  by_cases hw : S.vp.params.n = 16
  · have narrow (g : CompressionTables) (k r : Bytes 16) :
        sha2PRFmsgMixed (liftC g.1) (lift512 g.2) k r m = (primsG (liftC g.1)).PRFmsg k r m := by
      change _ = sha2PRFmsgG (liftC g.1) k r m
      simp only [sha2PRFmsgMixed,sha2PRFmsgG,ite_true]
    have hc (k r : Bytes 16) : EvalCost (fun H => (pure (sha2PRFmsgMixed (liftC (tablesOf H).1)
        (lift512 (tablesOf H).2) k r m) : ProbComp (Bytes 16))) ((m.length+24)/64+4) := by
      simpa only [narrow] using hmac256_cost k r m
    cases S <;> first | exact hc k r | (exfalso; revert hw; decide)
  · have inner := fold512_cost MIdeal.Sha512.initial (MIdeal.Sha512.ikey S k :: MIdeal.Sha512.iblocks S r m)
    have outer (s : Chain512) := finishCost (fold512_cost MIdeal.Sha512.initial [MIdeal.Sha512.okey S k,MIdeal.Sha512.oblock s])
      (fun st => byteArrayPrefixOrZero (stateBytes64 st.toArray) S.vp.params.n)
    simp only [List.length_cons, List.length_nil] at outer
    have h := seqCost inner outer
    simp only [msgPrfCalls,ite_eq_right hw, MIdeal.Sha512.msgPrf_shape S _ hw]
    simpa only [mdFold,List.foldl_cons,List.foldl_nil,List.length_cons,List.length_nil,MIdeal.Sha512.iblocks_length,Nat.add_assoc] using h

def hmsgCalls (S : Sha2Set) (ml : ℕ) :=
  match S with
  | .s128s => (ml+56)/64+3
  | .s128f => (ml+56)/64+5
  | _ => (ml+3*S.vp.params.n+16)/128+3

private theorem hmsg128s_cost (r pk root : Bytes 16) (m : List Byte) :
    EvalCost (fun H => (pure ((tablePrimitives (tablesOf H) Sha2Set.s128s.vp.params).Hmsg r pk root m) : ProbComp (Bytes 30)))
      ((m.length+56)/64+3) := by
  have h (g : CompressionTables) : (tablePrimitives g Sha2Set.s128s.vp.params).Hmsg r pk root m =
      (primsG (liftC g.1)).Hmsg r pk root m := by
    change sha2HmsgMixed (liftC g.1) (lift512 g.2) Sha2Set.s128s.vp.params r pk root m =
      sha2HmsgG (liftC g.1) Link.vp.params r pk root m
    simp only [sha2HmsgMixed,sha2HmsgG, show Sha2Set.s128s.vp.params.n = 16 from rfl,
      show Link.vp.params.n = 16 from rfl, ite_true]
    rfl
  have outer (s : St) := finishCost (fold256_cost IV128 (oblocksH r pk s)) dig30
  simp only [oblocksH_length] at outer
  have ev := seqCost (fold256_cost IV128 (iblocksH r pk root m)) outer
  simp only [h,hmsg_shape]
  simpa only [iblocksH_length, Nat.add_assoc] using ev

private theorem hmsg128f_cost (r pk root : Bytes 16) (m : List Byte) :
    EvalCost (fun H => (pure ((tablePrimitives (tablesOf H) Sha2Set.s128f.vp.params).Hmsg r pk root m) : ProbComp (Bytes 34)))
      ((m.length+56)/64+5) := by
  have ctr (s : St) (i : UInt32) := fold256_cost IV128 (MIdeal.Hmsg.counterBlocks r pk s i)
  simp only [MIdeal.Hmsg.counter_length] at ctr
  have outer (s : St) := seqCost (ctr s 0) (fun a => finishCost (ctr s 1) (fun b =>
      byteArrayPrefixOrZero ((digestBytes a ++ digestBytes b).extract 0 34) 34))
  have ev := seqCost (fold256_cost IV128 (iblocksH r pk root m)) outer
  simp only [MIdeal.Hmsg.hmsg_128f]
  simpa only [iblocksH_length, Nat.add_assoc] using ev

theorem hmsg_cost (S : Sha2Set) (r pk root : S.Node) (m : List Byte) :
    EvalCost (fun H => (pure ((tablePrimitives (tablesOf H) S.vp.params).Hmsg r pk root m) : ProbComp (Bytes S.vp.params.m)))
      (hmsgCalls S m.length) := by
  by_cases hw : S.vp.params.n = 16
  · cases S <;> first | exact hmsg128s_cost r pk root m | exact hmsg128f_cost r pk root m | (exfalso; revert hw; decide)
  · have h (s : Chain512) := finishCost (fold512_cost MIdeal.Sha512.initial (MIdeal.Hmsg.outer S r pk s))
      (fun v => byteArrayPrefixOrZero ((stateBytes64 v.toArray).extract 0 S.vp.params.m) S.vp.params.m)
    simp only [MIdeal.Hmsg.outer_length S hw] at h
    have ev := seqCost (fold512_cost MIdeal.Sha512.initial (MIdeal.Hmsg.inner S r pk root m)) h
    have len := MIdeal.Hmsg.ib_length S (r,pk,root,m)
    change (MIdeal.Hmsg.inner S r pk root m).length = (m.length + 3*S.vp.params.n+16)/128+1 at len
    have calls : hmsgCalls S m.length = (m.length + 3*S.vp.params.n+16)/128+3 := by
      cases S <;> first | rfl | (exfalso; revert hw; decide)
    simp only [MIdeal.Hmsg.hmsg_wide S _ hw,calls]
    simpa only [len,Nat.add_assoc] using ev
end Reduction.Compression

#print axioms Reduction.Compression.msgPrf_cost
#print axioms Reduction.Compression.hmsg_cost
