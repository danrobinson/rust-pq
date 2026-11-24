import Integration.SlhDsaShakeSignatureItsr
import Integration.SlhDsaSetItsr

namespace Reduction.ShakeAdaptive
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum QMsg QItsr KeyedHash
open scoped ComplexOrder Kronecker ENNReal
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeApi.primitives ShakeSecurity.primitives
variable (S : Sha2Set) (N : ℕ) {E : Type} [Fintype E] [DecidableEq E]
  (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
  (F : PortForger (ShakeApi.Input N) (Bytes S.vp.params.m) E)
local notation "A" => fun H => qPureBytesToInternal (ShakeApi.rawForger S N rand seeds F H)
local notation "P" => fun H => ShakeApi.primitives S (ShakeApi.extend H)

theorem target_count (s : ℕ) (hs : ∀ pk, CountBound isSign (F.main pk) s) (H : ShakeApi.RawTable S N) :
    CountBound (QC (WS (ShakeApi.Input N) (Bytes S.vp.params.m) E) isR) (qbItsrL (A H)) s :=
  cb_qLazyRun _ _ (cb_qItsrOpen (P H) _ fun pk =>
    cb_qPureBytesToInternal _ (fun pkb => cb_compileQ H (F.main pkb) (hs pkb)) pk)

theorem target_support (c : Caps) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (H : ShakeApi.RawTable S N) :
    AllQueries (QG (WS (ShakeApi.Input N) (Bytes S.vp.params.m) E) (Gfin (Ptgt (P H) c.ml)))
        (fun r : S.Node × ItsrIn (P H) ↦ r.2.2.2.length ≤ c.ml) (qbItsrL (A H)) := by
  have hQ (pk) : AllQueries (QG _ (Gint c.ml)) (fun z : List SLHDSA.Byte × _ ↦ z.1.length ≤ c.ml) ((A H).main pk) :=
    allQ_and (allQ_qPureBytesToInternal c.ml _ (fun pkb => allQ_compileQ c H _ (hc pkb)) pk)
      (out_qPureBytesToInternal _ c.ml (fun pkb => allQ_out_simulateQ (compileImplQ H) (hc pkb)) pk)
  have ho := allQ_qItsrOpen (P H) c.ml (A H) hQ
  exact allQ_and (allQ_qLazyRun _ (Ptgt (P H) c.ml) _ (allQ_mono (fun _ h => h) (fun _ _ => trivial) ho))
    (out_qLazyRun _ _ ho)

/-- Compile the actual open signature reduction into an interactive machine
which sees the shared raw XOF and receives the salt only after requesting a target. -/
theorem interactive_machine (q s : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) s) :
    ∃ (L : LocalSig.{1,0}) (B : QReg) (I : L.Interp) (ρ : SubState B)
      (x : IAdv L (qromSpec (ShakeApi.Input N) (Bytes S.vp.params.m))
        (S.Node × S.Node × List SLHDSA.Byte) S.Node (fun _ ↦ Option (ShakeSingle.Query S)) s B),
      IAdv.IsQueryBound s x (fun _ ↦ q + itsrHashes S.vp s) ∧
      ∀ (H : ShakeApi.RawTable S N) (Rs : Fin s → S.Node)
        (Ev : Option (ShakeSingle.Query S) × List (S.Node × S.Node × List SLHDSA.Byte) → Prop) [DecidablePred Ev],
        qprob I H (IAdv.flat (rndCh Rs) (IAdv.stop (L := L) (spec := qromSpec (ShakeApi.Input N) (Bytes S.vp.params.m))) s [] x)
          ρ (fun p ↦ Ev p.2) =
          qWeight (fun z ↦ Ev (some z.1, z.2)) (close (rndImpl Rs) (qbItsrL (A H)) []) F.ρ₀ := by
  let base : ShakeApi.Xof S := fun _ => default
  obtain ⟨ρ,hρ⟩ := exists_subState F.ρ₀ F.posSemidef F.trace_eq_one
  have hP := PUE.map (some : ShakeSingle.Query S → Option (ShakeSingle.Query S))
    (ShakeApi.pue_itsrMach S N rand seeds F base q s hq hs)
  obtain ⟨x,hx,hxe⟩ := PUE.exists_iadv_qprob (Req := S.Node × S.Node × List SLHDSA.Byte) (Resp := S.Node)
    (α := Option (ShakeSingle.Query S)) hP s
  refine ⟨LocalSig.instruments.{0},progReg (ShakeApi.Input N) (Bytes S.vp.params.m) E,LocalSig.Interp.instruments,ρ,x,hx,?_⟩
  intro H Rs Ev inst
  have eq := ShakeApi.itsrMach_oracle S N rand seeds F base H
  have cg : CountBound (isGameQ (Req := S.Node × S.Node × List SLHDSA.Byte) (Resp := S.Node))
      (ShakeApi.itsrMach S N rand seeds F base H) s := by
    rw [eq]
    exact cb_congr (fun t ↦ by rcases t with _ | _ | _ <;> simp [QC,isR,isGameQ]) (target_count S N rand seeds F s hs H)
  have hc := (countBound_iff_wCount _ _ _).2 (WCount.map ((countBound_iff_wCount _ _ _).1 cg) some)
  have he := hxe (List (S.Node × S.Node × List SLHDSA.Byte)) (rndCh Rs) [] Ev H ρ hc
  refine he.trans ?_
  rw [hρ,close_map_out,qWeight_map,eq]
  rfl

end Reduction.ShakeAdaptive
#print axioms Reduction.ShakeAdaptive.interactive_machine
