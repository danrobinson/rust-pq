import Ideal.Realize.Port
import Reduction.Open.MsgV
open OracleComp OracleSpec
namespace Ideal.Realize.Msg
open Reduction Reduction.Lazy
variable {ι κ : Type} {G : OracleSpec ι} {H : OracleSpec κ} {D V α : Type} [DecidableEq D]
example (n : ℕ) (s : List (D × V)) : (lazyImplR (gspec := G) (hspec := H) (V := V) (Sum.inl n)).run s = (fun a => (a, s)) <$> (liftM ((RSpec G Unit V H).query (Sum.inl n)) : OracleComp (RSpec G Unit V H) _) := by
  simp [lazyImplR]
example (n : ℕ) (s : List (D × V)) : (lazyImplR (gspec := G) (hspec := H) (V := V) (Sum.inl n)).run s = (fun a => (a, s)) <$> (liftM ((RSpec G Unit V H).query (Sum.inl n)) : OracleComp (RSpec G Unit V H) _) := by
  rfl
example (n : ℕ) (s : List (D × V)) : (lazyImplR (gspec := G) (hspec := H) (V := V) (Sum.inl n)).run s = (fun a => (a, s)) <$> (liftM ((RSpec G Unit V H).query (Sum.inl n)) : OracleComp (RSpec G Unit V H) _) := by
  show (monadLift (liftM ((RSpec G Unit V H).query (Sum.inl n)) : OracleComp (RSpec G Unit V H) _) : StateT _ _ _).run s = _
  rw [StateT.run_monadLift, map_eq_bind_pure_comp]; rfl
end Ideal.Realize.Msg
