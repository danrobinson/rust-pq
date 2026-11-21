import Ideal.Realize.WotsCount1
open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash
namespace Ideal.Realize.Wots
open Reduction Reduction.Open WotsFinal
variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  (pkSeedDist : ProbComp prims.PkSeed)

theorem t2 (my : ProbComp (SecretTable vp prims)) (A : Forger vp prims optRand pkSeedDist) (kf : ℕ) :
    IsQueryBoundP (WotsGame.simChoose (Lazy.bWotsWith my A) (wotsInsts vp) (udStart pkSeedDist kf)
      (udChainHash pkSeedDist) (udColl pkSeedDist) : OracleComp (udSpecC prims.AdrsKey prims.Y) _) isColl (wotsQc vp + (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))) := by
  apply qb_simChoose (T := prims.AdrsKey) (Y := prims.Y) (K := prims.AdrsKey) isColl isColl_inl
  intro z hz
  have h := simChoose_bWotsWith_count (univO (sampG prims.Y prims.AdrsKey) (cG isColl)) id
    isColl (univG_hO isColl isColl_inl) (udStart pkSeedDist kf) (udChainHash pkSeedDist)
    (udColl pkSeedDist) 1 (vp.params.len * (vp.params.w - 1)) (udColl_qb pkSeedDist)
    (signProg_qb isColl _ _ (fun b => b) 1 (vp.params.w - 1)
      (fun ca b => udStart_qb pkSeedDist kf ca b) (fun a y => udColl_qb pkSeedDist _ _)
      (fun b hb => by omega)) my A 0 z hz
  simpa using h

theorem t3 (A : Forger vp prims optRand pkSeedDist) :
    IsQueryBoundP (rUd pkSeedDist (Lazy.bWotsS A)).pick isColl
      (wotsQc vp + (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1))) := by
  have e : (rUd pkSeedDist (Lazy.bWotsS A)).pick =
    ((monadLift ($ᵗ (Fin (vp.params.w - 3 + 1)) : ProbComp (Fin (vp.params.w - 3 + 1))) :
      OracleComp (udSpecC prims.AdrsKey prims.Y) (Fin (vp.params.w - 3 + 1))) >>= fun k =>
        WotsGame.simChoose (Lazy.bWotsWith (Lazy.sparseOn vp prims (forsSkIdx vp)) A) (wotsInsts vp) (udStart pkSeedDist k.val)
      (udChainHash pkSeedDist) (udColl pkSeedDist)) := rfl
  rw [e]
  exact (isQueryBoundP_bind (n := 0)
    (qb_lift_isColl _ isColl (by rintro (_ | _ | _) h <;> simp_all [isColl])) fun kf _ =>
      t2 pkSeedDist _ A kf.val).mono (by omega)
end Ideal.Realize.Wots
