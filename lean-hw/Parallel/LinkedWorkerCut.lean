namespace slhdsa.LinkedWorkerCut

/-- A vertex label retains the instruction/block identity above bit zero.
Odd labels are on the unpermitted side of the supplied cut. -/
structure Edge where
  src : Nat
  dst : Nat
  grant : Bool

def preserves (e : Edge) : Bool := e.src%2==1 || e.grant || e.dst%2==0

inductive WithoutGrant (edges : List Edge) : Nat → Nat → Prop where
  | refl (v) : WithoutGrant edges v v
  | step {u v} (p : WithoutGrant edges u v) (e : Edge) (member : e ∈ edges)
      (source : e.src=v) (denied : e.grant=false) : WithoutGrant edges u e.dst

/-- Applies to walks of arbitrary length, including repeated spin/park loops. -/
theorem must_cross (edges : List Edge) (checked : edges.all preserves=true)
    {entry target : Nat} (start : entry%2=0) (finish : target%2=1) :
    ¬ WithoutGrant edges entry target := by
  intro walk
  have invariant {u v} (w : WithoutGrant edges u v) (h : u%2=0) : v%2=0 := by
    induction w with
    | refl => exact h
    | step p e mem src denied ih =>
      have pass := List.all_eq_true.mp checked e mem
      have left : e.src%2=0 := src ▸ ih
      simpa [preserves,left,denied] using pass
  have := invariant walk start
  omega
end slhdsa.LinkedWorkerCut
