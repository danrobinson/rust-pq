import Spec.ArmKeygen

namespace Spec.ArmPublicKeygen
open ArmKeygen

/-- Map the two private subtree calling conventions into the checked XMSS
contract. Only volatile argument registers are rearranged. `subtree` checks
all input words, the output region, index, address and height before it returns. -/
def rootCall (c : Config) (s : State) : Option State :=
  let args := match c.seed with
    | .shake => put (put (put s 1 (g s 2)) 2 (g s 3)) 3 (g s 1)
    | _ => (List.range 5).foldl (fun t r => put t r (g s (r+1))) (put s 8 (g s 0))
  subtree c args

/-- The two buffers returned by a successful machine execution, interpreted at
arbitrary values of the four seed/root inputs to the symbolic memory model. -/
theorem keyBytes {p : Params} {c : Config} {path : List (Nat × Nat)}
    (checked : runWith rootCall c path = some (secret p.n,publicKey p.n))
    (sources : Nat → Bytes) (size : ∀ i<4, (sources i).length=p.n)
    (aligned : p.n%4=0) (small : p.n≤32)
    (tree : sources 3 = Spec.xmssNode p (sources 0) 0 p.hp (sources 2) {Adrs.zero with layer:=p.d-1}) :
    (runWith rootCall c path).map (fun keys => (ArmKeygen.bytes (interpret sources) keys.1,
      ArmKeygen.bytes (interpret sources) keys.2)) = some (Spec.slhKeygenInternal p (sources 0) (sources 1) (sources 2)) := by
  have blockEq (i) (hi : i<4) := bytes_block (size i hi) aligned small
  have append (l r : Cells) : ArmKeygen.bytes (interpret sources) (l ++ r) =
      ArmKeygen.bytes (interpret sources) l ++ ArmKeygen.bytes (interpret sources) r := List.flatMap_append
  rw [checked]
  simp only [Option.map_some,secret,publicKey,append,blockEq 0 (by decide),blockEq 1 (by decide),blockEq 2 (by decide),
    blockEq 3 (by decide),tree,slhKeygenInternal]

/-- Choose the FIPS result for the local XMSS call. Every other returned byte
comes from running the public driver's memory instructions. -/
def inputs (p : Params) (sk prf pk : Bytes) : Nat → Bytes
  | 0 => sk
  | 1 => prf
  | 2 => pk
  | _ => xmssNode p sk 0 p.hp pk {Adrs.zero with layer:=p.d-1}

def execute (p : Params) (c : Config) (path : List (Nat × Nat)) (sk prf pk : Bytes) :=
  let v := interpret (inputs p sk prf pk)
  (runWith rootCall c path).map fun keys => (ArmKeygen.bytes v keys.1,ArmKeygen.bytes v keys.2)

theorem execute_fips (p : Params) (valid : p.Valid) (c : Config) (path : List (Nat × Nat))
    (checked : runWith rootCall c path = some (secret p.n,publicKey p.n))
    (aligned : p.n%4=0) (small : p.n≤32) (sk prf pk : Bytes)
    (hs : sk.length=p.n) (hr : prf.length=p.n) (hp : pk.length=p.n) :
    execute p c path sk prf pk=some (slhKeygenInternal p sk prf pk) := by
  apply keyBytes checked (inputs p sk prf pk) _ aligned small rfl
  intro i hi
  interval_cases i <;> first | exact hs | exact hr | exact hp | apply xmssNode_length p valid

end Spec.ArmPublicKeygen
