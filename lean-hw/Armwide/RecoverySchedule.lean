import Spec.Correctness
import Armwide.RecoveryHashes
import Armwide.WotsRefill
namespace slhdsa.Armwide.Recovery
open WotsRefill Transitions Spec.SHA256

local instance : Inhabited RecoverLane := ⟨⟨[],0,0,0⟩⟩

def banks (n : Nat) (a : Spec.Adrs) (ls : List RecoverLane) : WotsRegisters where
  address _ := a
  chain j := ls[j]!.chain
  counter j := ls[j]!.curT
  digest j := loadDigest n ls[j]!.x

def advance (n : Nat) (st : List Word) (a : Spec.Adrs) (k : Nat) (ls : List RecoverLane) :=
  ls.mapIdx fun j l =>
    let x := registers n st (banks n a ls) ls.length k j
    (⟨storedBytes n x.1 x.2,l.chain,l.curT+k,l.left-k⟩ : RecoverLane)

def fresh (sig : Nat → Spec.Bytes) (d : Nat → Nat) (i : Nat) : RecoverLane :=
  ⟨sig i,i,d i,15-d i⟩

/-- Immediate writes occur before advancing the sorted queue. Surviving
and replenished lanes retain their left-to-right rank during compaction. -/
def retire {α : Type} (write : α → Nat → Spec.Bytes → α) (sig : Nat → Spec.Bytes) (d : Nat → Nat) :
    List RecoverLane → List Nat → α → List RecoverLane × List Nat × α
  | [],q,out => ([],q,out)
  | l::ls,q,out =>
    if l.left=0 then
      let changed := write out l.chain l.x
      match q with
      | [] => retire write sig d ls [] changed
      | c::rest =>
        let (ls',q',out') := retire write sig d ls rest changed
        (fresh sig d c :: ls',q',out')
    else
      let (ls',q',out') := retire write sig d ls q out
      (l::ls',q',out')

theorem retire_table (sig : Nat → Spec.Bytes) (d : Nat → Nat)
    (ls : List RecoverLane) (q : List Nat) (o : Nat → Spec.Bytes) :
    retire setOut sig d ls q o = recoverRetireRefill sig d ls q o := by
  induction ls generalizing q o with
  | nil => rfl
  | cons l ls ih =>
    simp only [retire,recoverRetireRefill,ih]
    split
    · cases q <;> rfl
    · rfl

def run {α : Type} (write : α → Nat → Spec.Bytes → α) (n : Nat) (st : List Word)
    (a : Spec.Adrs) (sig : Nat → Spec.Bytes) (d : Nat → Nat)
    (ls : List RecoverLane) (q : List Nat) (out : α) : Nat → α
  | 0 => out
  | fuel+1 =>
    if ls.length=4 then
      let stepped := advance n st a (minLeft ls) ls
      let (active,more,result) := retire write sig d stepped q out
      run write n st a sig d active more result fuel
    else if ls.length>0 then
      let stepped := advance n st a 1 ls
      let (active,_,result) := retire write sig d stepped [] out
      run write n st a sig d active q result fuel
    else out

def Good (n count : Nat) (l : RecoverLane) :=
  l.chain<count ∧ l.x.length=n ∧ 0<l.left ∧ l.left≤15

private theorem advanced_eq (p : Spec.Params) [Fact (p.family=.sha2)] (valid : p.Valid)
    (pk : Spec.Bytes) (pkLength : pk.length=p.n) (a : Spec.Adrs) (ls : List RecoverLane)
    (count k : Nat) (cap : count≤67) (width : ls.length≤4)
    (good : ∀ l∈ls, Good p.n count l) (positive : 0<k) (limit : k≤15) (tailStep : ls.length<4 → k=1) :
    advance p.n (seedState p.n pk) a k ls = ls.map (fun l =>
      (⟨Spec.chain p l.x l.curT k pk {a with word2:=l.chain},l.chain,l.curT+k,l.left-k⟩ : RecoverLane)) := by
  apply List.ext_getElem (by simp [advance])
  intro j hj _
  have live : j<ls.length := by simpa [advance] using hj
  have g := good ls[j] (List.getElem_mem ..)
  have atLane : ls[j]! = ls[j] := by simp [live]
  have registersEq := registers_fips p valid pk pkLength (banks p.n a ls) ls.length k j width live positive limit tailStep
    (by change ls[j]!.chain<65536; rw [atLane];exact Nat.lt_trans g.1 (by omega))
  unfold content banks at registersEq
  simp only [atLane,load_content p.n valid.n_cases _ g.2.1] at registersEq
  simp only [advance,List.getElem_mapIdx,List.getElem_map,stored_eq p.n valid.n_cases]
  exact congrArg (fun x => RecoverLane.mk x ls[j].chain (ls[j].curT+k) (ls[j].left-k)) registersEq

private theorem min_in_bounds {ls : List RecoverLane} (four : ls.length=4)
    {n count} (good : ∀ l∈ls, Good n count l) : 0<minLeft ls ∧ minLeft ls≤15 := by
  obtain ⟨l,t,rfl⟩ := List.exists_cons_of_ne_nil (show ls≠[] by intro eq;simp [eq] at four)
  have lo {xs : List RecoverLane} (positive : ∀ l∈xs, 0<l.left) (ne : xs≠[]) : 0<minLeft xs := by
    induction xs with
    | nil => contradiction
    | cons h t ih =>
      cases t with
      | nil => exact positive h (by simp)
      | cons x r =>
        exact Nat.lt_min.mpr ⟨positive h (by simp),ih (fun i hi => positive i (by simp [hi])) (by simp)⟩
  refine ⟨lo (fun l hl => (good l hl).2.2.1) (by simp),?_⟩
  have upper := (good l (by simp)).2.2.2
  cases t with
  | nil => exact upper
  | cons h t => exact le_trans (Nat.min_le_left ..) upper

private theorem retire_good {α} (write : α → Nat → Spec.Bytes → α) (sig : Nat → Spec.Bytes) (d : Nat → Nat)
    (n count : Nat) (sizes : ∀ c<count, (sig c).length=n)
    (ls : List RecoverLane) (q : List Nat) (o : α)
    (live : ∀ l∈ls, l.chain<count ∧ l.x.length=n ∧ l.left≤15)
    (waits : ∀ c∈q, c<count ∧ d c<15) :
    let result := retire write sig d ls q o
    result.1.length≤ls.length ∧ (∀ l∈result.1, Good n count l) ∧
      (∀ c∈result.2.1, c<count ∧ d c<15) := by
  induction ls generalizing q o with
  | nil => exact ⟨by simp [retire],by simp [retire],waits⟩
  | cons l ls ih =>
    have later := fun x hx => live x (List.mem_cons_of_mem l hx)
    have gl := live l List.mem_cons_self
    unfold retire
    split
    · cases q with
      | nil =>
        obtain ⟨sz,rows,tail⟩ := ih [] (write o l.chain l.x) later waits
        exact ⟨by simp;omega,rows,tail⟩
      | cons c rest =>
        obtain ⟨sz,rows,tail⟩ := ih rest (write o l.chain l.x) later (fun x h => waits x (List.mem_cons_of_mem c h))
        have hc := waits c List.mem_cons_self
        exact ⟨by simpa using sz,by
          intro x hx;rcases List.mem_cons.mp hx with rfl|mem
          · exact ⟨hc.1,sizes c hc.1,by dsimp [fresh];omega,by dsimp [fresh];omega⟩
          · exact rows x mem,tail⟩
    · obtain ⟨sz,rows,tail⟩ := ih q o later waits
      exact ⟨by simpa using sz,by
        intro x hx;rcases List.mem_cons.mp hx with rfl|mem
        · exact ⟨gl.1,gl.2.1,by omega,gl.2.2⟩
        · exact rows x mem,tail⟩


/-- Representation change for all writes in a physical iteration. -/
private theorem retire_sim {α : Type} (write : α → Nat → Spec.Bytes → α) (repr : (Nat → Spec.Bytes) → α)
    (n count : Nat) (writes : ∀ o c x, c<count → x.length=n → write (repr o) c x=repr (setOut o c x))
    (sig : Nat → Spec.Bytes) (d : Nat → Nat) (ls : List RecoverLane) (q : List Nat) (o : Nat → Spec.Bytes)
    (ready : ∀ l∈ls, l.chain<count ∧ l.x.length=n) :
    retire write sig d ls q (repr o) = let r := retire setOut sig d ls q o; (r.1,r.2.1,repr r.2.2) := by
  induction ls generalizing q o with
  | nil => rfl
  | cons l ls ih =>
    have gl := ready l List.mem_cons_self
    have tail := fun x hx => ready x (List.mem_cons_of_mem l hx)
    simp only [retire]
    split
    · rw [writes _ _ _ gl.1 gl.2]
      cases q with
      | nil => exact ih _ _ tail
      | cons c q => simp only;rw [ih q _ tail]
    · rw [ih _ _ tail]

private theorem no_refill {α} (write : α → Nat → Spec.Bytes → α) (sig : Nat → Spec.Bytes) (d : Nat → Nat)
    (ls : List RecoverLane) (o : α) :
    retire write sig d ls [] o=retire write (fun _ => []) (fun _ => 0) ls [] o := by
  induction ls generalizing o with
  | nil => rfl
  | cons l ls ih => simp only [retire];split <;> rw [ih]

theorem run_sim {α} (write : α → Nat → Spec.Bytes → α) (repr : (Nat → Spec.Bytes) → α)
    (p : Spec.Params) [Fact (p.family=.sha2)] (valid : p.Valid) (pk : Spec.Bytes) (pkLength : pk.length=p.n)
    (a : Spec.Adrs) (sig : Nat → Spec.Bytes) (d : Nat → Nat) (count : Nat) (cap : count≤67)
    (writes : ∀ o c x, c<count → x.length=p.n → write (repr o) c x=repr (setOut o c x))
    (sizes : ∀ c<count, (sig c).length=p.n) (ls : List RecoverLane) (q : List Nat) (o : Nat → Spec.Bytes)
    (fuel : Nat) (width : ls.length≤4) (live : ∀ l∈ls, Good p.n count l) (waits : ∀ c∈q, c<count ∧ d c<15) :
    run write p.n (seedState p.n pk) a sig d ls q (repr o) fuel = repr (recoverRun p pk a sig d ls q o fuel) := by
  induction fuel generalizing ls q o with
  | zero => rfl
  | succ k ih =>
    unfold run recoverRun
    by_cases four : ls.length=4
    · simp only [four,↓reduceIte]
      obtain ⟨pos,stop⟩ := min_in_bounds four live
      let stepped := ls.map fun l => (⟨Spec.chain p l.x l.curT (minLeft ls) pk {a with word2:=l.chain},
        l.chain,l.curT+minLeft ls,l.left-minLeft ls⟩ : RecoverLane)
      have ready : ∀ l∈stepped, l.chain<count ∧ l.x.length=p.n ∧ l.left≤15 := by
        intro l mem
        obtain ⟨old,ho,rfl⟩ := List.mem_map.mp (show l∈ls.map _ from mem)
        have h := live old ho
        exact ⟨h.1,Spec.chain_length p valid _ h.2.1 ..,by dsimp;have := h.2.2.2;omega⟩
      have result := retire_good setOut sig d p.n count sizes stepped q o ready waits
      rw [advanced_eq p valid pk pkLength a ls count (minLeft ls) cap width live pos stop (by omega)]
      change run write _ _ _ _ _ _ _ _ k = _
      rw [retire_sim write repr p.n count writes sig d stepped q o (fun x h => ⟨(ready x h).1,(ready x h).2.1⟩)]
      unfold recoverStep4
      rw [← retire_table sig d stepped q o]
      exact ih _ _ _ (result.1.trans (by simp [stepped];omega)) result.2.1 result.2.2
    · simp only [four,↓reduceIte]
      by_cases any : ls.length>0
      · simp only [any,↓reduceIte]
        let stepped := ls.map fun l => (⟨Spec.F p pk {a with word2:=l.chain,word3:=l.curT} l.x,
          l.chain,l.curT+1,l.left-1⟩ : RecoverLane)
        have ready : ∀ l∈stepped, l.chain<count ∧ l.x.length=p.n ∧ l.left≤15 := by
          intro l mem
          obtain ⟨old,ho,rfl⟩ := List.mem_map.mp (show l∈ls.map _ from mem)
          have h := live old ho
          exact ⟨h.1,Spec.F_length p valid ..,by dsimp;have := h.2.2.2;omega⟩
        have result := retire_good setOut sig d p.n count sizes stepped [] o ready (by simp)
        have one : advance p.n (seedState p.n pk) a 1 ls=stepped := by
          rw [advanced_eq p valid pk pkLength a ls count 1 cap width live (by decide) (by decide) (by simp)]
          simp [stepped,Spec.chain]
        rw [one,retire_sim write repr p.n count writes sig d stepped [] o (fun x h => ⟨(ready x h).1,(ready x h).2.1⟩)]
        unfold recoverStepTail
        dsimp only
        rw [← retire_table (fun _ => []) (fun _ => 0) stepped [] o,← no_refill setOut sig d stepped o]
        generalize eqn : retire setOut sig d stepped [] o = triple at result ⊢
        obtain ⟨al,ql,ol⟩ := triple
        dsimp only at result ⊢
        exact ih _ _ _ (result.1.trans (by simp [stepped];omega)) result.2.1 waits
      · simp [any]

end slhdsa.Armwide.Recovery
