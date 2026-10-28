import InitECandidate.Solver.Input.CurrentHash.RequestListRound
import InitECandidate.Solver.Input.CounterFlow

namespace InitECandidate.Solver.Input.CurrentHash.RequestList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem branch_evaluate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind selected : Kind)
    (category : source.locals.lookup (ofString "kind")=some (.val (.word (BitVec.ofNat 64 kind.tag)))) :
    evaluateHOLFiniteState source (branch selected)=
      if kind=selected then evaluateHOLFiniteState source (.call (some (none,none)) kind.record.name arguments) else (none,source) := by
  have read : eval source (branchTest selected)=some (.val (.word (if kind=selected then 1#64 else 0#64))) := by
    simp [eval,evalHOLExact,toExact,branchTest,localVar,category,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,tag_injective]
  simp only [eval] at read
  rw [branch,evaluateHOLFiniteState_ite,read]
  by_cases same : kind=selected
  · subst selected; simp
  · simp [same,evaluateHOLFiniteState_skip]

def branchPrice (kind selected : Kind) := if kind=selected then kind.record.price+1 else 0

theorem branch_summary (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind selected : Kind) (p roots out : BitVec 64) (n index : Nat)
    (actual : RoundState source kind p roots out n index)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (branch selected)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤branchPrice kind selected ∧ (result=none → RoundState post kind p roots out n index) := by
  rw [branch_evaluate source kind selected actual.category] at run
  by_cases same : kind=selected
  · rw [if_pos same] at run
    simpa only [branchPrice,if_pos same] using call_summary source post kind p roots out n index actual result run notTimeout
  · rw [if_neg same] at run
    have endpoint : post=source := (congrArg Prod.snd run).symm
    rw [endpoint]
    exact ⟨by simp [branchPrice,same],by intro normal; exact actual⟩

def chainPrice (kind : Kind) (branches : List Kind) := (branches.map (branchPrice kind)).sum

theorem chain_cost (branches : List Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out : BitVec 64) (n index : Nat)
    (actual : RoundState source kind p roots out n index)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (chain branches)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤chainPrice kind branches := by
  induction branches generalizing source post result with
  | nil=>
    have same := QuietClock.assign source.code (ofString "i") (.op .add [localVar "i",.const 1#64]) source rfl
    change (evaluateHOLFiniteState source increment).2.clock=source.clock at same
    change evaluateHOLFiniteState source increment=(result,post) at run
    rw [run] at same
    change post.clock=source.clock at same
    simp [chainPrice,same]
  | cons selected rest ih=>
    change evaluateHOLFiniteState source (.seq (branch selected) (chain rest))=(result,post) at run
    have price := ClockCost.sequence_terminating source post _ _ (branchPrice kind selected) (chainPrice kind rest)
      (by intro actualResult target evaluated notTimeout
          exact (branch_summary source target kind selected p roots out n index actual actualResult evaluated notTimeout).1)
      (by intro middle normal actualResult target evaluated notTimeout
          have next := (branch_summary source middle kind selected p roots out n index actual none normal (by simp)).2 rfl
          exact ih middle target next actualResult evaluated notTimeout)
      result run notTimeout
    exact price

theorem branch_local (key : MlS) (kind : Kind) : LocalPrefix key (branch kind) := .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip

theorem chain_local (key : MlS) (branches : List Kind) (different : key≠ofString "i") : LocalPrefix key (chain branches) := by
  induction branches with
  | nil=>exact .assign _ _ different
  | cons selected rest ih=>exact .seq (branch_local key selected) ih

theorem chain_advance (branches : List Kind) : CounterFlow.Advances (ofString "i") 1 (chain branches) := by
  induction branches with
  | nil=>exact CounterFlow.increment (ofString "i")
  | cons selected rest ih=>exact CounterFlow.sequence (ofString "i") _ _ 0 1 (CounterFlow.preserved (ofString "i") _ (branch_local (ofString "i") selected)) ih

/-- All five literal tests execute, but exactly one original record hash
is charged for the actual kind; inactive branches have zero source cost. -/
theorem selected_price (kind : Kind) : chainPrice kind kinds=kind.record.price+1 := by cases kind <;> decide

end InitECandidate.Solver.Input.CurrentHash.RequestList

#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.branch_evaluate
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.branch_summary
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.chain_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.chain_local
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.chain_advance
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.selected_price
