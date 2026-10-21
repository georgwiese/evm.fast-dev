import InitECandidate.Solver.Input.RequestListHashRound
import InitECandidate.Solver.Input.CounterFlow

namespace InitECandidate.Solver.Input.RequestListHash
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

theorem branch_summary (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind selected : Kind) (p roots out cursor stp accel chunk zeros : BitVec 64) (n index : Nat)
    (active : index<n) (actual : RoundState source kind p roots out cursor stp accel chunk zeros n index) (geometry : Geometry kind p roots cursor n)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (branch selected)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤branchPrice kind selected ∧ (result=none → RoundState post kind p roots out cursor stp accel chunk zeros n index) := by
  rw [branch_evaluate source kind selected actual.category] at run
  by_cases same : kind=selected
  · rw [if_pos same] at run
    simpa only [branchPrice,if_pos same] using call_summary source post kind p roots out cursor stp accel chunk zeros n index active actual geometry result run notTimeout
  · rw [if_neg same] at run
    have endpoint : post=source := (congrArg Prod.snd run).symm
    rw [endpoint]
    exact ⟨by simp [branchPrice,same],by intro normal; exact actual⟩

def chainPrice (kind : Kind) (branches : List Kind) := (branches.map (branchPrice kind)).sum

theorem chain_cost (branches : List Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out cursor stp accel chunk zeros : BitVec 64) (n index : Nat)
    (active : index<n) (actual : RoundState source kind p roots out cursor stp accel chunk zeros n index) (geometry : Geometry kind p roots cursor n)
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
          exact (branch_summary source target kind selected p roots out cursor stp accel chunk zeros n index active actual geometry actualResult evaluated notTimeout).1)
      (by intro middle normal actualResult target evaluated notTimeout
          have next := (branch_summary source middle kind selected p roots out cursor stp accel chunk zeros n index active actual geometry none normal (by simp)).2 rfl
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

theorem chain_globals (branches : List Kind) (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code (chain branches) := by
  induction branches with
  | nil=>exact GlobalEffects.assign key code _ _
  | cons selected rest ih=>
    exact GlobalEffects.sequence key code _ _
      (GlobalEffects.conditional key code _ _ _
        (GlobalEffects.call_body key code (some none) selected.record.name arguments selected.record.formals selected.record.body .one
          (FixedHash.original_code selected.record code installed) (FixedHash.globals selected.record key code installed different))
        (GlobalEffects.skip key code)) ih

theorem chain_normal_heap (branches : List Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out cursor stp accel chunk zeros : BitVec 64) (n index : Nat)
    (active : index<n) (actual : RoundState source kind p roots out cursor stp accel chunk zeros n index) (geometry : Geometry kind p roots cursor n)
    (run : evaluateHOLFiniteState source (chain branches)=(none,post)) : post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  induction branches generalizing source post with
  | nil=>
    have frame := GlobalEffects.assign (ofString "heap_ptr") source.code (ofString "i") (.op .add [localVar "i",.const 1#64]) source rfl
    change evaluateHOLFiniteState source increment=(none,post) at run
    change GlobalEffects.erase (ofString "heap_ptr") (evaluateHOLFiniteState source increment).2=_ at frame
    rw [run] at frame
    exact (congrArg Prod.snd frame).trans actual.heap
  | cons selected rest ih=>
    change evaluateHOLFiniteState source (.seq (branch selected) (chain rest))=(none,post) at run
    obtain ⟨middle,normal,remaining⟩ := sequence_none source post _ _ run
    have next := (branch_summary source middle kind selected p roots out cursor stp accel chunk zeros n index active actual geometry none normal (by simp)).2 rfl
    exact ih middle post next remaining

/-- All five literal tests execute, but exactly one original record hash
is charged for the actual kind; inactive branches have zero source cost. -/
theorem selected_price (kind : Kind) : chainPrice kind kinds=kind.record.price+1 := by cases kind <;> decide

end InitECandidate.Solver.Input.RequestListHash

#print axioms InitECandidate.Solver.Input.RequestListHash.branch_evaluate
#print axioms InitECandidate.Solver.Input.RequestListHash.branch_summary
#print axioms InitECandidate.Solver.Input.RequestListHash.chain_cost
#print axioms InitECandidate.Solver.Input.RequestListHash.chain_local
#print axioms InitECandidate.Solver.Input.RequestListHash.chain_advance
#print axioms InitECandidate.Solver.Input.RequestListHash.chain_globals
#print axioms InitECandidate.Solver.Input.RequestListHash.chain_normal_heap
#print axioms InitECandidate.Solver.Input.RequestListHash.selected_price
