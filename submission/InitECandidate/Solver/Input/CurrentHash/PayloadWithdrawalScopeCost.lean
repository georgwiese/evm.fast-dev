import InitECandidate.Solver.Input.CurrentHash.PayloadWithdrawalAllocationCost

set_option maxRecDepth 20000
set_option maxHeartbeats 200000

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob record array ch cursor chunk out zeros base : BitVec 64} {length start size : Nat}

/-- Complete actual withdrawal phase, including decoded field declarations,
assigned roots allocation, actual loop/list, both release and final fields. -/
theorem State.withdrawal_cost (data : State input source blob record array ch cursor chunk out zeros length start size)
    (saved : SavedCursor source "m2" ch base) (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source withdrawalScope=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤848*withdrawalCount input+5*balanceLength input length+11497 := by
  have entry := data.withdrawal_data
  let firstState := bind source "wd" (withdrawalPointer input blob)
  let secondState := bind firstState "nwd" (BitVec.ofNat 64 (withdrawalCount input))
  have next : State input firstState blob record array ch cursor chunk out zeros length start size := data.bound "wd" (withdrawalPointer input blob) (by decide)
  have finalState : State input secondState blob record array ch cursor chunk out zeros length start size := next.bound "nwd" (BitVec.ofNat 64 (withdrawalCount input)) (by decide)
  have savedFirst : SavedCursor firstState "m2" ch base := saved.of_lookup
    ((bind_lookup_other source "wd" "m2" (withdrawalPointer input blob) (by decide)).trans saved.binding)
  have savedSecond : SavedCursor secondState "m2" ch base := savedFirst.of_lookup
    ((bind_lookup_other firstState "nwd" "m2" (BitVec.ofNat 64 (withdrawalCount input)) (by decide)).trans savedFirst.binding)
  have pointer : secondState.locals.lookup (ofString "wd")=some (.val (.word (withdrawalPointer input blob))) :=
    (bind_lookup_other firstState "nwd" "wd" (BitVec.ofNat 64 (withdrawalCount input)) (by decide)).trans (bind_lookup_same source "wd" (withdrawalPointer input blob))
  have count : secondState.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 (withdrawalCount input)))) := bind_lookup_same firstState "nwd" (BitVec.ofNat 64 (withdrawalCount input))
  have countRead := next.withdrawal_data.2.1
  let output := evaluateHOLFiniteState secondState afterNwd
  have inner := ScalarScope.declare_execute firstState output.2 "nwd" (fieldExpression 56) (BitVec.ofNat 64 (withdrawalCount input)) afterNwd output.1 countRead rfl
  have innerRun : evaluateHOLFiniteState firstState afterWd=(output.1,restore firstState "nwd" output.2) := by
    rw [withdrawal_shapes.2.1]
    exact inner
  have whole := ScalarScope.declare_execute source (restore firstState "nwd" output.2) "wd" (fieldExpression 48) (withdrawalPointer input blob) afterWd output.1 entry.1 innerRun
  rw [←withdrawal_shapes.1] at whole
  have resultEq : result=output.1 := congrArg Prod.fst (actual.symm.trans whole)
  have clockEq := congrArg (fun observed : Option (PanSemResultExact 64)×PanSemStateFiniteExact 64 Guest.HostMemory=>observed.2.clock) (actual.symm.trans whole)
  change post.clock=output.2.clock at clockEq
  have observed : output.1≠some .timeOut := by rw [←resultEq]; exact notTimeout
  have paid := finalState.withdrawal_after_nwd_cost (post:=output.2) savedSecond (withdrawalPointer input blob) (withdrawalCount input) entry.2.2.1 pointer count entry.2.2.2 output.1 rfl observed
  change source.clock-output.2.clock≤848*withdrawalCount input+5*balanceLength input length+11497 at paid
  rw [clockEq]
  exact paid


end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.withdrawal_cost
