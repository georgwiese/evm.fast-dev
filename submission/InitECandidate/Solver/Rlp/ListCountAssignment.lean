import InitECandidate.Solver.Rlp.ListCountSyntax
import InitECandidate.Solver.Input.ClockCost
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Rlp.ListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def advancePost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (offset count size : BitVec 64) :=
  bind (bind source "off" (offset+size)) "count" (count+1#64)

theorem advance_price (code) : Input.ClockCost.Bound code advance 0 :=
  Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.assign code _ _) (Input.ClockCost.assign code _ _)

theorem advance_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (offset count size : BitVec 64)
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset)))
    (countCell : source.locals.lookup (ofString "count")=some (.val (.word count)))
    (sizeCell : source.locals.lookup (ofString "total")=some (.val (.word size))) :
    evaluateHOLFiniteState source advance=(none,advancePost source offset count size) := by
  have offsetRead : eval source (.op .add [localVar "off",localVar "total"])=some (.val (.word (offset+size))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,offsetCell,sizeCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have first := WitnessRadix.StateSteps.assign_execute source "off" _ offset (offset+size) offsetCell offsetRead
  let middle := bind source "off" (offset+size)
  have currentCount : middle.locals.lookup (ofString "count")=some (.val (.word count)) := (bind_lookup_other _ "off" "count" _ (by decide)).trans countCell
  have countRead : eval middle (.op .add [localVar "count",.const 1#64])=some (.val (.word (count+1#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,currentCount,valueIsWord,valueWord,wordOpHOL,wordOp]
  have second := WitnessRadix.StateSteps.assign_execute middle "count" _ count (count+1#64) currentCount countRead
  rw [advance,WitnessRadix.StateSteps.next_sequence source middle _ _ first (Nat.le_refl _)]
  exact second

end InitECandidate.Solver.Rlp.ListCount

#print axioms InitECandidate.Solver.Rlp.ListCount.advance_price
#print axioms InitECandidate.Solver.Rlp.ListCount.advance_execute
