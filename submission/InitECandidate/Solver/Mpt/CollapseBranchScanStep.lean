import InitECandidate.Solver.Mpt.CollapseBranchProgram
import InitECandidate.Solver.WitnessRadix.StateSteps
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem child_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node index child : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (counterCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (mapped : source.memaddrs (node+32#64+index*8#64))
    (stored : source.memory (node+32#64+index*8#64)=.word child) :
    eval source (.load .one (childAddress (localVar "i")))=some (.val (.word child)) := by
  simp [eval,childAddress,localVar,evalHOLExact,evalListHOLExact,toExact,nodeCell,counterCell,
    valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,memLoadHOLExact,isWfShapeExactHOL,←BitVec.add_assoc,mapped,stored]

theorem selected_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index count oldIndex : BitVec 64)
    (counterCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (countCell : source.locals.lookup (ofString "count")=some (.val (.word count)))
    (indexCell : source.locals.lookup (ofString "idx")=some (.val (.word oldIndex))) :
    evaluateHOLFiniteState source selected=(none,QueryBranch.bind (QueryBranch.bind source "count" (count+1#64)) "idx" index) := by
  have countRead : eval source (.op .add [localVar "count",.const 1#64])=some (.val (.word (count+1#64))):=by
    simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,countCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have counted:=StateSteps.assign_execute source "count" _ count (count+1#64) countCell countRead
  let next:=QueryBranch.bind source "count" (count+1#64)
  have currentI : next.locals.lookup (ofString "i")=some (.val (.word index)):=
    (bind_lookup_other source "count" "i" (count+1#64) (by decide)).trans counterCell
  have currentIndex : next.locals.lookup (ofString "idx")=some (.val (.word oldIndex)):=
    (bind_lookup_other source "count" "idx" (count+1#64) (by decide)).trans indexCell
  have indexRead : eval next (localVar "i")=some (.val (.word index)):=by simp [eval,localVar,evalHOLExact,toExact,currentI]
  rw [selected,StateSteps.next_sequence source next _ _ counted (Nat.le_refl _)]
  exact StateSteps.assign_execute next "idx" _ oldIndex index currentIndex indexRead

def scanned (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index count child : BitVec 64) :=
  QueryBranch.bind (if child=0#64 then source else QueryBranch.bind (QueryBranch.bind source "count" (count+1#64)) "idx" index) "i" (index+1#64)

/-- Exact original scan step. The actual mapped child controls both the
count increment and saved index; all memory and nonlocal fields survive. -/
theorem scan_step_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node index count oldIndex child : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (counterCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (countCell : source.locals.lookup (ofString "count")=some (.val (.word count)))
    (indexCell : source.locals.lookup (ofString "idx")=some (.val (.word oldIndex)))
    (mapped : source.memaddrs (node+32#64+index*8#64))
    (stored : source.memory (node+32#64+index*8#64)=.word child) :
    evaluateHOLFiniteState source scanBody=(none,scanned source index count child) := by
  have childRead:=child_read source node index child nodeCell counterCell mapped stored
  have choice : evaluateHOLFiniteState source scanChoice=
      (none,if child=0#64 then source else QueryBranch.bind (QueryBranch.bind source "count" (count+1#64)) "idx" index):=by
    rw [scan_shapes.2.2.1,evaluateHOLFiniteState_ite]
    simp only [eval] at childRead
    rw [evalHOLExact,childRead]
    simp only [evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    by_cases zero : child=0#64
    · simp [zero,evaluateHOLFiniteState_skip]
    · simpa [zero] using selected_execute source index count oldIndex counterCell countCell indexCell
  let middle:=if child=0#64 then source else QueryBranch.bind (QueryBranch.bind source "count" (count+1#64)) "idx" index
  have middleI : middle.locals.lookup (ofString "i")=some (.val (.word index)):=by
    dsimp only [middle]
    split
    · exact counterCell
    · exact (bind_lookup_other _ "idx" "i" index (by decide)).trans ((bind_lookup_other source "count" "i" (count+1#64) (by decide)).trans counterCell)
  have middleClock : middle.clock≤source.clock:=by dsimp only [middle]; split <;> exact Nat.le_refl _
  have incrementRead : eval middle (.op .add [localVar "i",.const 1#64])=some (.val (.word (index+1#64))):=by
    simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,middleI,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [scan_shapes.2.1,StateSteps.next_sequence source middle _ _ choice middleClock,scan_shapes.2.2.2]
  exact StateSteps.assign_execute middle "i" _ index (index+1#64) middleI incrementRead

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.child_read
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.selected_execute
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.scan_step_execute
