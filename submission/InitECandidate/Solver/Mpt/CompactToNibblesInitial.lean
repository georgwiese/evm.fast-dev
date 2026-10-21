import InitECandidate.Solver.Mpt.CompactToNibblesProgram
import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def prepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (byte : BitVec 64) :=
  QueryBranch.bind (QueryBranch.bind (QueryBranch.bind source "first" (byte>>>4)) "is_leaf" ((byte>>>4>>>1)&&&1#64)) "odd" ((byte>>>4)&&&1#64)

theorem initial_executes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (byte : BitVec 64)
    (byteCell : source.locals.lookup (ofString "c0")=some (.val (.word byte))) :
    ∃ restoreStack,ProgramPrefix.Executes source initialActions (prepared source byte) restoreStack := by
  let firstState:=QueryBranch.bind source "first" (byte>>>4)
  let leafState:=QueryBranch.bind firstState "is_leaf" ((byte>>>4>>>1)&&&1#64)
  have firstCell : firstState.locals.lookup (ofString "first")=some (.val (.word (byte>>>4))):=bind_lookup_same _ _ _
  have keptFirst : leafState.locals.lookup (ofString "first")=some (.val (.word (byte>>>4))):=
    (bind_lookup_other firstState "is_leaf" "first" _ (by decide)).trans firstCell
  have firstRead : eval source firstExpression=some (.val (.word (byte>>>4))):=by simp [eval,firstExpression,localVar,evalHOLExact,toExact,byteCell,wordShiftHOL]
  have leafRead : eval firstState leafExpression=some (.val (.word ((byte>>>4>>>1)&&&1#64))):=by
    simp [eval,leafExpression,localVar,evalHOLExact,evalListHOLExact,toExact,firstCell,valueIsWord,valueWord,wordOpHOL,wordOp,wordShiftHOL] <;> rfl
  have oddRead : eval leafState oddExpression=some (.val (.word ((byte>>>4)&&&1#64))):=by
    simp [eval,oddExpression,localVar,evalHOLExact,evalListHOLExact,toExact,keptFirst,valueIsWord,valueWord,wordOpHOL,wordOp] <;> rfl
  exact ⟨_,.declare (byte>>>4) firstRead (.declare ((byte>>>4>>>1)&&&1#64) leafRead
    (.declare ((byte>>>4)&&&1#64) oddRead (.done _)))⟩

theorem prepared_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (byte : BitVec 64) (name : String)
    (notFirst : ofString "first"≠ofString name) (notLeaf : ofString "is_leaf"≠ofString name) (notOdd : ofString "odd"≠ofString name) :
    (prepared source byte).locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  simp [prepared,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notFirst,notLeaf,notOdd]

theorem prepared_erase (source : PanSemStateFiniteExact 64 Guest.HostMemory) (byte : BitVec 64) :
    Input.LocalEffects.erase (prepared source byte)=Input.LocalEffects.erase source:=rfl

/-- Three actual scalar declarations reach the real allocator call without
spending a source tick; the original lexical restorations remain attached. -/
theorem initial_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (byte : BitVec 64)
    (byteCell : source.locals.lookup (ofString "c0")=some (.val (.word byte)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterByte=(outcome,post)) :
    ∃ restoreStack inner,ProgramPrefix.Executes source initialActions (prepared source byte) restoreStack ∧
      evaluateHOLFiniteState (prepared source byte) allocationCall=(outcome,inner) ∧
      post=restoreStack inner ∧ post.clock=inner.clock := by
  obtain ⟨restoreStack,setup⟩:=initial_executes source byte byteCell
  have actual:=ProgramPrefix.execute setup allocationCall
  rw [initial_shape,actual] at run
  let inner:=(evaluateHOLFiniteState (prepared source byte) allocationCall).2
  have firstEq:=congrArg Prod.fst run
  have endpoint:=congrArg Prod.snd run
  change restoreStack inner=post at endpoint
  have continued : evaluateHOLFiniteState (prepared source byte) allocationCall=(outcome,inner):=Prod.ext firstEq rfl
  have frame:=ProgramPrefix.restoration_frame setup inner
  have clock:=congrArg PanSemStateFiniteExact.clock frame
  change (restoreStack inner).clock=inner.clock at clock
  exact ⟨restoreStack,inner,setup,continued,endpoint.symm,by rw [←endpoint]; exact clock⟩

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.initial_executes
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.prepared_other
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.prepared_erase
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.initial_trace
