import InitECandidate.Solver.Rlp.ValidationProgram

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def movesPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer payload after : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  bind (bind (bind source "top" pointer) "pos" payload) "end" after

theorem moves_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (position ending previous pointer payload after : BitVec 64)
    (positionCell : source.locals.lookup (ofString "pos")=some (.val (.word position)))
    (endCell : source.locals.lookup (ofString "end")=some (.val (.word ending)))
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word previous)))
    (recordCell : source.locals.lookup (ofString "rec")=some (.val (.word pointer)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word payload)))
    (afterCell : source.locals.lookup (ofString "after")=some (.val (.word after))) :
    evaluateHOLFiniteState source pushMoves=(none,movesPost source pointer payload after) := by
  let afterTop := bind source "top" pointer
  let afterPosition := bind afterTop "pos" payload
  have readRecord : eval source (localVar "rec")=some (.val (.word pointer)) := by simp [eval,localVar,evalHOLExact,toExact,recordCell]
  have firstRun := WitnessRadix.StateSteps.assign_execute source "top" _ previous pointer topCell readRecord
  have currentPosition : afterTop.locals.lookup (ofString "pos")=some (.val (.word position)) :=
    (bind_lookup_other source "top" "pos" pointer (by decide)).trans positionCell
  have currentPayload : afterTop.locals.lookup (ofString "payload")=some (.val (.word payload)) :=
    (bind_lookup_other source "top" "payload" pointer (by decide)).trans payloadCell
  have readPayload : eval afterTop (localVar "payload")=some (.val (.word payload)) := by simp [eval,localVar,evalHOLExact,toExact,currentPayload]
  have secondRun := WitnessRadix.StateSteps.assign_execute afterTop "pos" _ position payload currentPosition readPayload
  have currentEnd : afterPosition.locals.lookup (ofString "end")=some (.val (.word ending)) :=
    (bind_lookup_other afterTop "pos" "end" payload (by decide)).trans ((bind_lookup_other source "top" "end" pointer (by decide)).trans endCell)
  have currentAfter : afterPosition.locals.lookup (ofString "after")=some (.val (.word after)) :=
    (bind_lookup_other afterTop "pos" "after" payload (by decide)).trans ((bind_lookup_other source "top" "after" pointer (by decide)).trans afterCell)
  have readAfter : eval afterPosition (localVar "after")=some (.val (.word after)) := by simp [eval,localVar,evalHOLExact,toExact,currentAfter]
  have thirdRun := WitnessRadix.StateSteps.assign_execute afterPosition "end" _ ending after currentEnd readAfter
  rw [pushMoves,WitnessRadix.StateSteps.next_sequence source afterTop _ _ firstRun (Nat.le_refl _),
    WitnessRadix.StateSteps.next_sequence afterTop afterPosition _ _ secondRun (Nat.le_refl _)]
  exact thirdRun

theorem moves_position (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer payload after : BitVec 64) :
    (movesPost source pointer payload after).locals.lookup (ofString "pos")=some (.val (.word payload)) := by
  rw [movesPost,bind_lookup_other _ "end" "pos" _ (by decide)]
  exact bind_lookup_same _ _ _
theorem moves_end (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer payload after : BitVec 64) :
    (movesPost source pointer payload after).locals.lookup (ofString "end")=some (.val (.word after)) := bind_lookup_same _ _ _
theorem moves_top (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer payload after : BitVec 64) :
    (movesPost source pointer payload after).locals.lookup (ofString "top")=some (.val (.word pointer)) := by
  rw [movesPost,bind_lookup_other _ "end" "top" _ (by decide),bind_lookup_other _ "pos" "top" _ (by decide)]
  exact bind_lookup_same _ _ _
theorem moves_go (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer payload after : BitVec 64) :
    (movesPost source pointer payload after).locals.lookup (ofString "go")=source.locals.lookup (ofString "go") := by
  rw [movesPost,bind_lookup_other _ "end" "go" _ (by decide),bind_lookup_other _ "pos" "go" _ (by decide),bind_lookup_other _ "top" "go" _ (by decide)]

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.moves_execute
#print axioms InitECandidate.Solver.Rlp.Validation.moves_position
#print axioms InitECandidate.Solver.Rlp.Validation.moves_end
#print axioms InitECandidate.Solver.Rlp.Validation.moves_top
#print axioms InitECandidate.Solver.Rlp.Validation.moves_go
