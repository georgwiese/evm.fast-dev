import InitECandidate.Solver.Rlp.ValidationProgram
import InitECandidate.Solver.Rlp.ValidationMemory
import InitECandidate.Solver.PanFieldStores

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def popPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : Frame) (rest : List Frame) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  bind (bind (bind source "pos" frame.resume) "end" frame.parentEnd) "top" (topOf rest)

/-- Execute the actual original three-load pop, preserving its load order:
the top pointer is overwritten only after loading resume and parent end. -/
theorem pop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (rootEnd ending position : BitVec 64)
    (frame : Frame) (rest : List Frame) (pending : Pending source.memory source.memaddrs cursor rootEnd (frame::rest) ending)
    (positionCell : source.locals.lookup (ofString "pos")=some (.val (.word position)))
    (endCell : source.locals.lookup (ofString "end")=some (.val (.word ending)))
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word frame.pointer))) :
    evaluateHOLFiniteState source pop=(none,popPost source frame rest) := by
  obtain ⟨sameEnd,active,lower,fits,ordered,mapped0,stored0,mapped8,stored8,mapped16,stored16,tail⟩ := pending
  let afterPos := bind source "pos" frame.resume
  let afterEnd := bind afterPos "end" frame.parentEnd
  have read0 : eval source (.load .one (addConst (localVar "top") 0#64))=some (.val (.word frame.resume)) :=
    FieldStores.Value.read source "top" frame.pointer (.copied 0 frame.resume)
      ⟨topCell,by simpa using mapped0,by simpa using stored0⟩
  have firstRun := StateSteps.assign_execute source "pos" _ position frame.resume positionCell read0
  have currentTop : afterPos.locals.lookup (ofString "top")=some (.val (.word frame.pointer)) :=
    (bind_lookup_other source "pos" "top" frame.resume (by decide)).trans topCell
  have currentEnd : afterPos.locals.lookup (ofString "end")=some (.val (.word ending)) :=
    (bind_lookup_other source "pos" "end" frame.resume (by decide)).trans endCell
  have read8 : eval afterPos (.load .one (addConst (localVar "top") 8#64))=some (.val (.word frame.parentEnd)) :=
    FieldStores.Value.read afterPos "top" frame.pointer (.copied 8 frame.parentEnd) ⟨currentTop,mapped8,stored8⟩
  have secondRun := StateSteps.assign_execute afterPos "end" _ ending frame.parentEnd currentEnd read8
  have lastTop : afterEnd.locals.lookup (ofString "top")=some (.val (.word frame.pointer)) :=
    (bind_lookup_other afterPos "end" "top" frame.parentEnd (by decide)).trans currentTop
  have read16 : eval afterEnd (.load .one (addConst (localVar "top") 16#64))=some (.val (.word (topOf rest))) :=
    FieldStores.Value.read afterEnd "top" frame.pointer (.copied 16 (topOf rest)) ⟨lastTop,mapped16,stored16⟩
  have thirdRun := StateSteps.assign_execute afterEnd "top" _ frame.pointer (topOf rest) lastTop read16
  rw [pop,StateSteps.next_sequence source afterPos _ _ firstRun (Nat.le_refl _),
    StateSteps.next_sequence afterPos afterEnd _ _ secondRun (Nat.le_refl _)]
  exact thirdRun

theorem pop_position (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : Frame) (rest : List Frame) :
    (popPost source frame rest).locals.lookup (ofString "pos")=some (.val (.word frame.resume)) := by
  rw [popPost,bind_lookup_other _ "top" "pos" _ (by decide),bind_lookup_other _ "end" "pos" _ (by decide)]
  exact bind_lookup_same _ _ _
theorem pop_end (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : Frame) (rest : List Frame) :
    (popPost source frame rest).locals.lookup (ofString "end")=some (.val (.word frame.parentEnd)) := by
  rw [popPost,bind_lookup_other _ "top" "end" _ (by decide)]
  exact bind_lookup_same _ _ _
theorem pop_top (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : Frame) (rest : List Frame) :
    (popPost source frame rest).locals.lookup (ofString "top")=some (.val (.word (topOf rest))) := bind_lookup_same _ _ _
theorem pop_go (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : Frame) (rest : List Frame) :
    (popPost source frame rest).locals.lookup (ofString "go")=source.locals.lookup (ofString "go") := by
  rw [popPost,bind_lookup_other _ "top" "go" _ (by decide),bind_lookup_other _ "end" "go" _ (by decide),bind_lookup_other _ "pos" "go" _ (by decide)]

theorem pop_pending (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (rootEnd ending : BitVec 64)
    (frame : Frame) (rest : List Frame) (pending : Pending source.memory source.memaddrs cursor rootEnd (frame::rest) ending) :
    Pending (popPost source frame rest).memory (popPost source frame rest).memaddrs cursor rootEnd rest frame.parentEnd := pending.2.2.2.2.2.2.2.2.2.2.2

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.pop_execute
#print axioms InitECandidate.Solver.Rlp.Validation.pop_position
#print axioms InitECandidate.Solver.Rlp.Validation.pop_end
#print axioms InitECandidate.Solver.Rlp.Validation.pop_top
#print axioms InitECandidate.Solver.Rlp.Validation.pop_go
#print axioms InitECandidate.Solver.Rlp.Validation.pop_pending
