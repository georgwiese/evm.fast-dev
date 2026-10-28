import InitECandidate.Solver.Headers.CurrentPipeline.State

namespace InitECandidate.Solver.Headers.CurrentPipeline
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

/-- A real assigned helper call derives its new typed value and full frame.
It retains the active slot types and every protected physical input record. -/
theorem State.assigned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array header current control : BitVec 64) (bytes index : Nat) (items : List Rlp.ListItem) (active : List Slot)
    (state : State source pointer array header current bytes items active)
    (slot : Slot) (kind : Helper.Kind) (item : Rlp.ListItem) (selected : items[index]?=some item)
    (shape : kind.resultShape=slot.shape) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (kind.values array (BitVec.ofNat 64 index) control))
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,slot.name),none)) kind.name expressions)=(none,post)) :
    State post pointer array header current bytes items active := by
  obtain ⟨value,typed,frame,localsEq⟩:=CurrentHelpers.assigned_none source post kind array pointer control bytes index items item state.slices selected slot.name expressions args normal
  have slots:=state.slots.set source active slot value (typed.trans shape)
  have actualSlots : Slots post (slot::active) := slots.of_locals _ post (slot::active) localsEq
  have slices:=state.slices.of_frame frame
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  apply state.of_parts active slices (actualSlots.tail post slot active) globals
  · rw [localsEq]
    simpa [HolFiniteMapExact.update,FUPDATE,slot.not_array,Ne.symm slot.not_array] using state.arrayCell
  · rw [localsEq]
    simpa [HolFiniteMapExact.update,FUPDATE,slot.not_header,Ne.symm slot.not_header] using state.headerCell
  · rw [localsEq]
    simpa [HolFiniteMapExact.update,FUPDATE,slot.not_current,Ne.symm slot.not_current] using state.currentCell

end InitECandidate.Solver.Headers.CurrentPipeline

#print axioms InitECandidate.Solver.Headers.CurrentPipeline.State.assigned
