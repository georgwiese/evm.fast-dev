import InitECandidate.Solver.Headers.CurrentHelpers.Body

namespace InitECandidate.Solver.Headers.CurrentHelpers
open Helper
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix

/-- All five actual field helpers preserve every nonlocal field on their
real normal returns. This supplies one shared physical-state frame. -/
theorem body_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (array pointer control : BitVec 64) (bytes index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (state : SliceImage source pointer array bytes items) (selected : items[index]?=some item)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (controlCell : kind.ternary=true → source.locals.lookup kind.controlName=some (.val (.word control)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source kind.body=(some (.returned value),post)) :
    LocalEffects.erase post=LocalEffects.erase source := by
  have row:=Field.selected_arguments source array pointer bytes index items item selected state.itemsAtInput state.records state.arena.domain state.arrayArena state.arrayAligned state.inputFits arrayCell indexCell
  cases kind
  · exact CurrentField.body_frame source post .uint (Rlp.Slices.itemPointer pointer items index) item.total row.1 state.arena row.2.2.2 value normal
  · exact CurrentField.body_frame source post .bytes (Rlp.Slices.itemPointer pointer items index) item.total row.1 state.arena row.2.2.2 value normal
  · exact CurrentField.body_frame source post .raw (Rlp.Slices.itemPointer pointer items index) item.total row.1 state.arena row.2.2.2 value normal
  · exact CurrentWord.body_frame source post array pointer bytes index items item selected state.itemsAtInput state.records state.arena state.arrayArena state.arrayAligned state.inputFits arrayCell indexCell value normal
  · exact CurrentU256.body_frame source post array pointer control bytes index items item selected state.itemsAtInput state.records state.arena state.arrayArena state.arrayAligned state.inputFits arrayCell indexCell (controlCell rfl) value normal

end InitECandidate.Solver.Headers.CurrentHelpers

#print axioms InitECandidate.Solver.Headers.CurrentHelpers.body_frame
