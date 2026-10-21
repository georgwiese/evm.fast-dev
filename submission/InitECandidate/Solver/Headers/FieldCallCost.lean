import InitECandidate.Solver.Headers.FieldCallProgram
import InitECandidate.Solver.Headers.FieldRows

namespace InitECandidate.Solver.Headers.Field
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- The actual original header-field caller is priced from the selected
physical row constructed by RLP slicing. Arbitrary caller destinations and
all outcomes are covered, with one additional caller tick. -/
theorem selected_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (array pointer cursor limit control : BitVec 64) (bytes index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (selected : items[index]?=some item) (model : Rlp.ListItems source pointer bytes items)
    (records : Rlp.Slices.Records source.memory array pointer items)
    (arena : Rlp.Validation.Arena source cursor limit) (allocation : AllocatedBytes.Arena array (16*items.length))
    (arrayAligned : array.toNat%8=0) (fits : pointer.toNat+bytes<2^64)
    (destination : Option (Option MlS)) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (kind.values array (BitVec.ofNat 64 index) control))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) kind.name expressions)).2.clock≤60*item.total.toNat+43 := by
  obtain ⟨callee,called,arrayCell,indexCell,controlCell⟩ := environment source.code.lookup kind array (BitVec.ofNat 64 index) control (original_code source.code installed kind)
  let entry := callEntryStateHOLFinite source callee
  have entryModel : Rlp.ListItems entry pointer bytes items :=
    Rlp.ListItems.transport source entry pointer bytes items model (by have := pointer.isLt; omega) (by intro offset inside; rfl)
  have entryArena := Rlp.Validation.Arena.of_fields source entry cursor limit arena rfl rfl
  have cost := (selected_body_cost entry kind array pointer cursor limit bytes index items item selected entryModel records entryArena allocation arrayAligned fits arrayCell indexCell installed).1
  exact Input.ClockCost.call_current source destination kind.name expressions _ kind.body callee kind.resultShape (60*item.total.toNat+42) args called cost

end InitECandidate.Solver.Headers.Field

#print axioms InitECandidate.Solver.Headers.Field.selected_call_cost
