import InitECandidate.Solver.Headers.WordLoopCost
import InitECandidate.Solver.Headers.CurrentFieldValue
import InitECandidate.Solver.Headers.FieldRowArguments
import InitECandidate.Solver.Headers.FieldCallSyntax

namespace InitECandidate.Solver.Headers.CurrentWord
open WordField
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Complete original hdr_word_field204, from its real selected RLP row and
normal uint-field result; the guarded byte loop adds at most eight ticks. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer : BitVec 64) (bytes index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (selected : items[index]?=some item) (model : Rlp.ListItems source pointer bytes items)
    (records : Rlp.Slices.Records source.memory array pointer items)
    (arena : Input.CurrentStartup.ArenaState source) (allocation : AllocatedBytes.Arena array (16*items.length))
    (arrayAligned : array.toNat%8=0) (fits : pointer.toNat+bytes<2^64)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤60*item.total.toNat+20 := by
  obtain ⟨callee,called,calleeArray,calleeIndex,_⟩ := Field.environment source.code.lookup .uint array (BitVec.ofNat 64 index) 0#64 (Field.original_code source.code installed .uint)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Field.Kind.uint.values array (BitVec.ofNat 64 index) 0#64) := by
    simp [arguments,Field.Kind.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,arrayCell,indexCell]
  let entry := callEntryStateHOLFinite source callee
  have entryModel : Rlp.ListItems entry pointer bytes items := Rlp.ListItems.transport source entry pointer bytes items model (by omega) (by intro offset inside; rfl)
  have entryArena : Input.CurrentStartup.ArenaState entry := arena.of_frame rfl
  obtain ⟨rowArgs,positive,bounded,itemFits⟩ := Field.selected_arguments entry array pointer bytes index items item selected entryModel records entryArena.domain allocation arrayAligned fits calleeArray calleeIndex
  have fieldPrice := CurrentField.body_cost entry .uint (Rlp.Slices.itemPointer pointer items index) item.total rowArgs entryArena itemFits installed
  have cost := Input.ClockCost.scoped_reached_current source "f" (.comb [.one,.one]) (ofString "hdr_uint_field") arguments _ Field.Kind.uint.body afterField callee Field.Kind.uint.resultShape
    (60*item.total.toNat+11) 8 args called fieldPrice ?_
  · rw [body_shape]
    exact cost
  · intro parsed answer actual checked
    obtain ⟨header,payload,valid,valueEq⟩ := CurrentField.body_normal_value entry parsed .uint (Rlp.Slices.itemPointer pointer items index) item.total rowArgs entryArena itemFits answer actual
    rw [valueEq]
    exact after_field_cost (Input.CallNormal.continuationEntry source parsed "f" (Field.Kind.uint.returnValue (Rlp.Slices.itemPointer pointer items index+header) payload))
      (Rlp.Slices.itemPointer pointer items index+header) payload
      (by simp [Input.CallNormal.continuationEntry,Field.Kind.returnValue,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE])

end InitECandidate.Solver.Headers.CurrentWord

#print axioms InitECandidate.Solver.Headers.CurrentWord.body_cost
