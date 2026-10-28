import InitECandidate.Solver.Headers.CurrentWordCost
import InitECandidate.Solver.Input.LocalEffectsLoop

namespace InitECandidate.Solver.Headers.WordField
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Every guarded word-reader suffix only reads bytes and changes locals,
including exhausted clocks and invalid memory outcomes. -/
theorem after_field_readonly (code) : Input.LocalEffects.Preserves code afterField := by
  have loopFrame : Input.LocalEffects.Preserves code loop := by
    rw [loop_shape]
    exact Input.LocalEffects.loop code condition loopBody
      (Input.LocalEffects.sequence code accumulate increment
        (Input.LocalEffects.assign code _ _) (Input.LocalEffects.assign code _ _))
  have back : Input.LocalEffects.Preserves code afterGuard := by
    rw [after_guard_shape]
    apply Input.LocalEffects.declared
    apply Input.LocalEffects.declared
    exact Input.LocalEffects.sequence code loop _ loopFrame (Input.LocalEffects.returned code _)
  rw [field_shape]
  exact Input.LocalEffects.sequence code _ afterGuard
    (Input.LocalEffects.conditional code _ _ _ (Input.LocalEffects.raised code _ _) (Input.LocalEffects.skip code)) back

end InitECandidate.Solver.Headers.WordField

namespace InitECandidate.Solver.Headers.CurrentWord
open WordField
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

/-- Real normal word-field decoding retains the original input, record array,
arenas, heap and all other nonlocal observations. -/
theorem body_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer : BitVec 64) (bytes index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (selected : items[index]?=some item) (model : Rlp.ListItems source pointer bytes items)
    (records : Rlp.Slices.Records source.memory array pointer items)
    (arena : CurrentStartup.ArenaState source) (allocation : AllocatedBytes.Arena array (16*items.length))
    (arrayAligned : array.toNat%8=0) (fits : pointer.toNat+bytes<2^64)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    LocalEffects.erase post=LocalEffects.erase source := by
  obtain ⟨callee,called,calleeArray,calleeIndex,_⟩:=Field.environment source.code.lookup .uint array (BitVec.ofNat 64 index) 0#64 (Field.original_code source.code arena.code .uint)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Field.Kind.uint.values array (BitVec.ofNat 64 index) 0#64) := by
    simp [arguments,Field.Kind.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,arrayCell,indexCell]
  let entry:=callEntryStateHOLFinite source callee
  have entryModel:=Rlp.ListItems.transport source entry pointer bytes items model (by omega) (by intro offset inside; rfl)
  have entryArena : CurrentStartup.ArenaState entry := arena.of_frame rfl
  obtain ⟨rowArgs,positive,bounded,itemFits⟩:=Field.selected_arguments entry array pointer bytes index items item selected entryModel records entryArena.domain allocation arrayAligned fits calleeArray calleeIndex
  rw [body_shape] at normal
  obtain ⟨funded,target,answer,inner,bodyRun,checked,continuation,endpoint⟩:=CallNormal.scoped_normal source post "f" (.comb [.one,.one]) (ofString "hdr_uint_field") arguments _ Field.Kind.uint.body afterField callee Field.Kind.uint.resultShape args called value normal
  have frame:=CurrentField.body_frame entry target .uint (Rlp.Slices.itemPointer pointer items index) item.total rowArgs entryArena itemFits answer bodyRun
  have codeEq:=congrArg PanSemStateFiniteExact.code frame
  have tailFrame:=after_field_readonly source.code (CallNormal.continuationEntry source target "f" answer) codeEq
  rw [continuation] at tailFrame
  rw [endpoint]
  exact tailFrame.trans frame

end InitECandidate.Solver.Headers.CurrentWord

#print axioms InitECandidate.Solver.Headers.WordField.after_field_readonly
#print axioms InitECandidate.Solver.Headers.CurrentWord.body_frame
