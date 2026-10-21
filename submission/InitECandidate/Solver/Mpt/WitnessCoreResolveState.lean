import InitECandidate.Solver.Mpt.WitnessCoreResolveProgram
import InitECandidate.Solver.Mpt.WitnessRecordHash
import InitECandidate.Solver.Mpt.WitnessRecordFrame
import InitECandidate.Solver.Mpt.WitnessCoreTerminal

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def resolveAnswer (tag pointer length hash : BitVec 64) : ValueHOL 64:=
  .rStruct [.val (.word tag),.val (.word pointer),.val (.word length),.val (.word hash)]
def hashState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record hash : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory:=
  {source with memory:=StoreWord.put source.memory (record+80#64) hash}
def resolvedTerminal (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record node : BitVec 64):=
  delivered (hashState source record 0#64) node
def resolvedDecode (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record pointer length hash : BitVec 64):=
  bind (bind (bind (hashState source record hash) "cur_p" pointer) "cur_n" length) "mode" 1#64

private theorem hash_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db hash : BitVec 64) (data : WitnessRecord.Description) (view : WitnessRecord.View source record db data)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (expression : ExpHOL 64) (read : eval source expression=some (.val (.word hash))) :
    evaluateHOLFiniteState source (.store resolveHash expression)=(none,hashState source record hash) := by
  have addressRead : eval source resolveHash=some (.val (.word (record+80#64))):=by
    simp [eval,resolveHash,evalHOLExact,evalListHOLExact,localVar,toExact,topCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have mapped : source.memaddrs (record+80#64):=by
    simpa only [byteAddress] using view.mapped source record db data 80 (by decide) (by decide)
  exact StoreWord.execute source resolveHash expression (record+80#64) hash addressRead read mapped

theorem resolve_terminal_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db node length hash oldResult oldMode : BitVec 64) (data : WitnessRecord.Description)
    (view : WitnessRecord.View source record db data)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (rCell : source.locals.lookup (ofString "r")=some (resolveAnswer 0#64 node length hash))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word oldResult)))
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word oldMode))) :
    evaluateHOLFiniteState source resolveTerminal=(none,resolvedTerminal source record node) := by
  let ready:=hashState source record 0#64
  have storeRun:=hash_execute source record db 0#64 data view topCell (.const 0#64) rfl
  have currentR : ready.locals.lookup (ofString "r")=some (resolveAnswer 0#64 node length hash):=rCell
  have read : eval ready (resolveField 1)=some (.val (.word node)):=by
    simp [eval,resolveField,evalHOLExact,localVar,toExact,currentR,resolveAnswer]
  have resultRun:=StateSteps.assign_execute ready "result" (resolveField 1) oldResult node resultCell read
  have nextMode : (bind ready "result" node).locals.lookup (ofString "mode")=some (.val (.word oldMode)):=
    (bind_lookup_other ready "result" "mode" node (by decide)).trans modeCell
  have modeRun:=StateSteps.assign_execute (bind ready "result" node) "mode" (.const 0#64) oldMode 0#64 nextMode rfl
  rw [resolve_terminal_shape,StateSteps.next_sequence _ _ _ _ storeRun (Nat.le_refl _),
    StateSteps.next_sequence _ _ _ _ resultRun (Nat.le_refl _),modeRun]
  rfl

theorem resolve_decode_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db pointer length hash oldPointer oldLength oldMode : BitVec 64) (data : WitnessRecord.Description)
    (view : WitnessRecord.View source record db data)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (rCell : source.locals.lookup (ofString "r")=some (resolveAnswer 1#64 pointer length hash))
    (pointerCell : source.locals.lookup (ofString "cur_p")=some (.val (.word oldPointer)))
    (lengthCell : source.locals.lookup (ofString "cur_n")=some (.val (.word oldLength)))
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word oldMode))) :
    evaluateHOLFiniteState source resolveDecode=(none,resolvedDecode source record pointer length hash) := by
  let ready:=hashState source record hash
  let pointerState:=bind ready "cur_p" pointer
  let lengthState:=bind pointerState "cur_n" length
  have hashRead : eval source (resolveField 3)=some (.val (.word hash)):=by
    simp [eval,resolveField,evalHOLExact,localVar,toExact,rCell,resolveAnswer]
  have storeRun:=hash_execute source record db hash data view topCell (resolveField 3) hashRead
  have currentR : ready.locals.lookup (ofString "r")=some (resolveAnswer 1#64 pointer length hash):=rCell
  have pointerRead : eval ready (resolveField 1)=some (.val (.word pointer)):=by
    simp [eval,resolveField,evalHOLExact,localVar,toExact,currentR,resolveAnswer]
  have pointerRun:=StateSteps.assign_execute ready "cur_p" (resolveField 1) oldPointer pointer pointerCell pointerRead
  have nextLength : pointerState.locals.lookup (ofString "cur_n")=some (.val (.word oldLength)):=
    (bind_lookup_other ready "cur_p" "cur_n" pointer (by decide)).trans lengthCell
  have nextR : pointerState.locals.lookup (ofString "r")=some (resolveAnswer 1#64 pointer length hash):=
    (bind_lookup_other ready "cur_p" "r" pointer (by decide)).trans currentR
  have lengthRead : eval pointerState (resolveField 2)=some (.val (.word length)):=by
    simp [eval,resolveField,evalHOLExact,localVar,toExact,nextR,resolveAnswer]
  have lengthRun:=StateSteps.assign_execute pointerState "cur_n" (resolveField 2) oldLength length nextLength lengthRead
  have nextMode : lengthState.locals.lookup (ofString "mode")=some (.val (.word oldMode)):=
    (bind_lookup_other pointerState "cur_n" "mode" length (by decide)).trans
      ((bind_lookup_other ready "cur_p" "mode" pointer (by decide)).trans modeCell)
  have modeRun:=StateSteps.assign_execute lengthState "mode" (.const 1#64) oldMode 1#64 nextMode rfl
  rw [resolve_decode_shape,StateSteps.next_sequence _ _ _ _ storeRun (Nat.le_refl _),
    StateSteps.next_sequence _ _ _ _ pointerRun (Nat.le_refl _),
    StateSteps.next_sequence _ _ _ _ lengthRun (Nat.le_refl _),modeRun]
  rfl

theorem after_resolve_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tag pointer length hash : BitVec 64)
    (rCell : source.locals.lookup (ofString "r")=some (resolveAnswer tag pointer length hash)) :
    evaluateHOLFiniteState source afterResolve=
      if tag=0#64 then evaluateHOLFiniteState source resolveTerminal else evaluateHOLFiniteState source resolveDecode := by
  rw [after_resolve_shape]
  by_cases zero : tag=0#64 <;>
    simp [evaluateHOLFiniteState_ite,resolveField,evalHOLExact,localVar,toExact,rCell,resolveAnswer,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem resolved_terminal_view (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db node : BitVec 64)
    (data : WitnessRecord.Description) (view : WitnessRecord.View source record db data) :
    WitnessRecord.View (resolvedTerminal source record node) record db data :=
  (view.hashed source record db 0#64 data).of_fields _ _ record db data rfl rfl

theorem resolved_decode_view (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db pointer length hash : BitVec 64)
    (data : WitnessRecord.Description) (view : WitnessRecord.View source record db data) :
    WitnessRecord.View (resolvedDecode source record pointer length hash) record db data :=
  (view.hashed source record db hash data).of_fields _ _ record db data rfl rfl

theorem resolved_terminal_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record node : BitVec 64) :
    let current:=resolvedTerminal source record node
    current.locals.lookup (ofString "result")=some (.val (.word node)) ∧
      current.locals.lookup (ofString "mode")=some (.val (.word 0#64)) ∧
      current.memory (record+80#64)=.word 0#64 ∧ current.globals=source.globals ∧ current.clock=source.clock :=
  ⟨(bind_lookup_other _ "mode" "result" 0#64 (by decide)).trans (bind_lookup_same _ _ _),bind_lookup_same _ _ _,if_pos rfl,rfl,rfl⟩

theorem resolved_decode_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record pointer length hash : BitVec 64) :
    let current:=resolvedDecode source record pointer length hash
    current.locals.lookup (ofString "cur_p")=some (.val (.word pointer)) ∧
      current.locals.lookup (ofString "cur_n")=some (.val (.word length)) ∧
      current.locals.lookup (ofString "mode")=some (.val (.word 1#64)) ∧
      current.memory (record+80#64)=.word hash ∧ current.globals=source.globals ∧ current.clock=source.clock := by
  let ready:=hashState source record hash
  let pointerState:=bind ready "cur_p" pointer
  let lengthState:=bind pointerState "cur_n" length
  have currentPointer : lengthState.locals.lookup (ofString "cur_p")=some (.val (.word pointer)):=
    (bind_lookup_other pointerState "cur_n" "cur_p" length (by decide)).trans (bind_lookup_same _ _ _)
  exact ⟨(bind_lookup_other lengthState "mode" "cur_p" 1#64 (by decide)).trans currentPointer,
    (bind_lookup_other lengthState "mode" "cur_n" 1#64 (by decide)).trans (bind_lookup_same _ _ _),bind_lookup_same _ _ _,if_pos rfl,rfl,rfl⟩

theorem resolved_terminal_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record node : BitVec 64)
    (name : String) (notResult : ofString "result"≠ofString name) (notMode : ofString "mode"≠ofString name) :
    (resolvedTerminal source record node).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (bind_lookup_other _ "mode" name 0#64 notMode).trans (bind_lookup_other _ "result" name node notResult)

theorem resolved_decode_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record pointer length hash : BitVec 64)
    (name : String) (notPointer : ofString "cur_p"≠ofString name) (notLength : ofString "cur_n"≠ofString name) (notMode : ofString "mode"≠ofString name) :
    (resolvedDecode source record pointer length hash).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (bind_lookup_other _ "mode" name 1#64 notMode).trans
    ((bind_lookup_other _ "cur_n" name length notLength).trans (bind_lookup_other _ "cur_p" name pointer notPointer))

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.resolve_terminal_execute
#print axioms InitECandidate.Solver.Mpt.WitnessCore.resolve_decode_execute
#print axioms InitECandidate.Solver.Mpt.WitnessCore.after_resolve_choice
#print axioms InitECandidate.Solver.Mpt.WitnessCore.resolved_terminal_view
#print axioms InitECandidate.Solver.Mpt.WitnessCore.resolved_decode_view
#print axioms InitECandidate.Solver.Mpt.WitnessCore.resolved_terminal_fields
#print axioms InitECandidate.Solver.Mpt.WitnessCore.resolved_decode_fields
#print axioms InitECandidate.Solver.Mpt.WitnessCore.resolved_terminal_other
#print axioms InitECandidate.Solver.Mpt.WitnessCore.resolved_decode_other
