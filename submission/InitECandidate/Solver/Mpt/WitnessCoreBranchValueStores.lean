import InitECandidate.Solver.Mpt.WitnessCoreReturnProgram
import InitECandidate.Solver.Mpt.WitnessRecordChild
import InitECandidate.Solver.Mpt.WitnessRecordFrame
import InitECandidate.Solver.Rlp.ItemValue
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Before the last row, the branch's original value words remain zero. -/
def EmptyValue (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) : Prop :=
  source.memory (node+160#64)=.word 0#64 ∧ source.memory (node+168#64)=.word 0#64

theorem EmptyValue.frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (empty : EmptyValue source node)
    (pointer : target.memory (node+160#64)=source.memory (node+160#64))
    (length : target.memory (node+168#64)=source.memory (node+168#64)) : EmptyValue target node :=
  ⟨pointer.trans empty.1,length.trans empty.2⟩

def branchValueOccupied (bytes flag : BitVec 64) (occupied : Fin 17) : Nat:=
  if flag=0#64 ∧ bytes≠0#64 then occupied.val+1 else occupied.val

def branchValueState (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node pointer header bytes flag : BitVec 64) (occupied : Fin 17) : PanSemStateFiniteExact 64 Guest.HostMemory:=
  if flag=0#64 then
    let stored:={source with memory:=StoreWord.put (StoreWord.put source.memory (node+160#64) (pointer+header)) (node+168#64) bytes}
    if bytes=0#64 then stored else QueryBranch.bind stored "occ" (BitVec.ofNat 64 (occupied.val+1))
  else source

/-- Execute the exact original flag-dependent branch value writes and
optional local occupancy increment. A list-valued row leaves both words
unchanged, as in the original program. -/
theorem branch_value_writes_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node pointer header bytes flag : BitVec 64) (occupied : Fin 17)
    (domain : source.memaddrs=InitE.ordinaryDomain) (nodeArena : AllocatedBytes.Arena node 176) (aligned : node.toNat%8=0)
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word node)))
    (valueCell : source.locals.lookup (ofString "bv")=some (Rlp.Item.result pointer header bytes flag))
    (occupiedCell : source.locals.lookup (ofString "occ")=some (.val (.word (BitVec.ofNat 64 occupied.val)))) :
    evaluateHOLFiniteState source branchValueWrites=(none,branchValueState source node pointer header bytes flag occupied) := by
  have choice : evaluateHOLFiniteState source branchValueWrites=
      if flag=0#64 then evaluateHOLFiniteState source
        (.seq (writeAt "br" 160#64 (returnField 1)) (.seq (writeAt "br" 168#64 (returnField 2))
          (.ite (.cmp .notEqual (returnField 2) (.const 0#64)) (.assign .local (ofString "occ") (.op .add [localVar "occ",.const 1#64])) .skip)))
      else (none,source) := by
    rw [branch_value_writes_shape,evaluateHOLFiniteState_ite]
    by_cases zero : flag=0#64 <;>
      simp [evalHOLExact,returnField,localVar,toExact,valueCell,Rlp.Item.result,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  rw [choice]
  by_cases flagZero : flag=0#64
  · rw [if_pos flagZero]
    let first : PanSemStateFiniteExact 64 Guest.HostMemory:={source with memory:=StoreWord.put source.memory (node+160#64) (pointer+header)}
    let second : PanSemStateFiniteExact 64 Guest.HostMemory:={first with memory:=StoreWord.put first.memory (node+168#64) bytes}
    have mapped160 : source.memaddrs (node+160#64):=AllocatedBytes.word_mapped source node 176 160 domain nodeArena (by decide) aligned (by decide)
    have mapped168 : source.memaddrs (node+168#64):=AllocatedBytes.word_mapped source node 176 168 domain nodeArena (by decide) aligned (by decide)
    have address160 : eval source (.op .add [localVar "br",.const 160#64])=some (.val (.word (node+160#64))):=by
      simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,branchCell,valueIsWord,valueWord,wordOpHOL,wordOp]
    have pointerRead : eval source (returnField 1)=some (.val (.word (pointer+header))):=by
      simp [eval,returnField,evalHOLExact,localVar,toExact,valueCell,Rlp.Item.result]
    have firstRun : evaluateHOLFiniteState source (writeAt "br" 160#64 (returnField 1))=(none,first):=
      StoreWord.execute source _ _ _ _ address160 pointerRead mapped160
    have address168 : eval first (.op .add [localVar "br",.const 168#64])=some (.val (.word (node+168#64))):=by
      simp [eval,first,evalHOLExact,evalListHOLExact,localVar,toExact,branchCell,valueIsWord,valueWord,wordOpHOL,wordOp]
    have bytesRead : eval first (returnField 2)=some (.val (.word bytes)):=by
      simp [eval,first,returnField,evalHOLExact,localVar,toExact,valueCell,Rlp.Item.result]
    have secondRun : evaluateHOLFiniteState first (writeAt "br" 168#64 (returnField 2))=(none,second):=
      StoreWord.execute first _ _ _ _ address168 bytesRead mapped168
    rw [StateSteps.next_sequence source first _ _ firstRun (Nat.le_refl _),StateSteps.next_sequence first second _ _ secondRun (Nat.le_refl _)]
    have increment : eval second (.op .add [localVar "occ",.const 1#64])=some (.val (.word (BitVec.ofNat 64 (occupied.val+1)))):=by
      simp [eval,second,first,evalHOLExact,evalListHOLExact,localVar,toExact,occupiedCell,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
    have incrementRun:=StateSteps.assign_execute second "occ" _ _ _ occupiedCell increment
    rw [evaluateHOLFiniteState_ite]
    by_cases bytesZero : bytes=0#64
    · simp [evalHOLExact,second,first,returnField,localVar,toExact,valueCell,Rlp.Item.result,bytesZero,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip,branchValueState,flagZero]
    · have test : eval second (.cmp .notEqual (returnField 2) (.const 0#64))=some (.val (.word 1#64)):=by
        simp [eval,second,first,evalHOLExact,returnField,localVar,toExact,valueCell,Rlp.Item.result,bytesZero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      simp only [eval] at test
      rw [test]
      simp only [show ¬(1#64 : BitVec 64)=0 from by decide,↓reduceIte]
      simpa only [branchValueState,if_pos flagZero,if_neg bytesZero] using incrementRun
  · rw [if_neg flagZero,branchValueState,if_neg flagZero]

theorem branch_value_state_view (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db node pointer header bytes flag : BitVec 64) (data : WitnessRecord.Description) (index : Fin 16) (occupied : Fin 17)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.branch node index occupied) :
    WitnessRecord.View (branchValueState source node pointer header bytes flag occupied) record db data := by
  unfold branchValueState
  split
  · have first:=view.branch_store source record db node (pointer+header) data index occupied 160 (by decide) (by decide) payload
    have second:=first.branch_store _ record db node bytes data index occupied 168 (by decide) (by decide) payload
    split
    · exact second
    · exact second.of_fields _ _ record db data rfl rfl
  · exact view

theorem branch_value_state_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node pointer header bytes flag : BitVec 64) (occupied : Fin 17)
    (occupiedCell : source.locals.lookup (ofString "occ")=some (.val (.word (BitVec.ofNat 64 occupied.val)))) :
    let target:=branchValueState source node pointer header bytes flag occupied
    target.locals.lookup (ofString "occ")=some (.val (.word (BitVec.ofNat 64 (branchValueOccupied bytes flag occupied)))) ∧
    target.globals=source.globals ∧ target.memaddrs=source.memaddrs ∧ target.clock=source.clock := by
  by_cases flagZero : flag=0#64 <;> by_cases bytesZero : bytes=0#64 <;>
    simp [branchValueState,branchValueOccupied,flagZero,bytesZero,occupiedCell,QueryBranch.bind,setVarHOLFinite,FUPDATE]

theorem branch_value_state_other (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node pointer header bytes flag : BitVec 64) (occupied : Fin 17) (name : String) (different : ofString "occ"≠ofString name) :
    (branchValueState source node pointer header bytes flag occupied).locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  unfold branchValueState
  split
  · split
    · rfl
    · exact bind_lookup_other _ "occ" name _ different
  · rfl

theorem branch_value_state_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node pointer header bytes flag : BitVec 64) (occupied : Fin 17) (query : BitVec 64)
    (away160 : query≠node+160#64) (away168 : query≠node+168#64) :
    (branchValueState source node pointer header bytes flag occupied).memory query=source.memory query := by
  unfold branchValueState
  split
  · split <;> simp [QueryBranch.bind,setVarHOLFinite,StoreWord.put,away160,away168]
  · rfl

theorem branch_value_occupied_bound (bytes flag : BitVec 64) (occupied : Fin 17) : branchValueOccupied bytes flag occupied≤17 := by
  have bound:=occupied.isLt
  unfold branchValueOccupied
  split <;> omega

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_value_writes_execute
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_value_state_view
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_value_state_fields
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_value_state_other
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_value_occupied_bound

#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_value_state_memory
