import InitECandidate.Solver.Mpt.InsertEmptyLeaf
import InitECandidate.Solver.Input.CallPrefixLocalResult

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def withResult (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key length pointer size : BitVec 64):=
  bind (leafResult source heap key length pointer size) "result" heap
def withNode (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key length pointer size : BitVec 64):=
  bind (withResult source heap key length pointer size) "node" 0#64
def withSlot (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key length pointer size : BitVec 64):=
  bind (withNode source heap key length pointer size) "slot" 0#64
def finished (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key length pointer size : BitVec 64):=
  bind (withSlot source heap key length pointer size) "level" 0#64

set_option maxHeartbeats 1000000 in
theorem after_choice_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key length pointer size : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word 0#64)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word 0#64))) :
    evaluateHOLFiniteState (leafResult source heap key length pointer size) afterChoice=(none,finished source heap key length pointer size) := by
  let entry:=leafResult source heap key length pointer size
  have resultCell : entry.locals.lookup (ofString "result")=some (.val (.word 0#64)):=by
    simp [entry,leafResult,firstDispatch,dispatchEntry,prepared,setup,decClockHOLFinite,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
  have resultRead : eval entry (localVar "r")=some (.val (.word heap)):=by
    simp [eval,localVar,evalHOLExact,toExact,entry,leafResult,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have setResult:=StateSteps.assign_execute entry "result" (localVar "r") 0#64 heap resultCell resultRead
  have testRead : eval entry (.cmp .equal (localVar "slot") (.const 0#64))=some (.val (.word 1#64)):=by
    simp [eval,localVar,evalHOLExact,toExact,entry,leafResult,firstDispatch,dispatchEntry,prepared,setup,decClockHOLFinite,QueryBranch.bind,
      PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have choose : evaluateHOLFiniteState entry chooseResult=(none,withResult source heap key length pointer size):=by
    rw [chooseResult,evaluateHOLFiniteState_ite]
    simp only [eval] at testRead
    rw [testRead]
    simp only
    rw [if_neg (show (1#64 : BitVec 64)≠0 from by decide)]
    exact setResult
  have nodeOld : (withResult source heap key length pointer size).locals.lookup (ofString "node")=some (.val (.word 0#64)):=by
    simpa [withResult,leafResult,firstDispatch,dispatchEntry,prepared,setup,decClockHOLFinite,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using nodeCell
  have nodeRead : eval (withResult source heap key length pointer size) (localVar "next_node")=some (.val (.word 0#64)):=by
    simp [eval,localVar,evalHOLExact,toExact,withResult,leafResult,firstDispatch,dispatchEntry,prepared,setup,decClockHOLFinite,QueryBranch.bind,
      PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
  have nodeRun:=StateSteps.assign_execute (withResult source heap key length pointer size) "node" (localVar "next_node") 0#64 0#64 nodeOld nodeRead
  change evaluateHOLFiniteState (withResult source heap key length pointer size) clearNode=(none,withNode source heap key length pointer size) at nodeRun
  have slotOld : (withNode source heap key length pointer size).locals.lookup (ofString "slot")=some (.val (.word 0#64)):=by
    simp [withNode,withResult,leafResult,firstDispatch,dispatchEntry,prepared,setup,decClockHOLFinite,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
  have slotRead : eval (withNode source heap key length pointer size) (localVar "next_slot")=some (.val (.word 0#64)):=by
    simp [eval,localVar,evalHOLExact,toExact,withNode,withResult,leafResult,firstDispatch,dispatchEntry,prepared,setup,decClockHOLFinite,QueryBranch.bind,
      PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
  have slotRun:=StateSteps.assign_execute (withNode source heap key length pointer size) "slot" (localVar "next_slot") 0#64 0#64 slotOld slotRead
  change evaluateHOLFiniteState (withNode source heap key length pointer size) clearSlot=(none,withSlot source heap key length pointer size) at slotRun
  have levelOld : (withSlot source heap key length pointer size).locals.lookup (ofString "level")=some (.val (.word 0#64)):=by
    simpa [withSlot,withNode,withResult,leafResult,firstDispatch,dispatchEntry,prepared,setup,decClockHOLFinite,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using levelCell
  have levelRead : eval (withSlot source heap key length pointer size) (localVar "next_level")=some (.val (.word 0#64)):=by
    simp [eval,localVar,evalHOLExact,toExact,withSlot,withNode,withResult,leafResult,firstDispatch,dispatchEntry,prepared,setup,decClockHOLFinite,QueryBranch.bind,
      PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
  have levelRun:=StateSteps.assign_execute (withSlot source heap key length pointer size) "level" (localVar "next_level") 0#64 0#64 levelOld levelRead
  change evaluateHOLFiniteState (withSlot source heap key length pointer size) clearLevel=(none,finished source heap key length pointer size) at levelRun
  rw [after_choice_shape,evaluateHOLFiniteState_seq_line780,choose]
  simp only
  rw [evaluateHOLFiniteState_seq_line780,nodeRun]
  simp only
  rw [evaluateHOLFiniteState_seq_line780,slotRun]
  simp only
  exact levelRun

theorem finished_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key length pointer size : BitVec 64) :
    (finished source heap key length pointer size).locals.lookup (ofString "go")=some (.val (.word 0#64)) ∧
      (finished source heap key length pointer size).locals.lookup (ofString "result")=some (.val (.word heap)) := by
  simp [finished,withSlot,withNode,withResult,leafResult,firstDispatch,dispatchEntry,prepared,setup,decClockHOLFinite,QueryBranch.bind,
    PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]

theorem finished_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key length pointer size : BitVec 64) :
    (finished source heap key length pointer size).clock=source.clock-3 := by
  simp only [finished,withSlot,withNode,withResult,leafResult,firstDispatch,dispatchEntry,prepared,setup,decClockHOLFinite,QueryBranch.bind,
    PersistentAlloc.post,setVarHOLFinite,Nat.sub_sub]

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.after_choice_shape
#print axioms InitECandidate.Solver.Mpt.Insert.after_choice_execute
#print axioms InitECandidate.Solver.Mpt.Insert.finished_locals
#print axioms InitECandidate.Solver.Mpt.Insert.finished_clock
