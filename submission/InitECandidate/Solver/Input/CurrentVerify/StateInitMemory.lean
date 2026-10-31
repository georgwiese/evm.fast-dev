import InitECandidate.Solver.Input.CurrentVerify.StateInitCost
import InitECandidate.Solver.Mpt.CurrentStateInitPrefixNormal

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Actual complete state_init normal execution returns the allocated
workspace and block records, restored scratch/frame cursors, a bounded
advancing heap and agreement on every earlier word. -/
theorem state_init_normal_context {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si : BitVec 64} {boundary : Nat}
    (inputs : StateInitInputs input source pointer si boundary) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source Mpt.StateInit.body=(some (.returned value),post)) :
    ∃ heap bs,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      value=.val (.word 0#64) ∧ Mpt.StateInit.MemoryContext post heap heap bs ∧
      Mpt.WitnessCore.Stack.StablePrefix source post heap.toNat := by
  obtain ⟨array,table,cap,root,codes,heap,start,length,arena,witness,image,heapCell,heapLower,heapUpper,aligned,inputBefore,tableBefore,nodesCell,rootCell,codesCell,nodeData,database,actualTable,actualTableBefore⟩:=inputs
  have actualNodes : source.locals.lookup (ofString "nodedb")=some (.val (.word nodeData.table)):=by
    rw [actualTable]
    exact nodesCell
  obtain ⟨answer,bs,records,priorMemory⟩:=Mpt.StateInit.current_body_normal_context nodeData source post heap root codes database
    actualTableBefore arena heapCell heapLower heapUpper aligned actualNodes rootCell codesCell value normal
  exact ⟨heap,bs,heapCell,answer,records,priorMemory⟩

/-- Earlier-memory and live-arena projections for callers that do not
need the actual workspace/block record ownership. -/
theorem state_init_normal_memory {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si : BitVec 64} {boundary : Nat}
    (inputs : StateInitInputs input source pointer si boundary) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source Mpt.StateInit.body=(some (.returned value),post)) :
    ∃ heap,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      value=.val (.word 0#64) ∧ CurrentStartup.ArenaState post ∧
      Mpt.WitnessCore.Stack.StablePrefix source post heap.toNat := by
  obtain ⟨heap,bs,cell,answer,physical,priorMemory⟩:=state_init_normal_context inputs value normal
  exact ⟨heap,cell,answer,physical.arena,priorMemory⟩

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.state_init_normal_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.state_init_normal_context
