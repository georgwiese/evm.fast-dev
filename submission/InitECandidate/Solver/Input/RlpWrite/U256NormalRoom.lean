import InitECandidate.Solver.Input.CallPrefixNormalTrace
import InitECandidate.Solver.Input.CallPrefixAllocation
import InitECandidate.Solver.Input.CallPrefixGlobals
import InitECandidate.Solver.Input.OriginalRlpCodes
import InitECandidate.Solver.Input.GlobalEffectsScoped
import InitECandidate.Solver.Input.GlobalEffectsAtoms

namespace InitECandidate.Solver.Input.RlpWrite.U256Put
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def allocationActions : List CallPrefix.Action:=[
  .scoped (ofString "mark") .one (ofString "heap_mark") [],
  .scoped (ofString "tmp") .one (ofString "alloc") [.const 32#64]]

theorem body_allocations : body=CallPrefix.program allocationActions afterTemporary := by
  rw [body_shape]
  rfl

theorem allocation_never : NoReturn.Never (CallPrefix.program allocationActions .skip) := by
  exact NoReturn.scoped_call _ _ _ _ _ (NoReturn.scoped_call _ _ _ _ _ NoReturn.skip)

/-- The original wide writer's actual normal run supplies room for its
real32-byte temporary after its actual heap_mark, without entry funding. -/
theorem normal_room (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer))) (bounded : pointer.toNat≤33806089496)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    pointer.toNat+32≤33806089496 := by
  rw [body_allocations] at normal
  obtain ⟨current,inner,execution,endpoint,remaining⟩:=CallPrefix.normal_trace source post allocationActions afterTemporary value allocation_never normal
  obtain ⟨middle,first,next⟩ : ∃ middle,
      CallPrefix.Reaches source (.scoped (ofString "mark") .one (ofString "heap_mark") []) middle ∧
      CallPrefix.Execution middle [.scoped (ofString "tmp") .one (ofString "alloc") [.const 32#64]] current:=by
    cases execution with
    | step first next=>exact ⟨_,first,next⟩
  have preserved : GlobalEffects.Preserves (ofString "heap_ptr") source.code
      (CallPrefix.program [.scoped (ofString "mark") .one (ofString "heap_mark") []] .skip):=by
    apply GlobalEffects.scoped_body _ source.code _ _ _ _ _ [] HeapScope.markBody .one
      (OriginalRlp.heap_mark source.code installed)
    · rw [HeapScope.mark_shape]
      exact GlobalEffects.returned _ _ _
    · exact GlobalEffects.skip _ _
  have middleHeap:=(first.globals (ofString "heap_ptr") preserved).trans heap
  have middleInstalled : OriginalCode.Installed middle.code:=by rw [first.runtime.2.2.2.1]; exact installed
  have args : evalListHOLFinite middle (h:=fun address=>Classical.propDecidable (middle.memaddrs address)) [.const 32#64]=some (PersistentAlloc.values 32#64):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  exact (CallPrefix.Execution.alloc_next (source:=middle) (target:=current) (ofString "tmp") [.const 32#64] pointer 32#64 []
    middleInstalled args middleHeap bounded next).1

end InitECandidate.Solver.Input.RlpWrite.U256Put

#print axioms InitECandidate.Solver.Input.RlpWrite.U256Put.body_allocations
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Put.allocation_never
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Put.normal_room
