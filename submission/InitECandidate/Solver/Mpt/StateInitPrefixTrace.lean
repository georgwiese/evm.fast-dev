import InitECandidate.Solver.Mpt.StateInitPrefix
import InitECandidate.Solver.WitnessRadix.AllocationGlobalNormal
import InitECandidate.Solver.Input.ClockCostAssignedBody

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The original state initializer either stops during its real workspace
allocation, or reaches the actual root call after the three mapped stores.
Normal allocation derives room and the new ws global, at any incoming clock. -/
theorem root_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap nodes root codes : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (nodesCell : source.locals.lookup (ofString "nodedb")=some (.val (.word nodes)))
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word root)))
    (codesCell : source.locals.lookup (ofString "codedb")=some (.val (.word codes)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤2 ∨
      heap.toNat+40≤2952790016 ∧ 1≤source.clock ∧
      evaluateHOLFiniteState (ready source heap nodes root codes) rootCall=(outcome,post) := by
  have price : source.clock-(evaluateHOLFiniteState source allocate).2.clock≤2 := by
    exact Input.ClockCost.assigned_body source.code (some (.global,ofString "ws")) (ofString "alloc") [.const 40#64]
      PersistentAlloc.formals PersistentAlloc.body .one 1 (PersistentAlloc.original_code source.code installed)
      (PersistentAlloc.body_price source.code installed) source rfl
  rw [shapes.1,evaluateHOLFiniteState_seq_line780] at run
  generalize allocationRun : evaluateHOLFiniteState source allocate=output at price run
  obtain ⟨allocationResult,allocatedPost⟩ := output
  change source.clock-allocatedPost.clock≤2 at price
  cases allocationResult with
  | some result=>
    have clock : allocatedPost.clock=post.clock := congrArg (fun output=>output.2.clock) run
    exact Or.inl (by omega)
  | none=>
    have normal : evaluateHOLFiniteState source (.call (some (some (.global,ofString "ws"),none)) (ofString "alloc") [.const 40#64])=(none,allocatedPost) := allocationRun
    obtain ⟨room,funded,allocatedEq⟩ := PersistentAlloc.global_call_normal_any source allocatedPost "ws" heap 40#64 [.const 40#64] rfl
      (PersistentAlloc.original_code source.code installed) (Input.Trap.original_code source.code installed) heapCell heapUpper normal
    have memoryArena : AllocatedBytes.Arena heap 40 := ⟨heapLower,by change heap.toNat+40≤2952790016 at room; omega⟩
    have newWs : (allocated source heap).globals.lookup (ofString "ws")=some (.val (.word heap)) :=
      Input.putGlobal.lookup_same _ _ _
    have mappedStores := stores_execute (allocated source heap) heap nodes root codes newWs nodesCell rootCell codesCell domain memoryArena aligned
    have allocatedSame : allocatedPost=allocated source heap := allocatedEq
    rw [allocatedSame] at run
    change evaluateHOLFiniteState (allocated source heap) afterAllocation=(outcome,post) at run
    rw [mappedStores] at run
    exact Or.inr ⟨room,funded,run⟩

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.root_trace
