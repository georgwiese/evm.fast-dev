import InitECandidate.Solver.Mpt.StateInitPrefixTrace

namespace InitECandidate.Solver.Mpt.StateInit
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- An actual enclosing normal return must pass the same real workspace
allocation and stores. Its request room and funding are derived from that
execution; a cheap failed prefix is excluded rather than treated as success. -/
theorem current_root_normal_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap nodes root codes : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (nodesCell : source.locals.lookup (ofString "nodedb")=some (.val (.word nodes)))
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word root)))
    (codesCell : source.locals.lookup (ofString "codedb")=some (.val (.word codes)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    heap.toNat+40≤2952790016 ∧ 1≤source.clock ∧
      evaluateHOLFiniteState (ready source heap nodes root codes) rootCall=(some (.returned value),post) := by
  rw [shapes.1] at normal
  have safe : LocalPrefix (ofString "nodedb") allocate:=.globalCall _ _ _
  obtain ⟨allocatedPost,allocationRun,continued,preserved⟩:=safe.normal_continue source post afterAllocation value normal
  obtain ⟨room,funded,allocatedEq⟩:=PersistentAlloc.global_call_normal_any source allocatedPost "ws" heap 40#64 [.const 40#64] rfl
    (PersistentAlloc.original_code source.code installed) (Input.Trap.original_code source.code installed) heapCell heapUpper allocationRun
  have nodeArena : AllocatedBytes.Arena heap 40:=⟨heapLower,by change heap.toNat+40≤2952790016 at room; omega⟩
  have wsCell : (allocated source heap).globals.lookup (ofString "ws")=some (.val (.word heap)):=putGlobal.lookup_same _ _ _
  have actualStores:=stores_execute (allocated source heap) heap nodes root codes wsCell nodesCell rootCell codesCell domain nodeArena aligned
  rw [allocatedEq] at continued
  change evaluateHOLFiniteState (allocated source heap) afterAllocation=(some (.returned value),post) at continued
  rw [actualStores] at continued
  exact ⟨room,funded,continued⟩

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.current_root_normal_trace
