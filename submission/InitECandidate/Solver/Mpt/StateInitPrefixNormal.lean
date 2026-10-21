import InitECandidate.Solver.Mpt.StateInitAllocationTrace

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Every genuine normal state_init return passed its actual workspace
allocation and three mapped stores. Room and funding follow from the run;
the real root continuation is retained without a cost-only alternative. -/
theorem allocation_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap oldWs nodes root codes : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (ws : source.globals.lookup (ofString "ws")=some (.val (.word oldWs)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (nodesCell : source.locals.lookup (ofString "nodedb")=some (.val (.word nodes)))
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word root)))
    (codesCell : source.locals.lookup (ofString "codedb")=some (.val (.word codes)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (heapLower : 2701131776≤heap.toNat)
    (heapBound : heap.toNat≤33806089496) (aligned : heap.toNat%8=0)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    AllocatedBytes.Arena heap 40 ∧ evaluateHOLFiniteState (ready source heap nodes root codes) rootCall=(some (.returned returned),post) := by
  have safe : Input.LocalPrefix (ofString "state_root") allocate:=.globalCall _ _ _
  have firstRun:=normal
  rw [shapes.1] at firstRun
  obtain ⟨middle,allocRun,tailRun,rootFrame⟩:=safe.normal_continue source post afterAllocation returned firstRun
  obtain ⟨room,funded,same⟩:=PersistentAlloc.global_call_normal source middle "ws" oldWs heap 40#64 ws [.const 40#64] rfl
    (PersistentAlloc.original_code source.code installed) (Input.Trap.original_code source.code installed) heapCell heapBound allocRun
  have arena : AllocatedBytes.Arena heap 40:=⟨heapLower,room⟩
  have actual:=execute_prefix source heap oldWs nodes root codes installed ws heapCell nodesCell rootCell codesCell domain arena aligned funded
  exact ⟨arena,actual.symm.trans normal⟩

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.allocation_normal
