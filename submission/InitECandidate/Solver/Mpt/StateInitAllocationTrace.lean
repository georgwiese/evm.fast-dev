import InitECandidate.Solver.Mpt.StateInitTrace
import InitECandidate.Solver.WitnessRadix.AllocationGlobalNormal
import InitECandidate.Solver.Input.ClockCostAssignedCurrent

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

theorem allocation_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source allocate).2.clock≤2 := by
  obtain ⟨callee,called,amountCell⟩ := PersistentAlloc.environment source.code.lookup 40#64 (PersistentAlloc.original_code source.code installed)
  exact Input.ClockCost.assigned_current source (some (.global,ofString "ws")) (ofString "alloc") [.const 40#64] _ PersistentAlloc.body callee .one 1 rfl called
    (PersistentAlloc.body_price source.code installed (callEntryStateHOLFinite source callee) rfl)

/-- The actual global allocation derives room for the workspace. Every
stopped allocator outcome has its own two-tick bound; no future room or
successful allocation is an entry premise. -/
theorem allocation_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap oldWs nodes root codes : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (ws : source.globals.lookup (ofString "ws")=some (.val (.word oldWs)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (nodesCell : source.locals.lookup (ofString "nodedb")=some (.val (.word nodes)))
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word root)))
    (codesCell : source.locals.lookup (ofString "codedb")=some (.val (.word codes)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (heapLower : 2701131776≤heap.toNat)
    (heapBound : heap.toNat≤33806089496) (aligned : heap.toNat%8=0)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤2 ∨ 1≤source.clock ∧ AllocatedBytes.Arena heap 40 ∧
      evaluateHOLFiniteState (ready source heap nodes root codes) rootCall=(outcome,post) := by
  have cost:=allocation_cost source installed
  rw [shapes.1,evaluateHOLFiniteState_seq_line780] at run
  generalize allocRun : evaluateHOLFiniteState source allocate=output at run cost
  obtain ⟨result,current⟩ := output
  cases result with
  | some result =>
    have endpoint : current=post := congrArg Prod.snd run
    exact Or.inl (by rwa [←endpoint])
  | none =>
    obtain ⟨room,funded,same⟩ := PersistentAlloc.global_call_normal source current "ws" oldWs heap 40#64 ws [.const 40#64] rfl
      (PersistentAlloc.original_code source.code installed) (Input.Trap.original_code source.code installed) heapCell heapBound allocRun
    have arena : AllocatedBytes.Arena heap 40 := ⟨heapLower,room⟩
    have newWs : (allocated source heap).globals.lookup (ofString "ws")=some (.val (.word heap)) := by
      simp [allocated,Input.putGlobal,HolFiniteMapExact.update,FUPDATE]
    change current=allocated source heap at same
    rw [same] at run
    simp only at run
    rw [stores_execute (allocated source heap) heap nodes root codes newWs nodesCell rootCell codesCell domain arena aligned] at run
    exact Or.inr ⟨funded,arena,run⟩

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.allocation_cost
#print axioms InitECandidate.Solver.Mpt.StateInit.allocation_trace
