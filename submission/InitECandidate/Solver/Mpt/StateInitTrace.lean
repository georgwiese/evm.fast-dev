import InitECandidate.Solver.Mpt.StateInitPrefixFields

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Every actual original state_init body run either stops within its one
prefix tick or reaches the genuine root-call suffix with initialized fields.
All physical entry premises remain explicit for the enclosing main proof. -/
theorem prefix_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap oldWs nodes root codes : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (ws : source.globals.lookup (ofString "ws")=some (.val (.word oldWs)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (nodesCell : source.locals.lookup (ofString "nodedb")=some (.val (.word nodes)))
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word root)))
    (codesCell : source.locals.lookup (ofString "codedb")=some (.val (.word codes)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena heap 40) (aligned : heap.toNat%8=0)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤1 ∨
      1≤source.clock ∧ evaluateHOLFiniteState (ready source heap nodes root codes) rootCall=(outcome,post) := by
  by_cases zero : source.clock=0
  · exact Or.inl (by omega)
  · have funded : 1≤source.clock := by omega
    rw [execute_prefix source heap oldWs nodes root codes installed ws heapCell nodesCell rootCell codesCell domain arena aligned funded] at run
    exact Or.inr ⟨funded,run⟩

/-- The original materializer arguments use the actual retained local words. -/
theorem root_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap nodes root codes : BitVec 64)
    (nodesCell : source.locals.lookup (ofString "nodedb")=some (.val (.word nodes)))
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word root))) :
    evalListHOLFinite (ready source heap nodes root codes) (h:=fun address=>Classical.propDecidable ((ready source heap nodes root codes).memaddrs address)) rootArguments=
      some [.val (.word nodes),.val (.word root)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,rootArguments,QueryBranch.localVar,ready,written,allocated,Input.putGlobal,PersistentAlloc.post,nodesCell,rootCell]

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.prefix_trace
#print axioms InitECandidate.Solver.Mpt.StateInit.root_arguments
