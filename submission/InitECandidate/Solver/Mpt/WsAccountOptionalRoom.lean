import InitECandidate.Solver.Mpt.WsAccountOptionalProgram
import InitECandidate.Solver.Mpt.WsAccountLeafCall
import InitECandidate.Solver.Mpt.WsAccountLeafRoom
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Mpt.WsAccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Derive temporary lookup allocation room from the actual complete normal
provider before imposing any hash buffer mapping, graph or payload model. -/
theorem body_room (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (addr heap : BitVec 64)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word addr)))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) : heap.toNat+32≤33806089496 := by
  rw [body_shape] at normal
  obtain ⟨callee,called,addrCell⟩ := WsAccountLeaf.environment source.code.lookup addr (WsAccountLeaf.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "addr"]=some (WsAccountLeaf.values addr) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,addressCell,WsAccountLeaf.values]
  obtain ⟨positive,target,answer,inner,bodyRun,checked,tailRun,restored⟩ := Input.CallNormal.scoped_normal source post "leaf" TrieWalk.resultShape
    (ofString "ws_account_leaf") [localVar "addr"] _ WsAccountLeaf.body afterLeaf callee TrieWalk.resultShape args called returned normal
  exact WsAccountLeaf.body_room (callEntryStateHOLFinite source callee) target heap heapGlobal heapBound installed answer bodyRun

end InitECandidate.Solver.Mpt.WsAccountOptional

#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.body_room
