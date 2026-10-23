import InitECandidate.Solver.Mpt.InsertEnvironment
import InitECandidate.Solver.Mpt.InsertCost

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- Every genuine original251 caller, including the setter's assigned
root call. Its actual six-word ABI determines the reached callee entry;
no normal return or future graph is assumed to obtain this allowance. -/
theorem general_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap node key level length pointer size : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (valuesModel : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat) (member : graph.valid node)
    (before : level.toNat≤length.toNat) (bounded : length.toNat≤64)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size) (empty : property 0#64 0#64)
    (floor : nodeLower≤heap.toNat) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values node key length level pointer size)) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "_mpt_insert_node") arguments)).2.clock≤36791 := by
  obtain ⟨callee,called,nodeCell,keyCell,lengthCell,levelCell,pointerCell,sizeCell⟩:=environment source.code.lookup node key length level pointer size (original_code source.code installed)
  have priced:=body_cost (callEntryStateHOLFinite source callee) heap node key level length pointer size graph limit nodeLower pathLower property valuesModel regions disjoint paths pathRegions separated query member
    nodeCell keyCell levelCell lengthCell pointerCell sizeCell before bounded payload extra empty floor domain installed heapCell frontier aligned
  exact Input.ClockCost.call_current source destination (ofString "_mpt_insert_node") arguments _ body callee .one 36790 args called priced

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.general_call_cost
