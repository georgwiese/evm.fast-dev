import InitECandidate.Solver.Mpt.InsertEmptyNodeOutput
import InitECandidate.Solver.Mpt.InsertNonemptyOutput

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Every genuine original insertion node choice supplies its current
root, child/parent slots, actual heap and complete graph/path models. Any
continuing choice consumes at least one more of the actual key nibbles. -/
theorem node_choice_output (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap node key level length pointer size : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (pending : Pending source) (member : graph.valid node)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (before : level.toNat≤length.toNat) (bounded : length.toNat≤64)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (floor : nodeLower≤heap.toNat) (empty : property 0#64 0#64) (domain : source.memaddrs=InitE.ordinaryDomain)
    (installed : Input.OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (normal : evaluateHOLFiniteState source nodeChoice=(none,target)) :
    Nonempty (NodeOutput source target graph heap key length level limit nodeLower pathLower property) := by
  by_cases zero : node=0#64
  · have currentNode : source.locals.lookup (ofString "node")=some (.val (.word 0#64)):=by simpa only [zero] using nodeCell
    have selected:=empty_choice source currentNode
    exact empty_node_output source target heap key level length pointer size graph limit nodeLower pathLower property
      values regions disjoint paths pathRegions separated query pending keyCell levelCell lengthCell pointerCell sizeCell before bounded payload extra floor empty domain installed heapCell frontier aligned
      (selected.symm.trans normal)
  · have selected : evaluateHOLFiniteState source nodeChoice=evaluateHOLFiniteState source nonemptyChoice:=by
      rw [node_choice_shape,evaluateHOLFiniteState_ite]
      simp [nodeTest,evalHOLExact,toExact,localVar,nodeCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    exact nonempty_output_normal source target heap node key level length pointer size graph limit nodeLower pathLower property
      values regions disjoint paths pathRegions separated query pending member zero nodeCell keyCell levelCell lengthCell pointerCell sizeCell before bounded payload extra floor empty domain installed heapCell frontier aligned
      (selected.symm.trans normal)

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.node_choice_output
