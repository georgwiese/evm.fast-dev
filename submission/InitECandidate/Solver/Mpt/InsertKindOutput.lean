import InitECandidate.Solver.Mpt.InsertLeafOutput
import InitECandidate.Solver.Mpt.InsertExtensionOutput
import InitECandidate.Solver.Mpt.InsertBranchOutput

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Join every genuine non-hash node-kind choice in original251. -/
theorem kind_output_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap node key level length pointer size : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (pending : Pending source) (member : graph.valid node) (active : node≠0#64)
    (notHash : wordAt source.memory node≠0#64)
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word (wordAt source.memory node))))
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
    (normal : evaluateHOLFiniteState source kindChoice=(none,target)) :
    Nonempty (NodeOutput source target graph heap key length level limit nodeLower pathLower property) := by
  by_cases leaf : wordAt source.memory node=1#64
  · have selected : evaluateHOLFiniteState source kindChoice=evaluateHOLFiniteState source insertLeafCall:=by
      rw [dispatch_shapes.2.2.2.2.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,tagCell,leaf,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    exact leaf_output_normal source target heap node key level length pointer size graph limit nodeLower pathLower property
      values regions disjoint paths pathRegions separated query pending member active leaf nodeCell keyCell levelCell lengthCell pointerCell sizeCell
      before bounded payload extra floor empty domain installed heapCell frontier aligned (selected.symm.trans normal)
  · have selected : evaluateHOLFiniteState source kindChoice=evaluateHOLFiniteState source extensionChoice:=by
      rw [dispatch_shapes.2.2.2.2.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,tagCell,leaf,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have continued:=selected.symm.trans normal
    by_cases extension : wordAt source.memory node=2#64
    · have selected : evaluateHOLFiniteState source extensionChoice=evaluateHOLFiniteState source extensionScope:=by
        rw [dispatch_shapes.2.2.2.2.2.2.2,evaluateHOLFiniteState_ite]
        simp [evalHOLExact,toExact,localVar,tagCell,extension,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      exact extension_output_normal source target heap node key level length pointer size graph limit nodeLower pathLower property
        values regions disjoint paths pathRegions separated query pending member active extension nodeCell keyCell levelCell lengthCell pointerCell sizeCell
        before bounded payload extra floor empty domain installed heapCell frontier aligned (selected.symm.trans continued)
    · have selected : evaluateHOLFiniteState source extensionChoice=evaluateHOLFiniteState source branchChoice:=by
        rw [dispatch_shapes.2.2.2.2.2.2.2,evaluateHOLFiniteState_ite]
        simp [evalHOLExact,toExact,localVar,tagCell,extension,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      exact branch_output_normal source target heap node key level length pointer size graph limit nodeLower pathLower property
        values regions disjoint paths pathRegions separated query pending member active notHash leaf extension nodeCell keyCell levelCell lengthCell pointerCell sizeCell
        before bounded payload extra heapCell frontier aligned (selected.symm.trans continued)

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.kind_output_normal
