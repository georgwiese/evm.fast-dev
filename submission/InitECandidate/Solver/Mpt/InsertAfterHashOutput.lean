import InitECandidate.Solver.Mpt.InsertKindOutput
import InitECandidate.Solver.Mpt.InsertNodeOutputPrefix
import InitECandidate.Solver.Mpt.TrieInvalidateMemoryFrame
import InitECandidate.Solver.Mpt.TriePathFieldsMutation
import InitECandidate.Solver.Mpt.TrieProtectedMutation
import InitECandidate.Solver.Input.LoopNormal

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Join the actual ignored cache invalidation to all genuine node-kind
cases, retaining the caller's original graph and saved-parent tag frame. -/
theorem after_hash_output (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
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
    (normal : evaluateHOLFiniteState source afterHash=(none,target)) :
    Nonempty (NodeOutput source target graph heap key length level limit nodeLower pathLower property) := by
  rw [dispatch_shapes.2.2.1] at normal
  obtain ⟨middle,invalidated,continued⟩:=Input.sequence_none source target invalidateCall kindChoice normal
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "node"]=some [.val (.word node)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,nodeCell]
  rw [dispatch_shapes.2.2.2.2.1] at invalidated
  obtain ⟨middleEq,base,same,baseRegions,baseDisjoint,⟨baseValues⟩,basePaths,basePathRegions,baseSeparated,currentQuery⟩:=
    graph.invalidate_call_paths source middle node key length.toNat limit nodeLower heap.toNat pathLower heap.toNat property values regions disjoint paths pathRegions separated query
      member active [localVar "node"] args installed domain invalidated
  obtain ⟨oldMemory,oldTags⟩:=graph.invalidate_memory_frames source node nodeLower heap.toNat regions disjoint member active
  have localsEq : middle.locals=source.locals:=by rw [middleEq]; rfl
  have domainEq : middle.memaddrs=source.memaddrs:=by rw [middleEq]; rfl
  have endianEq : middle.be=source.be:=by rw [middleEq]; rfl
  have codeEq : middle.code=source.code:=by rw [middleEq]; rfl
  have globalsEq : middle.globals=source.globals:=by rw [middleEq]; rfl
  have currentPending : Pending middle:=⟨by rw [localsEq]; exact pending.node,by rw [localsEq]; exact pending.slot,
    by rw [localsEq]; exact pending.level,by rw [localsEq]; exact pending.go⟩
  have memory (query : BitVec 64) (before : query.toNat<nodeLower) : middle.memory query=source.memory query:=by rw [middleEq]; exact oldMemory query before
  have tags (current : BitVec 64) (live : graph.valid current) (nonzero : current≠0#64) : wordAt middle.memory current=wordAt source.memory current:=by rw [middleEq]; exact oldTags current live nonzero
  have currentTag : middle.locals.lookup (ofString "k")=some (.val (.word (wordAt middle.memory node))):=by
    rw [localsEq,tags node member active]
    exact tagCell
  obtain ⟨output⟩:=kind_output_normal middle target heap node key level length pointer size base limit nodeLower pathLower property
    baseValues baseRegions baseDisjoint basePaths basePathRegions baseSeparated currentQuery currentPending (by rw [same]; exact member) active
    (by rw [tags node member active]; exact notHash) currentTag
    (by rw [localsEq]; exact nodeCell) (by rw [localsEq]; exact keyCell) (by rw [localsEq]; exact levelCell) (by rw [localsEq]; exact lengthCell)
    (by rw [localsEq]; exact pointerCell) (by rw [localsEq]; exact sizeCell) before bounded (by rw [domainEq]; exact payload) extra floor empty (domainEq.trans domain)
    (by rw [codeEq]; exact installed) (by rw [globalsEq]; exact heapCell) frontier aligned continued
  exact output.prepend source middle target graph base heap heap key length level limit nodeLower pathLower property localsEq domainEq endianEq codeEq (Nat.le_refl _)
    memory tags (by intro current live; rw [same]; exact live) same
    (by rw [middleEq]; exact TrieWalk.Graph.PathFields.of_invalidate source node graph nodeLower heap.toNat regions disjoint member active)
    (by intro address safe _before; rw [middleEq]; exact safe.invalidate_memory source graph address node member active)

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.after_hash_output
