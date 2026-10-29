import InitECandidate.Solver.Mpt.InsertExtensionPrefixOutput
import InitECandidate.Solver.Mpt.InsertExtensionPrefixEntry
import InitECandidate.Solver.Mpt.InsertNodeOutputScope
import InitECandidate.Solver.Mpt.TrieGraphPathErase

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Join the genuine bounded read-only prefix comparison to both actual
extension choices and restore its temporary prefix binding. -/
theorem extension_prefix_scope_output (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap node key level length pointer size : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (pending : Pending source) (member : graph.valid node) (active : node≠0#64)
    (tag : wordAt source.memory node=2#64)
    (nodeClean : TrieWalk.Uncached source.memory node)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word (wordAt source.memory (node+32#64)))))
    (oldLengthCell : source.locals.lookup (ofString "sl")=some (.val (.word (wordAt source.memory (node+40#64)))))
    (before : level.toNat≤length.toNat) (bounded : length.toNat≤64)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (floor : nodeLower≤heap.toNat) (empty : property 0#64 0#64) (domain : source.memaddrs=InitE.ordinaryDomain)
    (installed : Input.OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (normal : evaluateHOLFiniteState source extensionPrefixScope=(none,target)) :
    Nonempty (NodeOutput source target graph heap key length level limit nodeLower pathLower property) := by
  obtain ⟨ready,inner,prefixLength,bound,prefixCell,localsEq,frame,price,continued,endpoint⟩:=extension_prefix_entry source target
    (wordAt source.memory (node+32#64)) (wordAt source.memory (node+40#64)) key level length bounded before installed segmentCell oldLengthCell keyCell levelCell lengthCell normal
  have memoryEq:=Input.LocalEffects.memory_of_erase source ready frame
  have domainEq:=congrArg PanSemStateFiniteExact.memaddrs frame
  have codeEq:=Input.LocalEffects.code_of_erase source ready frame
  have globalsEq:=congrArg PanSemStateFiniteExact.globals frame
  change ready.memaddrs=source.memaddrs at domainEq
  change ready.globals=source.globals at globalsEq
  obtain ⟨base,same,baseRegions,baseDisjoint,⟨baseValues⟩,basePaths,basePathRegions,baseSeparated⟩:=
    graph.after_erase source ready limit nodeLower heap.toNat pathLower heap.toNat property values regions disjoint paths pathRegions separated frame
  have currentQuery:=query.of_erase source ready graph base pathLower heap.toNat key length.toNat same frame
  have currentPending:=pending.after_scalar source ready "pl" prefixLength (by decide) (by decide) (by decide) (by decide) localsEq
  have current (name : MlS) (other : name≠ofString "pl") : ready.locals.lookup name=source.locals.lookup name:=by
    rw [localsEq]
    simp [HolFiniteMapExact.update,FUPDATE,Ne.symm other]
  have currentSegment : ready.locals.lookup (ofString "seg")=some (.val (.word (wordAt ready.memory (node+32#64)))):=by
    rw [memoryEq,current _ (by decide)]
    exact segmentCell
  have currentLength : ready.locals.lookup (ofString "sl")=some (.val (.word (wordAt ready.memory (node+40#64)))):=by
    rw [memoryEq,current _ (by decide)]
    exact oldLengthCell
  obtain ⟨output⟩:=extension_prefix_output ready inner heap node key level length prefixLength pointer size base limit nodeLower pathLower property
    baseValues baseRegions baseDisjoint basePaths basePathRegions baseSeparated currentQuery currentPending (by rw [same]; exact member) active (by rw [memoryEq]; exact tag)
    (by rw [memoryEq]; exact nodeClean)
    ((current _ (by decide)).trans nodeCell) ((current _ (by decide)).trans keyCell) ((current _ (by decide)).trans levelCell) ((current _ (by decide)).trans lengthCell)
    ((current _ (by decide)).trans pointerCell) ((current _ (by decide)).trans sizeCell) prefixCell currentSegment currentLength (by rw [memoryEq]; exact bound)
    before bounded (by rw [domainEq]; exact payload) extra floor empty (domainEq.trans domain) (by rw [codeEq]; exact installed)
    (by rw [globalsEq]; exact heapCell) frontier aligned continued
  rw [endpoint]
  exact output.restore_scope source ready inner graph base heap key length level limit nodeLower pathLower property "pl" prefixLength
    (by decide) (by decide) (by decide) (by decide) (by decide) localsEq frame same

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.extension_prefix_scope_output
