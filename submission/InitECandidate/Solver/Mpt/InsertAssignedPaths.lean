import InitECandidate.Solver.Mpt.InsertNormal
import InitECandidate.Solver.Mpt.InsertGeneralCallCost
import InitECandidate.Solver.Mpt.InsertGlobals
import InitECandidate.Solver.Input.AssignedCallKnown

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- Physical result of the actual assigned original251 caller. Caller
headers may lie between old and fresh nodes; their frames follow from
separation, rather than from a global order of node addresses. -/
structure Output (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root incoming key length : BitVec 64) (old : TrieWalk.Graph source.memory source.memaddrs)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop) where
  heap : BitVec 64
  domain : target.memaddrs=source.memaddrs
  endian : target.be=source.be
  code : target.code=source.code
  heapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapArena : AllocatedBytes.Arena heap 0
  heapAligned : heap.toNat%8=0
  heapGrows : incoming.toNat≤heap.toNat
  globalsNonHeap : HeapGlobals source target
  price : source.clock-target.clock≤36791
  olderPrefix : ∀ address : BitVec 64,address.toNat<nodeLower → target.memory address=source.memory address
  oldPathFields : old.PathFields target.memory
  protectedMemory : ∀ address : BitVec 64,old.ProtectedWord address → address.toNat<incoming.toNat → target.memory address=source.memory address
  next : TrieWalk.Graph target.memory target.memaddrs
  members : ∀ node,old.valid node → next.valid node
  freshMembers : ∀ node,next.valid node → old.valid node ∨ incoming.toNat≤node.toNat
  protectedGraph : ∀ address : BitVec 64,old.ProtectedWord address → address.toNat<incoming.toNat →
    TrieWalk.PathWordAway key length.toNat address → next.ProtectedWord address
  rootMember : next.valid root
  rootUncached : TrieWalk.Uncached target.memory root
  values : TrieWalk.Values next limit property
  regions : next.Regions nodeLower heap.toNat
  disjoint : next.Disjoint
  paths : next.PathBytes target.be
  pathRegions : next.PathRegions pathLower heap.toNat
  separated : next.PathSeparated

/-- Derive the real callee entry, actual returned root and complete
caller-restored physical output for any registered incoming root and
bounded current query. No future successful helper or graph is supplied. -/
theorem assigned_path_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
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
    (name : MlS) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values node key length level pointer size))
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString "_mpt_insert_node") arguments)=(none,target)) :
    ∃ root : BitVec 64,target.locals=source.locals.update (name,.val (.word root)) ∧
      Nonempty (Output source target root heap key length graph limit nodeLower pathLower property) := by
  obtain ⟨callee,called,nodeCell,keyCell,lengthCell,levelCell,pointerCell,sizeCell⟩:=environment source.code.lookup node key length level pointer size (original_code source.code installed)
  obtain ⟨_funded,childTarget,returned,run,endpoint⟩:=Input.CallNormal.local_known source target name (ofString "_mpt_insert_node") arguments _ body callee .one args called normal
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨domainEq,endianEq,codeEq,memory,_tags,root,finalHeap,answer,finalHeapCell,finalArena,finalAligned,grows,next,members,rootMember,nextRegions,nextDisjoint,⟨nextValues⟩,nextPaths,nextPathRegions,nextSeparated,fields,protectedWords,provenance,protection,rootClean⟩:=
    body_path_normal entry heap node key level length pointer size graph limit nodeLower pathLower property valuesModel regions disjoint paths pathRegions separated query member
      nodeCell keyCell levelCell lengthCell pointerCell sizeCell before bounded payload extra empty floor domain installed heapCell frontier aligned childTarget returned run
  have kept:=heap_globals entry installed
  rw [run] at kept
  have priced:=general_call_cost source heap node key level length pointer size graph limit nodeLower pathLower property valuesModel regions disjoint paths pathRegions separated query member
    before bounded payload extra empty floor domain installed heapCell frontier aligned (some (some name)) arguments args
  change source.clock-(evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString "_mpt_insert_node") arguments)).2.clock≤36791 at priced
  rw [normal] at priced
  have spent : source.clock-childTarget.clock≤36791:=by rw [endpoint] at priced; exact priced
  rw [endpoint,answer]
  exact ⟨root,rfl,⟨{
    heap:=finalHeap
    domain:=domainEq
    endian:=endianEq
    code:=codeEq
    heapCell:=finalHeapCell
    heapArena:=finalArena
    heapAligned:=finalAligned
    heapGrows:=grows
    globalsNonHeap:=kept
    price:=spent
    olderPrefix:=memory
    oldPathFields:=fields
    protectedMemory:=protectedWords
    next:=next
    members:=members
    freshMembers:=provenance
    protectedGraph:=protection
    rootMember:=rootMember
    rootUncached:=rootClean
    values:=nextValues
    regions:=nextRegions
    disjoint:=nextDisjoint
    paths:=nextPaths
    pathRegions:=nextPathRegions
    separated:=nextSeparated }⟩⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.assigned_path_normal
