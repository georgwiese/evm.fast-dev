import InitECandidate.Solver.Mpt.InsertLoopModel
import InitECandidate.Solver.Mpt.InsertSetup

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- The real original result/slot/go initialization establishes the loop
model for any genuine bounded current key level and registered input root. -/
theorem initial_loop_model (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap node key level length pointer size : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat) (member : graph.valid node)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (before : level.toNat≤length.toNat) (bounded : length.toNat≤64)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (floor : nodeLower≤heap.toNat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) :
    ∃ initial : LoopModel (setup source) key length pointer size limit nodeLower pathLower property,initial.graph.valid=graph.valid ∧ initial.heap=heap := by
  have current (name : String) (notResult : ofString "result"≠ofString name) (notSlot : ofString "slot"≠ofString name) (notGo : ofString "go"≠ofString name) :
      (setup source).locals.lookup (ofString name)=source.locals.lookup (ofString name):=setup_saved source (ofString name) notResult notSlot notGo
  obtain ⟨resultCell,slotCell,goCell⟩:=setup_locals source
  exact ⟨{
    node:=node
    slot:=0#64
    result:=0#64
    level:=level
    go:=1#64
    heap:=heap
    keyCell:=(current _ (by decide) (by decide) (by decide)).trans keyCell
    lengthCell:=(current _ (by decide) (by decide) (by decide)).trans lengthCell
    pointerCell:=(current _ (by decide) (by decide) (by decide)).trans pointerCell
    sizeCell:=(current _ (by decide) (by decide) (by decide)).trans sizeCell
    nodeCell:=(current _ (by decide) (by decide) (by decide)).trans nodeCell
    slotCell:=slotCell
    resultCell:=resultCell
    levelCell:=(current _ (by decide) (by decide) (by decide)).trans levelCell
    goCell:=goCell
    goTyped:=Or.inr rfl
    activeBound:=fun _=>before
    bounded:=bounded
    domain:=domain
    installed:=installed
    heapCell:=heapCell
    heapArena:=frontier
    heapAligned:=aligned
    floor:=floor
    payload:=payload
    graph:=graph
    nodeMember:=member
    resultMember:=graph.null
    parentSlot:=Or.inl rfl
    values:=values
    regions:=regions
    disjoint:=disjoint
    paths:=paths
    pathRegions:=pathRegions
    separated:=separated
    query:=fun _=>query },rfl,rfl⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.initial_loop_model
