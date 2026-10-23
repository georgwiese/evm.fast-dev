import InitECandidate.Solver.Mpt.DeleteDescentModel
import InitECandidate.Solver.Mpt.DeleteSetup

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- Real original top/res/go setup initializes both the descent model
and its empty physical return stack from current entry facts. It assumes
neither a future allocator return nor a successful descendant traversal. -/
theorem initial_descent_model (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor frame node key length level : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat) (member : graph.valid node)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (small : length.toNat≤64) (within : level.toNat≤length.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (scratch : Rlp.Validation.Arena source cursor frame) (scratchBefore : cursor.toNat≤DeleteFrame.ceiling)
    (floor : DeleteFrame.ceiling≤pathLower) (pathFloor : pathLower≤nodeLower) (nodeFloor : nodeLower≤heap.toNat)
    (little : source.be=false) (installed : Input.OriginalCode.Installed source.code) :
    ∃ initial : DescentModel (setup source) key length limit nodeLower pathLower property,
      initial.pending.heap=heap ∧ initial.pending.graph.valid=graph.valid ∧ initial.pending.frames=[] ∧ initial.go=1#64 := by
  obtain ⟨topCell,resultCell,goCell⟩:=setup_locals source
  let pending : UnwindModel (setup source) limit nodeLower pathLower property := {
    heap:=heap
    cursor:=cursor
    frame:=frame
    top:=0#64
    result:=0#64
    frames:=[]
    topCell:=topCell
    resultCell:=resultCell
    heapCell:=heapCell
    heapArena:=heapArena
    heapAligned:=heapAligned
    scratch:=scratch.of_fields source (setup source) cursor frame rfl rfl
    scratchBefore:=scratchBefore
    floor:=floor
    pathFloor:=pathFloor
    nodeFloor:=nodeFloor
    little:=little
    installed:=installed
    graph:=graph
    resultMember:=graph.null
    values:=values
    regions:=regions
    disjoint:=disjoint
    paths:=paths
    pathRegions:=pathRegions
    separated:=separated
    stack:=rfl
    parents:=by intro _ impossible; cases impossible
    bounded:=by decide }
  have current (name : String) (notTop : ofString "top"≠ofString name) (notResult : ofString "res"≠ofString name) (notGo : ofString "go"≠ofString name) :
      (setup source).locals.lookup (ofString name)=source.locals.lookup (ofString name):=setup_saved source (ofString name) notTop notResult notGo
  exact ⟨{
    pending:=pending
    node:=node
    level:=level
    go:=1#64
    keyCell:=(current "key" (by decide) (by decide) (by decide)).trans keyCell
    lengthCell:=(current "klen" (by decide) (by decide) (by decide)).trans lengthCell
    nodeCell:=(current "node" (by decide) (by decide) (by decide)).trans nodeCell
    levelCell:=(current "level" (by decide) (by decide) (by decide)).trans levelCell
    goCell:=goCell
    goTyped:=Or.inr rfl
    bounded:=small
    levelBound:=within
    depthBound:=by change 0≤level.toNat; omega
    nodeMember:=member
    query:=query },rfl,rfl,rfl,rfl⟩

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.initial_descent_model
