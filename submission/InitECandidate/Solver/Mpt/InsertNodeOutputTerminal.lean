import InitECandidate.Solver.Mpt.InsertNodeOutput

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- Package a derived actual terminal mutation result with the unchanged
zeroed pending loop fields. This is a record constructor for dispatch joins. -/
theorem terminal_output (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (incoming key length level root heap : BitVec 64) (old : TrieWalk.Graph source.memory source.memaddrs)
    (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (nodeCell : source.locals.lookup (ofString "next_node")=some (.val (.word 0#64)))
    (slotCell : source.locals.lookup (ofString "next_slot")=some (.val (.word 0#64)))
    (levelCell : source.locals.lookup (ofString "next_level")=some (.val (.word 0#64)))
    (goCell : source.locals.lookup (ofString "go")=some (.val (.word 0#64)))
    (localsEq : target.locals=source.locals.update (ofString "r",.val (.word root)))
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be) (code : target.code=source.code)
    (heapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (arena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (grows : incoming.toNat≤heap.toNat)
    (olderMemory : ∀ query : BitVec 64,query.toNat<nodeLower → target.memory query=source.memory query)
    (oldPathFields : old.PathFields target.memory)
    (protectedMemory : ∀ address : BitVec 64,old.ProtectedWord address → address.toNat<incoming.toNat → target.memory address=source.memory address)
    (tags : ∀ node,old.valid node → node≠0#64 → wordAt target.memory node=wordAt source.memory node)
    (graph : TrieWalk.Graph target.memory target.memaddrs) (members : ∀ node,old.valid node → graph.valid node) (member : graph.valid root)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes target.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated) :
    Nonempty (NodeOutput source target old incoming key length level limit nodeLower pathLower property) := by
  have current (name : MlS) (other : name≠ofString "r") : target.locals.lookup name=source.locals.lookup name:=by
    rw [localsEq]
    simp [HolFiniteMapExact.update,FUPDATE,Ne.symm other]
  exact ⟨{
    root:=root
    nextNode:=0#64
    nextSlot:=0#64
    nextLevel:=0#64
    go:=0#64
    heap:=heap
    rootCell:=by rw [localsEq]; simp [HolFiniteMapExact.update,FUPDATE]
    nodeCell:=(current _ (by decide)).trans nodeCell
    slotCell:=(current _ (by decide)).trans slotCell
    levelCell:=(current _ (by decide)).trans levelCell
    goCell:=(current _ (by decide)).trans goCell
    stable:=by intro name notRoot notNode notSlot notLevel notGo; exact current name notRoot
    domain:=domain
    endian:=endian
    code:=code
    heapCell:=heapCell
    heapArena:=arena
    heapAligned:=aligned
    heapGrows:=grows
    olderPrefix:=olderMemory
    oldPathFields:=oldPathFields
    protectedMemory:=protectedMemory
    tags:=tags
    graph:=graph
    oldMember:=members
    activeRegistry:=by intro impossible; exact (impossible rfl).elim
    rootMember:=member
    nodeMember:=graph.null
    nextParent:=Or.inl rfl
    values:=values
    regions:=regions
    disjoint:=disjoint
    paths:=paths
    pathRegions:=pathRegions
    separated:=separated
    step:=Or.inl rfl
    query:=by intro impossible; exact (impossible rfl).elim }⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.terminal_output
