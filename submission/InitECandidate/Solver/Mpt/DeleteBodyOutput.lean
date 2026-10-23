import InitECandidate.Solver.Mpt.DeleteDescentOutput

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- Physical result of the unchanged deletion body. Its own scratch
records remain allocated until the original outer wrapper releases its
mark. Memory below the caller frame and above its incoming scratch
cursor survives; the free pool between those cursors may have changed. -/
structure BodyOutput (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (heap cursor frame : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop) where
  root : BitVec 64
  finalHeap : BitVec 64
  finalCursor : BitVec 64
  answer : value=.val (.word root)
  domain : target.memaddrs=source.memaddrs
  endian : target.be=source.be
  code : target.code=source.code
  globals : ∀ name,name≠ofString "heap_ptr"→name≠ofString "scratch_ptr"→target.globals.lookup name=source.globals.lookup name
  heapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap))
  heapArena : AllocatedBytes.Arena finalHeap 0
  heapAligned : finalHeap.toNat%8=0
  grows : heap.toNat≤finalHeap.toNat
  scratch : Rlp.Validation.Arena target finalCursor frame
  scratchDecreases : finalCursor.toNat≤cursor.toNat
  next : TrieWalk.Graph target.memory target.memaddrs
  members : ∀ node,graph.valid node→next.valid node
  freshMembers : ∀ node,next.valid node→graph.valid node ∨ heap.toNat≤node.toNat
  rootMember : next.valid root
  regions : next.Regions nodeLower finalHeap.toNat
  disjoint : next.Disjoint
  values : TrieWalk.Values next limit property
  paths : next.PathBytes target.be
  pathRegions : next.PathRegions pathLower finalHeap.toNat
  separated : next.PathSeparated
  fields : graph.PathFields target.memory
  memoryLow : ∀ query : BitVec 64,query.toNat<frame.toNat→target.memory query=source.memory query
  memoryBand : ∀ query : BitVec 64,cursor.toNat≤query.toNat→query.toNat<nodeLower→target.memory query=source.memory query

end InitECandidate.Solver.Mpt.DeleteBody
