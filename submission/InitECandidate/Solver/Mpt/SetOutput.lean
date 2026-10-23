import InitECandidate.Solver.Mpt.SetMutationNormal

namespace InitECandidate.Solver.Mpt.SetTrie
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- Physical setter result after the actual root store. Other separated
caller words survive, and every protected caller word remains separated
from the final trie, including the map header whose root was updated. -/
structure Output (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64) (m : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (incoming key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop) (allowance : Nat) where
  root : BitVec 64
  heap : BitVec 64
  answer : value=.val (.word 0#64)
  rootStored : target.memory m=.word root
  domain : target.memaddrs=source.memaddrs
  endian : target.be=source.be
  code : target.code=source.code
  globalsNonHeap : HeapGlobals source target
  price : source.clock-target.clock≤allowance
  heapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapArena : AllocatedBytes.Arena heap 0
  heapAligned : heap.toNat%8=0
  grows : incoming.toNat≤heap.toNat
  fields : graph.PathFields target.memory
  next : TrieWalk.Graph target.memory target.memaddrs
  members : ∀ node,graph.valid node→next.valid node
  freshMembers : ∀ node,next.valid node→graph.valid node ∨ incoming.toNat≤node.toNat
  rootMember : next.valid root
  regions : next.Regions nodeLower heap.toNat
  disjoint : next.Disjoint
  values : TrieWalk.Values next limit property
  paths : next.PathBytes target.be
  pathRegions : next.PathRegions pathLower heap.toNat
  separated : next.PathSeparated
  protectedWords : ∀ address : BitVec 64,graph.ProtectedWord address →
    DeleteFrame.ceiling≤address.toNat → address.toNat<incoming.toNat → TrieWalk.PathWordAway key length.toNat address →
    (address≠m → target.memory address=source.memory address) ∧ next.ProtectedWord address

end InitECandidate.Solver.Mpt.SetTrie
