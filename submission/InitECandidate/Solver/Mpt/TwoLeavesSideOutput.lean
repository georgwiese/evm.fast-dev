import InitECandidate.Solver.Mpt.TriePathBuffer
import InitECandidate.Solver.Mpt.TrieProtectedGrowth
import InitECandidate.Solver.Mpt.TrieCacheMutation

namespace InitECandidate.Solver.Mpt.TwoLeaves
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- Current physical output of either original branch-building side. -/
structure SideOutput (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (old : TrieWalk.Graph source.memory source.memaddrs) (incoming key length otherKey otherLength branch : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop) where
  heap : BitVec 64
  locals : post.locals=source.locals
  domain : post.memaddrs=source.memaddrs
  endian : post.be=source.be
  code : post.code=source.code
  heapCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapArena : AllocatedBytes.Arena heap 0
  heapAligned : heap.toNat%8=0
  heapGrows : incoming.toNat≤heap.toNat
  branchTag : wordAt post.memory branch=3#64
  olderPrefix : ∀ query : BitVec 64,query.toNat<branch.toNat → post.memory query=source.memory query
  cacheFrame : old.CacheFrame post.memory
  graph : TrieWalk.Graph post.memory post.memaddrs
  oldMember : ∀ node,old.valid node → graph.valid node
  branchMember : graph.valid branch
  values : TrieWalk.Values graph limit property
  regions : graph.Regions nodeLower heap.toNat
  disjoint : graph.Disjoint
  paths : graph.PathBytes post.be
  pathRegions : graph.PathRegions pathLower heap.toNat
  separated : graph.PathSeparated
  buffer : graph.PathBuffer post.be pathLower heap.toNat key length.toNat
  otherBuffer : graph.PathBuffer post.be pathLower heap.toNat otherKey otherLength.toNat

/-- The two-leaf builder additionally records real fresh-node provenance
and caller-word protection for its one newly borrowed input suffix. -/
structure ProtectedSideOutput (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (old : TrieWalk.Graph source.memory source.memaddrs) (incoming key length otherKey otherLength branch : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    extends SideOutput source post old incoming key length otherKey otherLength branch limit nodeLower pathLower property where
  freshMembers : ∀ node,graph.valid node → old.valid node ∨ incoming.toNat≤node.toNat
  protectedGraph : ∀ query : BitVec 64,old.ProtectedWord query → query.toNat<incoming.toNat →
    TrieWalk.PathWordAway key length.toNat query → graph.ProtectedWord query

end InitECandidate.Solver.Mpt.TwoLeaves
