import InitECandidate.Solver.Mpt.NewProtected
import InitECandidate.Solver.Mpt.WitnessMaterializePathOutput
import InitECandidate.Solver.Mpt.WitnessCoreStablePrefix

namespace InitECandidate.Solver.Mpt.FromWitness
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open Input.Main.RunAttemptConstructors

/-- Complete map produced by the original witness wrapper, with the real
post-decoding header allocation and a retained immutable database band. -/
structure Output (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (value : ValueHOL 64) (db incoming flag : BitVec 64) where
  map : BitVec 64
  root : BitVec 64
  heap : BitVec 64
  answer : value=.val (.word map)
  domain : target.memaddrs=source.memaddrs
  endian : target.be=source.be
  code : target.code=source.code
  globalsNonHeap : HeapGlobals source target
  heapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapArena : AllocatedBytes.Arena heap 0
  heapAligned : heap.toNat%8=0
  mapGrows : incoming.toNat≤map.toNat
  headerBefore : map.toNat+16≤heap.toNat
  graph : TrieWalk.Graph target.memory target.memaddrs
  values : TrieWalk.Values graph 1024 (WitnessCore.WitnessValue db)
  regions : graph.Regions incoming.toNat heap.toNat
  disjoint : graph.Disjoint
  paths : graph.PathBytes target.be
  pathRegions : graph.PathRegions incoming.toNat heap.toNat
  separated : graph.PathSeparated
  header : SetTrie.Header target graph map root flag
  frozen : FrozenWitnessDatabases input (QueryBranch.bind target "db" db) incoming.toNat
  memory : WitnessCore.Stack.StablePrefix source target incoming.toNat

end InitECandidate.Solver.Mpt.FromWitness
