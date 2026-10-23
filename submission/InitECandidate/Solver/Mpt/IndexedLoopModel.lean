import InitECandidate.Solver.Mpt.IndexedSliceArray
import InitECandidate.Solver.Mpt.SetHeader
import InitECandidate.Solver.Input.MptWorkspaceBindings
import InitECandidate.Solver.WitnessRadix.KeccakOriginalEnvironment

namespace InitECandidate.Solver.Mpt.Indexed
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Current physical invariant of the unchanged indexed builder. The
fixed older rows and live map header survive every real update; the heap
and registered trie grow at their actual reached states. -/
structure LoopModel (source : PanSemStateFiniteExact 64 Guest.HostMemory) (m array : BitVec 64)
    (count cutoff limit : Nat) (slices : Nat→BitVec 64×BitVec 64) (property : BitVec 64→BitVec 64→Prop) where
  index : BitVec 64
  root : BitVec 64
  heap : BitVec 64
  indexCell : source.locals.lookup (ofString "i")=some (.val (.word index))
  countCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count)))
  mCell : source.locals.lookup (ofString "m")=some (.val (.word m))
  arrayCell : source.locals.lookup (ofString "slice_arr")=some (.val (.word array))
  bounded : index.toNat≤count
  countBound : count<2^64
  cutoffLower : 2713731432≤cutoff
  cutoffAligned : cutoff%8=0
  floor : cutoff≤heap.toNat
  headerAbove : cutoff≤m.toNat
  headerBefore : m.toNat+16≤heap.toNat
  domain : source.memaddrs=InitE.ordinaryDomain
  little : source.be=false
  installed : Input.OriginalCode.Installed source.code
  bindings : Input.Main.MptWorkspace.Bindings source
  hash : Keccak256.Environment source 2713714976#64 2713715176#64
  scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapArena : AllocatedBytes.Arena heap 0
  heapAligned : heap.toNat%8=0
  rows : SliceArray source array count cutoff limit slices property
  graph : TrieWalk.Graph source.memory source.memaddrs
  values : TrieWalk.Values graph limit property
  regions : graph.Regions cutoff heap.toNat
  disjoint : graph.Disjoint
  paths : graph.PathBytes source.be
  pathRegions : graph.PathRegions cutoff heap.toNat
  separated : graph.PathSeparated
  header : SetTrie.Header source graph m root 0#64
  empty : property 0#64 0#64

end InitECandidate.Solver.Mpt.Indexed
