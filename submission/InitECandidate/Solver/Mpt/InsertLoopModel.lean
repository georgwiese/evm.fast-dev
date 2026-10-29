import InitECandidate.Solver.Mpt.InsertNodeOutput
import InitECandidate.Solver.Input.OriginalCode

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- Current original insertion-loop state. Active states protect the full
key buffer and bound the consumed length; a stopped loop retains the real
registered result and heap without requiring another key read. -/
structure LoopModel (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (key length pointer size : BitVec 64) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop) where
  node : BitVec 64
  slot : BitVec 64
  result : BitVec 64
  level : BitVec 64
  go : BitVec 64
  heap : BitVec 64
  keyCell : source.locals.lookup (ofString "key")=some (.val (.word key))
  lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length))
  pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer))
  sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size))
  nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))
  slotCell : source.locals.lookup (ofString "slot")=some (.val (.word slot))
  resultCell : source.locals.lookup (ofString "result")=some (.val (.word result))
  levelCell : source.locals.lookup (ofString "level")=some (.val (.word level))
  goCell : source.locals.lookup (ofString "go")=some (.val (.word go))
  goTyped : go=0#64 ∨ go=1#64
  activeBound : go≠0#64 → level.toNat≤length.toNat
  bounded : length.toNat≤64
  domain : source.memaddrs=InitE.ordinaryDomain
  installed : Input.OriginalCode.Installed source.code
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapArena : AllocatedBytes.Arena heap 0
  heapAligned : heap.toNat%8=0
  floor : nodeLower≤heap.toNat
  payload : TrieWalk.Payload source.memaddrs pointer size limit
  graph : TrieWalk.Graph source.memory source.memaddrs
  nodeMember : graph.valid node
  resultMember : graph.valid result
  resultUncached : TrieWalk.Uncached source.memory result
  parentSlot : graph.ParentSlot slot
  values : TrieWalk.Values graph limit property
  regions : graph.Regions nodeLower heap.toNat
  disjoint : graph.Disjoint
  paths : graph.PathBytes source.be
  pathRegions : graph.PathRegions pathLower heap.toNat
  separated : graph.PathSeparated
  query : go≠0#64 → graph.PathBuffer source.be pathLower heap.toNat key length.toNat

end InitECandidate.Solver.Mpt.Insert
