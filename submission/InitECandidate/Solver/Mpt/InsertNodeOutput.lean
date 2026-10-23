import InitECandidate.Solver.Mpt.TrieParentSlot
import InitECandidate.Solver.Mpt.TriePathBuffer

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- Current physical output of one original insertion dispatch, before
its real parent store. Continuing cases carry a strictly consumed key;
terminal cases require no later query read. -/
structure NodeOutput (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (old : TrieWalk.Graph source.memory source.memaddrs) (incoming key length level : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop) where
  root : BitVec 64
  nextNode : BitVec 64
  nextSlot : BitVec 64
  nextLevel : BitVec 64
  go : BitVec 64
  heap : BitVec 64
  rootCell : target.locals.lookup (ofString "r")=some (.val (.word root))
  nodeCell : target.locals.lookup (ofString "next_node")=some (.val (.word nextNode))
  slotCell : target.locals.lookup (ofString "next_slot")=some (.val (.word nextSlot))
  levelCell : target.locals.lookup (ofString "next_level")=some (.val (.word nextLevel))
  goCell : target.locals.lookup (ofString "go")=some (.val (.word go))
  stable : ∀ name : MlS,name≠ofString "r" → name≠ofString "next_node" → name≠ofString "next_slot" → name≠ofString "next_level" → name≠ofString "go" →
    target.locals.lookup name=source.locals.lookup name
  domain : target.memaddrs=source.memaddrs
  endian : target.be=source.be
  code : target.code=source.code
  heapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapArena : AllocatedBytes.Arena heap 0
  heapAligned : heap.toNat%8=0
  heapGrows : incoming.toNat≤heap.toNat
  olderPrefix : ∀ query : BitVec 64,query.toNat<nodeLower → target.memory query=source.memory query
  tags : ∀ node,old.valid node → node≠0#64 → wordAt target.memory node=wordAt source.memory node
  graph : TrieWalk.Graph target.memory target.memaddrs
  oldMember : ∀ node,old.valid node → graph.valid node
  rootMember : graph.valid root
  nodeMember : graph.valid nextNode
  nextParent : graph.ParentSlot nextSlot
  values : TrieWalk.Values graph limit property
  regions : graph.Regions nodeLower heap.toNat
  disjoint : graph.Disjoint
  paths : graph.PathBytes target.be
  pathRegions : graph.PathRegions pathLower heap.toNat
  separated : graph.PathSeparated
  step : go=0#64 ∨ go=1#64 ∧ level.toNat<nextLevel.toNat ∧ nextLevel.toNat≤length.toNat
  query : go≠0#64 → graph.PathBuffer target.be pathLower heap.toNat key length.toNat

end InitECandidate.Solver.Mpt.Insert
