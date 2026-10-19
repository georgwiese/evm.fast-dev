import InitECandidate.Solver.Mpt.WsAccountLeafData
import InitECandidate.Solver.Mpt.TrieWalkValuesMap
import InitECandidate.Solver.Mpt.TrieWalkValueHash
import InitECandidate.Solver.WitnessRadix.CopyAwayIntervals

namespace InitECandidate.Solver.Mpt.WsAccountLeaf
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Current immutable witness graph/value ownership, separate from the
changing heap and mutable tables. Constructor/global reachability is an
independent obligation; no future call or buffer result is supplied here. -/
structure World (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root nibs : BitVec 64)
    (cutoff frozenEnd valueLimit : Nat) where
  graph : TrieWalk.Graph source.memory source.memaddrs
  member : graph.valid root
  values : TrieWalk.Values graph valueLimit (fun p n=>cutoff≤p.toNat ∧ p.toNat+n.toNat≤frozenEnd)
  worldState : source.globals.lookup (ofString "ws")=some (.val (.word ws))
  rootMapped : source.memaddrs (ws+24#64)
  rootStored : source.memory (ws+24#64)=.word root
  scratch : source.globals.lookup (ofString "mpt_nib_scratch")=some (.val (.word nibs))
  domain : source.memaddrs=InitE.ordinaryDomain
  little : source.be=false
  nibsArena : AllocatedBytes.Arena nibs 64
  nibsBelow : nibs.toNat+64≤cutoff
  ordered : cutoff≤frozenEnd
  bounded : frozenEnd≤33806089496
  footprint : ∀ query,graph.Footprint query ∨ TrieWalk.ValueFootprint graph query ∨ query=ws+24#64 →
    cutoff≤query.toNat ∧ query.toNat<frozenEnd

/-- Real current owned buffers derive the low-level lookup entry model at
any fresh allocated hash output, independent of the mutable table cursor. -/
def World.data (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root nibs heap : BitVec 64)
    (cutoff frozenEnd valueLimit : Nat) (world : World source ws root nibs cutoff frozenEnd valueLimit)
    (afterWorld : frozenEnd≤heap.toNat) (outputArena : AllocatedBytes.Arena heap 32) : Data source ws root heap nibs := by
  have small : cutoff<2^64 := by have := world.ordered; have := world.bounded; omega
  refine {
    graph := world.graph
    member := world.member
    protectedGraph := ?_
    worldState := world.worldState
    rootMapped := world.rootMapped
    rootStored := world.rootStored
    scratch := world.scratch
    little := world.little
    fits := by have := world.nibsArena.upper; omega
    inputMapped := fun offset active=>AllocatedBytes.byte_mapped source heap 32 offset world.domain outputArena active
    outputMapped := fun offset active=>AllocatedBytes.byte_mapped source nibs 64 offset world.domain world.nibsArena active
    separate := ?_ }
  · intro query needed offset active
    have beyond := (world.footprint query (Or.inl needed)).1
    exact (CopyGeneral.Away.before nibs query 64 cutoff world.nibsBelow small beyond offset active).2
  · intro left activeLeft right activeRight
    have number := byteAddress_toNat heap left (by have := outputArena.upper; omega)
    exact (CopyGeneral.Away.before nibs (byteAddress heap left) 64 cutoff world.nibsBelow small (by have := world.ordered; omega) right activeRight).1

def World.values_at_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root nibs heap : BitVec 64)
    (cutoff frozenEnd valueLimit : Nat) (world : World source ws root nibs cutoff frozenEnd valueLimit) (afterWorld : frozenEnd≤heap.toNat) :
    TrieWalk.Values world.graph valueLimit (fun p n=>cutoff≤p.toNat ∧ p.toNat+n.toNat≤heap.toNat) :=
  TrieWalk.Values.map_extra source.memory source.memaddrs world.graph valueLimit _ _ world.values
    (fun p n region=>⟨region.1,Nat.le_trans region.2 afterWorld⟩)

theorem World.value_protected (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root nibs : BitVec 64)
    (cutoff frozenEnd valueLimit : Nat) (world : World source ws root nibs cutoff frozenEnd valueLimit) : TrieWalk.ValueProtected world.graph nibs := by
  intro query needed offset active
  have beyond := (world.footprint query (Or.inr (Or.inl needed))).1
  exact (CopyGeneral.Away.before nibs query 64 cutoff world.nibsBelow (by have := world.ordered; have := world.bounded; omega) beyond offset active).2

/-- All hash-protection premises follow from the current witness interval,
fixed scratch-buffer placement and a fresh aligned output heap. -/
theorem World.protections (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root nibs heap stp pad : BitVec 64)
    (cutoff frozenEnd valueLimit : Nat) (world : World source ws root nibs cutoff frozenEnd valueLimit)
    (afterWorld : frozenEnd≤heap.toNat) (heapBound : heap.toNat≤33806089496) (heapAligned : heap.toNat%8=0)
    (stateBelow : stp.toNat+200≤cutoff) (padBelow : pad.toNat+136≤cutoff) :
    (∀ query,world.graph.Footprint query → Keccak256.Protected stp pad heap query) ∧
      (∀ query,TrieWalk.ValueFootprint world.graph query → Keccak256.Protected stp pad heap query) ∧ Keccak256.Protected stp pad heap (ws+24#64) := by
  have small : cutoff<2^64 := by have := world.ordered; have := world.bounded; omega
  have current (query : BitVec 64) (span : cutoff≤query.toNat ∧ query.toNat<frozenEnd) : Keccak256.Protected stp pad heap query :=
    ⟨CopyGeneral.Away.before stp query 200 cutoff stateBelow small span.1,CopyGeneral.Away.before pad query 136 cutoff padBelow small span.1,
      CopyGeneral.Away.after heap query 32 heapAligned (by omega) (by omega)⟩
  exact ⟨fun query needed=>current query (world.footprint query (Or.inl needed)),
    fun query needed=>current query (world.footprint query (Or.inr (Or.inl needed))),current _ (world.footprint _ (Or.inr (Or.inr rfl)))⟩

end InitECandidate.Solver.Mpt.WsAccountLeaf

#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.World.data
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.World.values_at_heap
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.World.value_protected
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.World.protections
