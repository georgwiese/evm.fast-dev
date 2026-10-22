import InitECandidate.Solver.Mpt.TrieGraphRegisteredRegions

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Register the actual fields of a newly initialized leaf. Its path
mapping is supplied for the bytes the original traversal can inspect. -/
def Registration.leaf (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (node key length : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena node 64) (aligned : node.toNat%8=0)
    (tag : source.memory node=.word 1#64)
    (pointerStored : source.memory (node+32#64)=.word key) (lengthStored : source.memory (node+40#64)=.word length)
    (fits : key.toNat+min length.toNat 64<2^64)
    (mapped : ∀ offset<min length.toNat 64,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress key offset))) :
    Registration graph node := by
  have nodeTag : wordAt source.memory node=1#64:=by simp [wordAt,tag,MemoryBytes.wordBits]
  have fields (offset : Nat) (inside : offset<64) (alignedOffset : offset%8=0) :
      source.memaddrs (node+BitVec.ofNat 64 offset):=
    AllocatedBytes.word_mapped source node 64 offset domain arena inside aligned alignedOffset
  refine ⟨?_,by rw [nodeTag]; exact tag,?_,?_,?_,?_⟩
  · simpa only [BitVec.add_zero] using fields 0 (by decide) (by decide)
  · intro pathTag
    exact {
      size:=length
      pointer:=key
      sizeMapped:=fields 40 (by decide) (by decide)
      sizeStored:=lengthStored
      pointerMapped:=fields 32 (by decide) (by decide)
      pointerStored:=pointerStored
      fits:=fits
      mapped:=mapped }
  · intro extensionTag; rw [nodeTag] at extensionTag; cases extensionTag
  · intro extensionTag; rw [nodeTag] at extensionTag; cases extensionTag
  · intro notHash notLeaf; exact (notLeaf nodeTag).elim

def ValueView.leaf (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node pointer length : BitVec 64) (limit : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena node 64) (aligned : node.toNat%8=0)
    (pointerStored : source.memory (node+48#64)=.word pointer) (lengthStored : source.memory (node+56#64)=.word length)
    (payload : Payload source.memaddrs pointer length limit) (extra : property pointer length) :
    ValueView source.memory source.memaddrs node 48#64 56#64 limit property := {
  pointer:=pointer
  length:=length
  pointerMapped:=AllocatedBytes.word_mapped source node 64 48 domain arena (by decide) aligned (by decide)
  pointerStored:=pointerStored
  lengthMapped:=AllocatedBytes.word_mapped source node 64 56 domain arena (by decide) aligned (by decide)
  lengthStored:=lengthStored
  payload:=payload
  extra:=extra }

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Registration.leaf
#print axioms InitECandidate.Solver.Mpt.TrieWalk.ValueView.leaf
