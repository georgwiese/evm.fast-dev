import InitECandidate.Solver.Mpt.LeafRegistration

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- The original extension constructor is closed when its actual child
belongs to the current graph. A positive segment excludes zero-hop loops. -/
def Registration.positive_extension (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (node key length child : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena node 56) (aligned : node.toNat%8=0)
    (tag : source.memory node=.word 2#64)
    (pointerStored : source.memory (node+32#64)=.word key) (lengthStored : source.memory (node+40#64)=.word length)
    (childStored : source.memory (node+48#64)=.word child) (member : graph.valid child) (positive : 0<length.toNat)
    (fits : key.toNat+min length.toNat 64<2^64)
    (mapped : ∀ offset<min length.toNat 64,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress key offset))) :
    Registration graph node := by
  have nodeTag : wordAt source.memory node=2#64:=by simp [wordAt,tag,MemoryBytes.wordBits]
  have fields (offset : Nat) (inside : offset<56) (alignedOffset : offset%8=0) :
      source.memaddrs (node+BitVec.ofNat 64 offset):=
    AllocatedBytes.word_mapped source node 56 offset domain arena inside aligned alignedOffset
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
  · intro extensionTag
    exact ⟨child,fields 48 (by decide) (by decide),childStored,member⟩
  · intro extensionTag zero
    have number : wordAt source.memory (node+40#64)=length:=by simp [wordAt,lengthStored,MemoryBytes.wordBits]
    have empty : length=0#64:=number.symm.trans zero
    rw [empty] at positive
    exact (by simp at positive)
  · intro notHash notLeaf notExtension
    exact (notExtension nodeTag).elim

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Registration.positive_extension
