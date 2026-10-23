import InitECandidate.Solver.Mpt.LeafRegistration

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- The real newly constructed branch has sixteen null children. -/
def Registration.empty_branch (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (node : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena node 176) (aligned : node.toNat%8=0)
    (tag : source.memory node=.word 3#64)
    (zeros : ∀ offset : Nat,0<offset → offset<176 → offset%8=0 → source.memory (node+BitVec.ofNat 64 offset)=.word 0#64) :
    Registration graph node := by
  have nodeTag : wordAt source.memory node=3#64:=by simp [wordAt,tag,MemoryBytes.wordBits]
  refine ⟨?_,by rw [nodeTag]; exact tag,?_,?_,?_,?_,by rw [nodeTag]; decide⟩
  · simpa only [byteAddress,BitVec.add_zero] using AllocatedBytes.word_mapped source node 176 0 domain arena (by decide) aligned (by decide)
  · intro pathTag
    have impossible : False:=by rw [nodeTag] at pathTag; rcases pathTag with bad|bad <;> cases bad
    exact impossible.elim
  · intro extensionTag
    have impossible : False:=by rw [nodeTag] at extensionTag; cases extensionTag
    exact impossible.elim
  · intro extensionTag zero
    rw [nodeTag] at extensionTag
    cases extensionTag
  · intro notHash notLeaf notExtension index inside
    have field : node+32#64+BitVec.ofNat 64 (index*8)=node+BitVec.ofNat 64 (32+index*8):=by
      rw [BitVec.ofNat_add,←BitVec.add_assoc]
    refine ⟨0#64,?_,?_,graph.null⟩
    · rw [field]
      exact AllocatedBytes.word_mapped source node 176 (32+index*8) domain arena (by omega) aligned (by omega)
    · rw [field]
      exact zeros _ (by omega) (by omega) (by omega)

def ValueView.empty_branch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (limit : Nat) (property : BitVec 64 → BitVec 64 → Prop) (extra : property 0#64 0#64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena node 176) (aligned : node.toNat%8=0)
    (zeros : ∀ offset : Nat,0<offset → offset<176 → offset%8=0 → source.memory (node+BitVec.ofNat 64 offset)=.word 0#64) :
    ValueView source.memory source.memaddrs node 160#64 168#64 limit property := {
  pointer:=0#64
  length:=0#64
  pointerMapped:=AllocatedBytes.word_mapped source node 176 160 domain arena (by decide) aligned (by decide)
  pointerStored:=zeros 160 (by decide) (by decide) (by decide)
  lengthMapped:=AllocatedBytes.word_mapped source node 176 168 domain arena (by decide) aligned (by decide)
  lengthStored:=zeros 168 (by decide) (by decide) (by decide)
  payload:=by simp [Payload]
  extra:=extra }

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Registration.empty_branch
#print axioms InitECandidate.Solver.Mpt.TrieWalk.ValueView.empty_branch
