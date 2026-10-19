import InitECandidate.Solver.Mpt.TrieWalkMemory

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact
open WitnessRadix

def triple (flag pointer length : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word flag),.val (.word pointer),.val (.word length)]

/-- A returned value may be parsed by the caller at its real pointer and
length. The byte contents are unrestricted; this is a physical runtime model. -/
def Payload (domain : BitVec 64 → Prop) (pointer length : BitVec 64) (limit : Nat) : Prop :=
  length.toNat≤limit ∧ pointer.toNat+length.toNat<2^64 ∧
    ∀ offset<length.toNat,domain (panByteAlignHOL (width := 64) (byteAddress pointer offset))

structure ValueView (memory : GasBudget.Memory) (domain : BitVec 64 → Prop)
    (node pointerOffset lengthOffset : BitVec 64) (limit : Nat)
    (property : BitVec 64 → BitVec 64 → Prop := fun _ _ => True) where
  pointer : BitVec 64
  length : BitVec 64
  pointerMapped : domain (node+pointerOffset)
  pointerStored : memory (node+pointerOffset)=.word pointer
  lengthMapped : domain (node+lengthOffset)
  lengthStored : memory (node+lengthOffset)=.word length
  payload : Payload domain pointer length limit
  extra : property pointer length

/-- The branch value occupies160/168, separate from its16children.
Neither these fields nor the leaf48/56 value fields are part of the earlier
structural walk invariant. They must be supplied and preserved explicitly. -/
structure Values {memory : GasBudget.Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (limit : Nat)
    (property : BitVec 64 → BitVec 64 → Prop := fun _ _ => True) where
  leaf : ∀ node,graph.valid node → node≠0#64 → GasBudget.wordAt memory node=1#64 →
    ValueView memory domain node 48#64 56#64 limit property
  branch : ∀ node,graph.valid node → node≠0#64 → GasBudget.wordAt memory node≠0#64 →
    GasBudget.wordAt memory node≠1#64 → GasBudget.wordAt memory node≠2#64 →
    ValueView memory domain node 160#64 168#64 limit property

def Answer (domain : BitVec 64 → Prop) (limit : Nat) (value : ValueHOL 64)
    (property : BitVec 64 → BitVec 64 → Prop := fun _ _ => True) : Prop :=
  value=triple 0#64 0#64 0#64 ∨
    ∃ pointer length,value=triple 1#64 pointer length ∧ Payload domain pointer length limit ∧ property pointer length

variable {property : BitVec 64 → BitVec 64 → Prop}

theorem Answer.absent (domain : BitVec 64 → Prop) (limit : Nat) : Answer domain limit (triple 0#64 0#64 0#64) property := Or.inl rfl

theorem ValueView.answer (memory : GasBudget.Memory) (domain : BitVec 64 → Prop)
    (node pointerOffset lengthOffset : BitVec 64) (limit : Nat)
    (view : ValueView memory domain node pointerOffset lengthOffset limit property) :
    Answer domain limit (triple 1#64 view.pointer view.length) property :=
  Or.inr ⟨view.pointer,view.length,rfl,view.payload,view.extra⟩

theorem Answer.binary (domain : BitVec 64 → Prop) (limit : Nat) (value : ValueHOL 64)
    (answer : Answer domain limit value property) :
    ∃ flag pointer length,value=triple flag pointer length ∧ (flag=0#64 ∨ flag=1#64) := by
  rcases answer with absent | ⟨pointer,length,found,payload,extra⟩
  · exact ⟨0#64,0#64,0#64,absent,Or.inl rfl⟩
  · exact ⟨1#64,pointer,length,found,Or.inr rfl⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Answer.absent
#print axioms InitECandidate.Solver.Mpt.TrieWalk.ValueView.answer
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Answer.binary
