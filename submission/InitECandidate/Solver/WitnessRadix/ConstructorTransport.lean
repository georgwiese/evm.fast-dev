import InitECandidate.Solver.WitnessRadix.ConstructorData

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack PanSemStateFiniteExact BackingLayout

theorem prefix_of_fields {F : Type} (source target : PanSemStateFiniteExact 64 F) (layout : Layout)
    (keyFor : BitVec 64 → ByteKeys.Key) (done : Nat)
    (memory : source.memory = target.memory) (domain : source.memaddrs = target.memaddrs)
    (endian : source.be = target.be) (prefixData : Prefix source layout keyFor done) :
    Prefix target layout keyFor done := by
  refine ⟨?_, ?_, ?_⟩
  · intro index inside; rw [← memory]; exact prefixData.recordWords index inside
  · intro index inside
    exact MemoryBytes.byteView_of_fields source target memory domain endian _ _ (prefixData.hashViews index inside)
  · intro index inside; rw [← memory]; exact prefixData.ordinalWords index inside

theorem fixed_of_fields {F : Type} (source target : PanSemStateFiniteExact 64 F) (layout : Layout)
    (sliceFor : BitVec 64 → Graph.Slice)
    (memory : source.memory = target.memory) (domain : source.memaddrs = target.memaddrs)
    (fixedData : FixedData source layout sliceFor) : FixedData target layout sliceFor := by
  rcases fixedData with ⟨⟨a,b,c,d,e,f,g,h⟩, pointers, lengths⟩
  rw [domain] at a c e g
  rw [memory] at b d f h pointers lengths
  exact ⟨⟨a,b,c,d,e,f,g,h⟩, pointers, lengths⟩

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.prefix_of_fields
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.fixed_of_fields
