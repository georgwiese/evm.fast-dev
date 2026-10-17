import InitECandidate.Solver.MutableTable.LayoutHeader32

namespace InitECandidate.Solver.MutableTable
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem key_model_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Find.Parameters)
    (capacity : Nat) (table : Find.Model32 (BitVec 64))
    (memory : source.memory=target.memory) (domain : source.memaddrs=target.memaddrs) (endian : source.be=target.be)
    (model : Find.KeyModel32 source p capacity table) : Find.KeyModel32 target p capacity table := by
  constructor
  · intro i inside
    rw [← Find.usedByte_of_fields source target p (BitVec.ofNat 64 i) memory domain endian]
    exact model.used i inside
  · intro i inside key value cell
    exact MemoryBytes.byteView_of_fields source target memory domain endian _ key (model.view i inside key value cell)

theorem value_model_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (vals : BitVec 64)
    (capacity : Nat) (table : Find.Model32 (BitVec 64))
    (memory : source.memory=target.memory) (domain : source.memaddrs=target.memaddrs)
    (model : Find.ValueModel32 source vals capacity table) : Find.ValueModel32 target vals capacity table := by
  intro i inside key value cell
  obtain ⟨mapped,stored⟩:=model i inside key value cell
  rw [domain] at mapped
  rw [memory] at stored
  exact ⟨mapped,stored⟩

theorem header_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (key : BitVec 64) (count : Nat) (memory : source.memory=target.memory) (domain : source.memaddrs=target.memaddrs)
    (header : Layout32.Header source plan key count) : Layout32.Header target plan key count := by
  refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
  · intro offset member;rw [← domain];exact header.find.mapped offset member
  all_goals rw [← memory]
  · exact header.find.capacity
  · exact header.find.keyLength
  · exact header.find.stride
  · exact header.find.keys
  · exact header.find.used
  · exact header.values
  · exact header.order
  · exact header.position
  · exact header.count

theorem word_view_fields {F : Type} (source target : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (words : Fin 4→BitVec 64)
    (memory : source.memory=target.memory) (domain : source.memaddrs=target.memaddrs)
    (view : MemoryBytes.WordView source pointer words) : MemoryBytes.WordView target pointer words := by
  constructor
  · intro i;rw [← domain];exact view.mapped i
  · intro i;rw [← memory];exact view.stored i

end InitECandidate.Solver.MutableTable

#print axioms InitECandidate.Solver.MutableTable.key_model_fields
#print axioms InitECandidate.Solver.MutableTable.value_model_fields
#print axioms InitECandidate.Solver.MutableTable.header_fields
