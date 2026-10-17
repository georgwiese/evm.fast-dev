import InitECandidate.Solver.MutableTable.MemoryModelSet
import InitECandidate.Solver.MutableTable.GrowRuntime.Call

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

/-- Physical runtime postcondition of the unchanged setter. Either the old
arrays and heap remain or actual growth doubles/relocates them. Occupancy
increases by at most one. No logical dictionary relation is required. -/
structure ModelPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan) (start count paid : Nat)
    (globals : HolFiniteMapExact MlS (ValueHOL 64)) (memory : WordWrites.Memory) (target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (plan : Plan) (slots : List Nat) : Prop where
  frame : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with globals := globals, memory := memory, clock := source.clock - paid}
  shape : (plan = old ∧ globals = source.globals) ∨
    (plan = relocated kind (old.base .header) start (2 * old.capacity) ∧ globals = source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (relocatedEnd kind start (2 * old.capacity))))))
  countBound : count ≤ slots.length ∧ slots.length ≤ count + 1
  grew : plan ≠ old → old.capacity < 2 * count + 2
  half : 2 * count ≤ old.capacity → 2 * slots.length ≤ plan.capacity
  header : MemoryModel.Header memory kind plan (BitVec.ofNat 64 slots.length)
  occupied : MemoryModel.Occupied target kind plan slots

/-- Transfer the physical model to the actual returned state using its
checked nonlocal frame, including returns that empty/restore local scopes. -/
theorem ModelPost.of_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan) (start count paid : Nat)
    (globals : HolFiniteMapExact MlS (ValueHOL 64)) (memory : WordWrites.Memory) (target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (plan : Plan) (slots : List Nat)
    (frame : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with globals := globals, memory := memory, clock := source.clock - paid})
    (shape : (plan = old ∧ globals = source.globals) ∨
      (plan = relocated kind (old.base .header) start (2 * old.capacity) ∧ globals = source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (relocatedEnd kind start (2 * old.capacity)))))))
    (countBound : count ≤ slots.length ∧ slots.length ≤ count + 1)
    (grew : plan ≠ old → old.capacity < 2 * count + 2)
    (half : 2 * count ≤ old.capacity → 2 * slots.length ≤ plan.capacity)
    (header : MemoryModel.Header memory kind plan (BitVec.ofNat 64 slots.length))
    (occupied : MemoryModel.Occupied {source with memory := memory} kind plan slots) :
    ModelPost source kind old start count paid globals memory target plan slots := by
  have memoryEq := congrArg PanSemStateFiniteExact.memory frame
  have domainEq := congrArg PanSemStateFiniteExact.memaddrs frame
  have endianEq := congrArg PanSemStateFiniteExact.be frame
  exact ⟨frame, shape, countBound, grew, half, header, MemoryModel.Occupied.of_fields _ target kind plan slots occupied memoryEq.symm domainEq.symm endianEq.symm⟩

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.ModelPost.of_frame
