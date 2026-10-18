import InitECandidate.Solver.MutableTable.TableFamily
import InitECandidate.Solver.MutableTable.TableFootprint

namespace InitECandidate.Solver.MutableTable.TableFamily
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- Mutation retains all table lifetime floors and all words before every
live table's floor. A global arena split can later instantiate this frame. -/
structure FloorFrame {ι : Type} (objects next : ι → Object)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  floors : ∀ index, (next index).floor = (objects index).floor
  words : ∀ address : BitVec 64, (∀ index, address.toNat < (objects index).floor) → target.memory address = source.memory address

theorem FloorFrame.refl {ι : Type} (objects : ι → Object) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    FloorFrame objects objects source source := ⟨fun _ => rfl, fun _ _ => rfl⟩

theorem FloorFrame.trans {ι : Type} {objects middleObjects next : ι → Object}
    {source middle target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (first : FloorFrame objects middleObjects source middle) (second : FloorFrame middleObjects next middle target) :
    FloorFrame objects next source target := by
  refine ⟨fun index => (second.floors index).trans (first.floors index), ?_⟩
  intro address before
  exact (second.words address (by intro index; rw [first.floors]; exact before index)).trans (first.words address before)

theorem FloorFrame.of_update {ι : Type} [DecidableEq ι] (objects : ι → Object) (writer : ι) (next : Object)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (floor : next.floor = (objects writer).floor)
    (words : ∀ address : BitVec 64, address.toNat < (objects writer).floor → target.memory address = source.memory address) :
    FloorFrame objects (Function.update objects writer next) source target := by
  refine ⟨?_, fun address before => words address (before writer)⟩
  intro index
  by_cases same : index = writer
  · subst index; simpa only [Function.update_self] using floor
  · rw [Function.update_of_ne same]

theorem FloorFrame.below {ι : Type} {objects next : ι → Object} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (frame : FloorFrame objects next source target) (cut : Nat) (floors : ∀ index, cut ≤ (objects index).floor)
    (address : BitVec 64) (before : address.toNat < cut) : target.memory address = source.memory address :=
  frame.words address (fun index => Nat.lt_of_lt_of_le before (floors index))

theorem outside_floor (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (slots : List Nat) (cursor floor : Nat) (table : TableState source kind plan slots cursor floor)
    (address : BitVec 64) (before : address.toNat < floor) : TableFootprint.Outside kind plan address := by
  apply TableFootprint.Outside.of_regions kind plan table.valid
  intro pool
  exact Or.inl (Nat.lt_of_lt_of_le before (table.lower pool))

end InitECandidate.Solver.MutableTable.TableFamily

#print axioms InitECandidate.Solver.MutableTable.TableFamily.FloorFrame.refl
#print axioms InitECandidate.Solver.MutableTable.TableFamily.FloorFrame.trans
#print axioms InitECandidate.Solver.MutableTable.TableFamily.FloorFrame.of_update
#print axioms InitECandidate.Solver.MutableTable.TableFamily.FloorFrame.below
#print axioms InitECandidate.Solver.MutableTable.TableFamily.outside_floor
