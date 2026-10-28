import InitECandidate.Solver.Input.CurrentTable.Set.InsertedFields

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix QueryBranch

theorem parents_before (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent leaf internal address : BitVec 64)
    (geometry : New.Geometry table cap) (nodeInside : node.toNat ≤ cap.toNat) (leafInside : leaf.toNat ≤ cap.toNat)
    (internalInside : internal.toNat ≤ cap.toNat) (before : address.toNat < table.toNat) :
    (parentsStored source (New.nodesPointer table cap) node parent leaf internal).memory address = source.memory address := by
  rw [parentsStored,node_before _ table cap node internal address 0 geometry nodeInside (by decide) before,
    node_before _ table cap leaf internal address 0 geometry leafInside (by decide) before,
    node_before _ table cap internal parent address 0 geometry internalInside (by decide) before]

theorem children_before (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node leaf internal address : BitVec 64)
    (query : KeyBits.Key) (difference : Nat) (geometry : New.Geometry table cap) (inside : internal.toNat ≤ cap.toNat)
    (before : address.toNat < table.toNat) :
    (childrenStored source (New.nodesPointer table cap) node leaf internal query difference).memory address = source.memory address := by
  rw [childrenStored,node_before _ table cap internal _ address 16 geometry inside (by decide) before,
    node_before _ table cap internal _ address 8 geometry inside (by decide) before]

theorem attached_before (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent internal oldLeft address : BitVec 64)
    (geometry : New.Geometry table cap) (parentInside : parent.toNat ≤ cap.toNat) (before : address.toNat < table.toNat) :
    (attached source table cap node parent internal oldLeft).memory address = source.memory address := by
  unfold attached
  split
  · exact header_before source table internal address 56 geometry.table (by decide) before
  · split <;> exact node_before source table cap parent internal address _ geometry parentInside (by decide) before

theorem splice_before (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent leaf internal oldLeft address : BitVec 64)
    (query : KeyBits.Key) (difference : Nat) (geometry : New.Geometry table cap)
    (nodeInside : node.toNat ≤ cap.toNat) (parentInside : parent.toNat ≤ cap.toNat)
    (leafInside : leaf.toNat ≤ cap.toNat) (internalInside : internal.toNat ≤ cap.toNat) (before : address.toNat < table.toNat) :
    (spliceResult source table cap node parent leaf internal oldLeft query difference).memory address = source.memory address := by
  rw [spliceResult,attached_before _ table cap node parent internal oldLeft address geometry parentInside before,
    children_before _ table cap node leaf internal address query difference geometry internalInside before,
    parents_before _ table cap node parent leaf internal address geometry nodeInside leafInside internalInside before]
  rfl

/-- The entire genuine fresh insertion protects every earlier input word. -/
theorem inserted_before {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root pointer value node parent : BitVec 64}
    {next count difference : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {query : KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf)
    (address : BitVec 64) (before : address.toNat < table.toNat) :
    (insertedState source table cap node parent pointer value next count difference query left).memory address = source.memory address := by
  obtain ⟨leafInside,internalInside,posInside⟩ := fresh_slots data.image data.available
  rw [insertedState,splice_before _ table cap node parent _ _ _ address query difference data.image.geometry data.node_inside data.parent_inside leafInside internalInside before]
  exact fresh_before data.image data.available address before

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.inserted_before
