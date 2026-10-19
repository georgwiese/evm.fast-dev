import InitECandidate.Solver.Mpt.TrieWalkValues

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget

/-- Weaken only the pure ownership predicate on real stored values. All
physical pointers, lengths, mapping and payload bounds are retained. -/
def ValueView.map_extra (memory : Memory) (domain : BitVec 64 → Prop)
    (node pointerOffset lengthOffset : BitVec 64) (limit : Nat)
    (property nextProperty : BitVec 64 → BitVec 64 → Prop)
    (view : ValueView memory domain node pointerOffset lengthOffset limit property)
    (implication : ∀ pointer length,property pointer length → nextProperty pointer length) :
    ValueView memory domain node pointerOffset lengthOffset limit nextProperty := {
  pointer := view.pointer
  length := view.length
  pointerMapped := view.pointerMapped
  pointerStored := view.pointerStored
  lengthMapped := view.lengthMapped
  lengthStored := view.lengthStored
  payload := view.payload
  extra := implication _ _ view.extra }

def Values.map_extra (memory : Memory) (domain : BitVec 64 → Prop) (graph : Graph memory domain) (limit : Nat)
    (property nextProperty : BitVec 64 → BitVec 64 → Prop) (values : Values graph limit property)
    (implication : ∀ pointer length,property pointer length → nextProperty pointer length) : Values graph limit nextProperty := {
  leaf := fun node member active tag=>ValueView.map_extra memory domain node 48#64 56#64 limit property nextProperty (values.leaf node member active tag) implication
  branch := fun node member active notHash notLeaf notExtension=>ValueView.map_extra memory domain node 160#64 168#64 limit property nextProperty
    (values.branch node member active notHash notLeaf notExtension) implication }

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.ValueView.map_extra
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Values.map_extra
