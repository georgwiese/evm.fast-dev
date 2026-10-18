import InitECandidate.Solver.MutableTable.DeleteMoveReads
import InitECandidate.Solver.WitnessRadix.Bindings

namespace InitECandidate.Solver.MutableTable.Delete.Move
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def afterCopy : ProgHOL 64 := .seq Delete.valueStore
  (.dec (ofString "moved_pos") .one (Delete.positionRead "j") (.seq Delete.orderStore (.seq Delete.positionStore Delete.moveIndex)))
def storesMemory (input : WordWrites.Memory) (plan : Plan) (hole ordinal : Nat) (value : BitVec 64) : WordWrites.Memory :=
  WordWrites.write (StoreWord.put input (cell plan .values (8 * hole)) value) (writes plan hole ordinal)

theorem branch_shape : Delete.moveBranch = .seq Delete.copyCall afterCopy := rfl

/-- The entire actual movable suffix after memcpy: source value and inverse
position reads, all three stores, hole-index assignment and moved_pos scope.
Every mapping/separation follows from physical owned pools. -/
theorem after_copy_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (hole slot ordinal : Nat) (value : BitVec 64)
    (holeInside : hole < plan.capacity) (slotInside : slot < plan.capacity) (ordinalInside : ordinal < plan.capacity)
    (locals : Locals source kind plan hole slot)
    (valueCell : source.memory (cell plan .values (8 * slot)) = .word value)
    (positionCell : source.memory (cell plan .position (8 * slot)) = .word (BitVec.ofNat 64 ordinal)) :
    evaluateHOLFiniteState source afterCopy =
      (none, WitnessRadix.QueryBranch.bind {source with memory := storesMemory source.memory plan hole ordinal value} "i" (BitVec.ofNat 64 slot)) := by
  let valued := {source with memory := StoreWord.put source.memory (cell plan .values (8 * hole)) value}
  let entered := WitnessRadix.QueryBranch.bind valued "moved_pos" (BitVec.ofNat 64 ordinal)
  let ordered := {entered with memory := StoreWord.put entered.memory (cell plan .order (8 * ordinal)) (BitVec.ofNat 64 hole)}
  let positioned := {entered with memory := WordWrites.write valued.memory (writes plan hole ordinal)}
  let canonical := {source with memory := storesMemory source.memory plan hole ordinal value}
  have mappedWord (pool : Pool) (index : Nat) (inside : index < plan.capacity) (wordPool : pool = .values ∨ pool = .order ∨ pool = .position) :
      source.memaddrs (cell plan pool (8 * index)) := by
    rw [domain]
    exact mapped kind plan valid pool _ (by have := word_offset_inside kind plan pool index wordPool inside; omega) (by omega)
  have valueMapped : source.memaddrs (cell plan .values 0 + BitVec.ofNat 64 slot * 8#64) := by
    rw [natural_word_address kind plan valid .values slot slotInside]
    exact mappedWord .values slot slotInside (Or.inl rfl)
  have valueStored : source.memory (cell plan .values 0 + BitVec.ofNat 64 slot * 8#64) = .word value := by
    rw [natural_word_address kind plan valid .values slot slotInside]
    exact valueCell
  have valueAddress : eval source (Delete.wordAddress "vals" "i") = some (.val (.word (cell plan .values (8 * hole)))) := by
    simpa only [natural_word_address kind plan valid .values hole holeInside] using word_address_read source "vals" "i" _ _ locals.values locals.hole
  have valueRun := StoreWord.execute source (Delete.wordAddress "vals" "i") (.load .one (Delete.wordAddress "vals" "j")) (cell plan .values (8 * hole)) value
    valueAddress (word_read source "vals" "j" _ _ value locals.values locals.slot valueMapped valueStored) (mappedWord .values hole holeInside (Or.inl rfl))
  have away := separate kind plan valid .position .values (by decide) (8 * slot) (8 * hole)
    (by change 8 * slot < 8 * plan.capacity; omega) (by change 8 * hole < 8 * plan.capacity; omega)
  have kept : valued.memory (cell plan .position (8 * slot)) = .word (BitVec.ofNat 64 ordinal) := by
    change StoreWord.put source.memory (cell plan .values (8 * hole)) value (cell plan .position (8 * slot)) = _
    rw [StoreWord.put, if_neg away]
    exact positionCell
  have positionMapped : valued.memaddrs (cell plan .position 0 + BitVec.ofNat 64 slot * 8#64) := by
    rw [natural_word_address kind plan valid .position slot slotInside]
    exact mappedWord .position slot slotInside (Or.inr (Or.inr rfl))
  have positionStored : valued.memory (cell plan .position 0 + BitVec.ofNat 64 slot * 8#64) = .word (BitVec.ofNat 64 ordinal) := by
    rw [natural_word_address kind plan valid .position slot slotInside]
    exact kept
  have positionRead := word_read valued "order_pos" "j" _ _ (BitVec.ofNat 64 ordinal) locals.position locals.slot positionMapped positionStored
  have enteredLocals := Locals.bind_position valued kind plan hole slot (Locals.of_locals source valued kind plan hole slot locals rfl) (BitVec.ofNat 64 ordinal)
  have ordinalLocal : entered.locals.lookup (ofString "moved_pos") = some (.val (.word (BitVec.ofNat 64 ordinal))) := bind_lookup_same _ _ _
  have orderAddress : eval entered (Delete.wordAddress "order" "moved_pos") = some (.val (.word (cell plan .order (8 * ordinal)))) := by
    simpa only [natural_word_address kind plan valid .order ordinal ordinalInside] using word_address_read entered "order" "moved_pos" _ _ enteredLocals.order ordinalLocal
  have orderValue : eval entered (localVar "i") = some (.val (.word (BitVec.ofNat 64 hole))) := by
    simpa [eval, localVar, evalHOLExact, toExact] using enteredLocals.hole
  have orderRun := StoreWord.execute entered (Delete.wordAddress "order" "moved_pos") (localVar "i") _ _ orderAddress orderValue (mappedWord .order ordinal ordinalInside (Or.inr (Or.inl rfl)))
  have positionAddress : eval ordered (Delete.wordAddress "order_pos" "i") = some (.val (.word (cell plan .position (8 * hole)))) := by
    simpa only [natural_word_address kind plan valid .position hole holeInside] using word_address_read ordered "order_pos" "i" _ _ enteredLocals.position enteredLocals.hole
  have positionValue : eval ordered (localVar "moved_pos") = some (.val (.word (BitVec.ofNat 64 ordinal))) := by
    simp [eval, localVar, evalHOLExact, toExact, ordered, ordinalLocal]
  have positionRun := StoreWord.execute ordered (Delete.wordAddress "order_pos" "i") (localVar "moved_pos") _ _ positionAddress positionValue (mappedWord .position hole holeInside (Or.inr (Or.inr rfl)))
  have indexRead : eval positioned (localVar "j") = some (.val (.word (BitVec.ofNat 64 slot))) := by
    have actual : positioned.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 slot))) := enteredLocals.slot
    simp [eval, localVar, evalHOLExact, toExact, actual]
  have indexRun := StateSteps.assign_execute positioned "i" (localVar "j") (BitVec.ofNat 64 hole) (BitVec.ofNat 64 slot) enteredLocals.hole indexRead
  have inner : evaluateHOLFiniteState entered (.seq Delete.orderStore (.seq Delete.positionStore Delete.moveIndex)) =
      (none, WitnessRadix.QueryBranch.bind positioned "i" (BitVec.ofNat 64 slot)) := by
    rw [StateSteps.next_sequence entered ordered Delete.orderStore _ orderRun (Nat.le_refl _),
      StateSteps.next_sequence ordered positioned Delete.positionStore Delete.moveIndex positionRun (Nat.le_refl _)]
    exact indexRun
  have scopeRun := Input.ScalarScope.declare_execute valued _ "moved_pos" (Delete.positionRead "j") (BitVec.ofNat 64 ordinal)
    (.seq Delete.orderStore (.seq Delete.positionStore Delete.moveIndex)) none positionRead inner
  have positionedEq : positioned = WitnessRadix.QueryBranch.bind canonical "moved_pos" (BitVec.ofNat 64 ordinal) := rfl
  have restored : restore valued "moved_pos" (WitnessRadix.QueryBranch.bind positioned "i" (BitVec.ofNat 64 slot)) =
      WitnessRadix.QueryBranch.bind canonical "i" (BitVec.ofNat 64 slot) := by
    rw [restore_bind_other valued positioned "moved_pos" "i" _ (by decide), positionedEq]
    change WitnessRadix.QueryBranch.bind (restore canonical "moved_pos" (WitnessRadix.QueryBranch.bind canonical "moved_pos" (BitVec.ofNat 64 ordinal))) "i" _ = _
    rw [restore_bound]
  rw [afterCopy, StateSteps.next_sequence source valued Delete.valueStore _ valueRun (Nat.le_refl _), scopeRun, restored]

end InitECandidate.Solver.MutableTable.Delete.Move

#print axioms InitECandidate.Solver.MutableTable.Delete.Move.branch_shape
#print axioms InitECandidate.Solver.MutableTable.Delete.Move.after_copy_execute
