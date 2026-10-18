import InitECandidate.Solver.MutableTable.DeleteFinishMemory

namespace InitECandidate.Solver.MutableTable.Delete.Finish
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure SwapLocals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : Plan) (ordinal last : Nat) : Prop where
  order : source.locals.lookup (ofString "order") = some (.val (.word (cell plan .order 0)))
  position : source.locals.lookup (ofString "order_pos") = some (.val (.word (cell plan .position 0)))
  deleted : source.locals.lookup (ofString "deleted_pos") = some (.val (.word (BitVec.ofNat 64 ordinal)))
  last : source.locals.lookup (ofString "last_pos") = some (.val (.word (BitVec.ofNat 64 last)))

def swapMemory {count : Nat} (input : WordWrites.Memory) (plan : Plan) (deleted : Fin count) (entries : Fin count → Nat) : WordWrites.Memory :=
  if deleted.val = count - 1 then input else WordWrites.write input
    [(cell plan .order (8 * deleted.val), BitVec.ofNat 64 (entries (lastOrdinal deleted))),
     (cell plan .position (8 * entries (lastOrdinal deleted)), BitVec.ofNat 64 deleted.val)]

theorem memory_eq_count {count : Nat} (input : WordWrites.Memory) (plan : Plan) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat) :
    memory input plan deleted entries hole = StoreWord.put (swapMemory (clearedMemory input plan hole) plan deleted entries)
      (cell plan .header 24) (BitVec.ofNat 64 (count - 1)) := by
  by_cases last : deleted.val = count - 1
  · simp only [memory, writes, swapMemory, if_pos last, WordWrites.write]
  · simp only [memory, writes, swapMemory, if_neg last, WordWrites.write]

/-- The actual last-entry swap declaration and two stores, with its local
restored. All physical read and destination mappings follow from owned pools. -/
theorem last_branch_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (ordinal last slot : Nat)
    (ordinalInside : ordinal < plan.capacity) (lastInside : last < plan.capacity) (slotInside : slot < plan.capacity)
    (locals : SwapLocals source plan ordinal last)
    (orderCell : source.memory (cell plan .order (8 * last)) = .word (BitVec.ofNat 64 slot)) :
    evaluateHOLFiniteState source Delete.lastBranch = (none, {source with memory := (WordWrites.write source.memory
      [(cell plan .order (8 * ordinal), BitVec.ofNat 64 slot), (cell plan .position (8 * slot), BitVec.ofNat 64 ordinal)])}) := by
  let entered := WitnessRadix.QueryBranch.bind source "last_slot" (BitVec.ofNat 64 slot)
  let ordered := {entered with memory := StoreWord.put source.memory (cell plan .order (8 * ordinal)) (BitVec.ofNat 64 slot)}
  let canonical := {source with memory := (WordWrites.write source.memory
    [(cell plan .order (8 * ordinal), BitVec.ofNat 64 slot), (cell plan .position (8 * slot), BitVec.ofNat 64 ordinal)])}
  let positioned := WitnessRadix.QueryBranch.bind canonical "last_slot" (BitVec.ofNat 64 slot)
  have mappedWord (pool : Pool) (index : Nat) (inside : index < plan.capacity) (wordPool : pool = .values ∨ pool = .order ∨ pool = .position) : source.memaddrs (cell plan pool (8 * index)) := by
    rw [domain]
    exact mapped kind plan valid pool _ (by have := word_offset_inside kind plan pool index wordPool inside; omega) (by omega)
  have mappedLast : source.memaddrs (cell plan .order 0 + BitVec.ofNat 64 last * 8#64) := by
    rw [Move.natural_word_address kind plan valid .order last lastInside]
    exact mappedWord .order last lastInside (Or.inr (Or.inl rfl))
  have storedLast : source.memory (cell plan .order 0 + BitVec.ofNat 64 last * 8#64) = .word (BitVec.ofNat 64 slot) := by
    rw [Move.natural_word_address kind plan valid .order last lastInside]
    exact orderCell
  have read := Move.word_read source "order" "last_pos" _ _ (BitVec.ofNat 64 slot) locals.order locals.last mappedLast storedLast
  have enteredOrder : entered.locals.lookup (ofString "order") = some (.val (.word (cell plan .order 0))) := (bind_lookup_other _ "last_slot" "order" _ (by decide)).trans locals.order
  have enteredPosition : entered.locals.lookup (ofString "order_pos") = some (.val (.word (cell plan .position 0))) := (bind_lookup_other _ "last_slot" "order_pos" _ (by decide)).trans locals.position
  have enteredDeleted : entered.locals.lookup (ofString "deleted_pos") = some (.val (.word (BitVec.ofNat 64 ordinal))) := (bind_lookup_other _ "last_slot" "deleted_pos" _ (by decide)).trans locals.deleted
  have slotLocal : entered.locals.lookup (ofString "last_slot") = some (.val (.word (BitVec.ofNat 64 slot))) := bind_lookup_same _ _ _
  have orderAddress : eval entered (Delete.wordAddress "order" "deleted_pos") = some (.val (.word (cell plan .order (8 * ordinal)))) := by
    simpa only [Move.natural_word_address kind plan valid .order ordinal ordinalInside] using Move.word_address_read entered "order" "deleted_pos" _ _ enteredOrder enteredDeleted
  have slotRead : eval entered (localVar "last_slot") = some (.val (.word (BitVec.ofNat 64 slot))) := by simp only [eval, localVar, evalHOLExact, toExact, slotLocal]
  have orderRun := StoreWord.execute entered (Delete.wordAddress "order" "deleted_pos") (localVar "last_slot") _ _ orderAddress slotRead (mappedWord .order ordinal ordinalInside (Or.inr (Or.inl rfl)))
  have positionAddress : eval ordered (Delete.wordAddress "order_pos" "last_slot") = some (.val (.word (cell plan .position (8 * slot)))) := by
    simpa only [Move.natural_word_address kind plan valid .position slot slotInside] using Move.word_address_read ordered "order_pos" "last_slot" _ _ enteredPosition slotLocal
  have deletedRead : eval ordered (localVar "deleted_pos") = some (.val (.word (BitVec.ofNat 64 ordinal))) := by
    have here : ordered.locals.lookup (ofString "deleted_pos") = some (.val (.word (BitVec.ofNat 64 ordinal))) := enteredDeleted
    simp only [eval, localVar, evalHOLExact, toExact, here]
  have positionRun := StoreWord.execute ordered (Delete.wordAddress "order_pos" "last_slot") (localVar "deleted_pos") _ _ positionAddress deletedRead (mappedWord .position slot slotInside (Or.inr (Or.inr rfl)))
  have inner : evaluateHOLFiniteState entered (.seq (.store (Delete.wordAddress "order" "deleted_pos") (localVar "last_slot"))
      (.store (Delete.wordAddress "order_pos" "last_slot") (localVar "deleted_pos"))) = (none, positioned) := by
    rw [StateSteps.next_sequence entered ordered _ _ orderRun (Nat.le_refl _)]
    exact positionRun
  have whole := Input.ScalarScope.declare_execute source positioned "last_slot" (.load .one (Delete.wordAddress "order" "last_pos")) (BitVec.ofNat 64 slot) _ none read inner
  change evaluateHOLFiniteState source Delete.lastBranch = (none, restore source "last_slot" positioned) at whole
  have restored : restore source "last_slot" positioned = canonical := by
    change restore canonical "last_slot" (WitnessRadix.QueryBranch.bind canonical "last_slot" (BitVec.ofNat 64 slot)) = canonical
    exact restore_bound _ _ _
  rw [restored] at whole
  exact whole

end InitECandidate.Solver.MutableTable.Delete.Finish

#print axioms InitECandidate.Solver.MutableTable.Delete.Finish.memory_eq_count
#print axioms InitECandidate.Solver.MutableTable.Delete.Finish.last_branch_execute
