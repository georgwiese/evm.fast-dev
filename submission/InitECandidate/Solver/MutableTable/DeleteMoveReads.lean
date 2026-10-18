import InitECandidate.Solver.MutableTable.DeleteMoveMemory

namespace InitECandidate.Solver.MutableTable.Delete.Move
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (hole slot : Nat) : Prop where
  keys : source.locals.lookup (ofString "keys") = some (.val (.word (cell plan .keys 0)))
  values : source.locals.lookup (ofString "vals") = some (.val (.word (cell plan .values 0)))
  order : source.locals.lookup (ofString "order") = some (.val (.word (cell plan .order 0)))
  position : source.locals.lookup (ofString "order_pos") = some (.val (.word (cell plan .position 0)))
  length : source.locals.lookup (ofString "klen") = some (.val (.word (BitVec.ofNat 64 (KeyHash.keySize kind))))
  stride : source.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 (NaturalLayout.stride kind))))
  hole : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 hole)))
  slot : source.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 slot)))

theorem Locals.of_locals (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (hole slot : Nat)
    (locals : Locals source kind plan hole slot) (same : source.locals = target.locals) : Locals target kind plan hole slot := by
  rcases locals with ⟨keys, values, order, position, length, stride, holeLocal, slotLocal⟩
  constructor <;> rw [← same] <;> assumption

theorem Locals.bind_position (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (hole slot : Nat)
    (locals : Locals source kind plan hole slot) (ordinal : BitVec 64) : Locals (WitnessRadix.QueryBranch.bind source "moved_pos" ordinal) kind plan hole slot := by
  exact ⟨(bind_lookup_other _ "moved_pos" "keys" _ (by decide)).trans locals.keys,
    (bind_lookup_other _ "moved_pos" "vals" _ (by decide)).trans locals.values,
    (bind_lookup_other _ "moved_pos" "order" _ (by decide)).trans locals.order,
    (bind_lookup_other _ "moved_pos" "order_pos" _ (by decide)).trans locals.position,
    (bind_lookup_other _ "moved_pos" "klen" _ (by decide)).trans locals.length,
    (bind_lookup_other _ "moved_pos" "stride" _ (by decide)).trans locals.stride,
    (bind_lookup_other _ "moved_pos" "i" _ (by decide)).trans locals.hole,
    (bind_lookup_other _ "moved_pos" "j" _ (by decide)).trans locals.slot⟩

theorem natural_word_address (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (pool : Pool) (index : Nat) (inside : index < plan.capacity) :
    cell plan pool 0 + BitVec.ofNat 64 index * 8#64 = cell plan pool (8 * index) := by
  rw [scaled_cell, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans inside (capacity_small kind plan valid)), Nat.mul_comm]

theorem word_address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pool index : String) (base number : BitVec 64)
    (poolLocal : source.locals.lookup (ofString pool) = some (.val (.word base)))
    (indexLocal : source.locals.lookup (ofString index) = some (.val (.word number))) :
    eval source (Delete.wordAddress pool index) = some (.val (.word (base + number * 8#64))) := by
  simp [eval, Delete.wordAddress, Delete.scaled, localVar, evalHOLExact, evalListHOLExact, toExact, poolLocal, indexLocal,
    valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL]

theorem word_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pool index : String) (base number value : BitVec 64)
    (poolLocal : source.locals.lookup (ofString pool) = some (.val (.word base)))
    (indexLocal : source.locals.lookup (ofString index) = some (.val (.word number)))
    (mapped : source.memaddrs (base + number * 8#64)) (stored : source.memory (base + number * 8#64) = .word value) :
    eval source (.load .one (Delete.wordAddress pool index)) = some (.val (.word value)) := by
  simp [eval, Delete.wordAddress, Delete.scaled, localVar, evalHOLExact, evalListHOLExact, toExact, poolLocal, indexLocal,
    valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, memLoadHOLExact, isWfShapeExactHOL, mapped, stored]

theorem copy_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (hole slot : Nat)
    (locals : Locals source kind plan hole slot) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [Delete.keyAddress "i", Delete.keyAddress "j", localVar "klen"] =
      some (CopyGeneral.values (cell plan .keys 0 + BitVec.ofNat 64 hole * BitVec.ofNat 64 (NaturalLayout.stride kind))
        (cell plan .keys 0 + BitVec.ofNat 64 slot * BitVec.ofNat 64 (NaturalLayout.stride kind)) (KeyHash.keySize kind)) := by
  simp [CopyGeneral.values, Delete.keyAddress, Delete.scaled, localVar, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact,
    locals.keys, locals.stride, locals.hole, locals.slot, locals.length, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL]

end InitECandidate.Solver.MutableTable.Delete.Move

#print axioms InitECandidate.Solver.MutableTable.Delete.Move.Locals.of_locals
#print axioms InitECandidate.Solver.MutableTable.Delete.Move.Locals.bind_position
#print axioms InitECandidate.Solver.MutableTable.Delete.Move.natural_word_address
#print axioms InitECandidate.Solver.MutableTable.Delete.Move.word_address_read
#print axioms InitECandidate.Solver.MutableTable.Delete.Move.word_read
#print axioms InitECandidate.Solver.MutableTable.Delete.Move.copy_arguments
