import InitECandidate.Solver.MutableTable.DeleteMoveReads
import InitECandidate.Solver.JumpDest.Advance

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def selected (home hole slot : BitVec 64) : Bool :=
  if slot.toNat < hole.toNat then decide (home.toNat ≤ hole.toNat ∧ slot.toNat < home.toNat)
  else decide (home.toNat ≤ hole.toNat ∨ slot.toNat < home.toNat)

/-- Actual unsigned home/hole/scan comparisons set exactly the original
movable flag. The proof makes no claim about favorable hash outcomes. -/
theorem decision_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (home hole slot : BitVec 64)
    (homeLocal : source.locals.lookup (ofString "home") = some (.val (.word home)))
    (holeLocal : source.locals.lookup (ofString "i") = some (.val (.word hole)))
    (slotLocal : source.locals.lookup (ofString "j") = some (.val (.word slot)))
    (movableLocal : source.locals.lookup (ofString "movable") = some (.val (.word 0#64))) :
    evaluateHOLFiniteState source decision =
      (none, WitnessRadix.QueryBranch.bind source "movable" (if selected home hole slot then 1#64 else 0#64)) := by
  have assigned : evaluateHOLFiniteState source setMovable = (none, WitnessRadix.QueryBranch.bind source "movable" 1#64) :=
    StateSteps.assign_execute source "movable" (.const 1#64) 0#64 1#64 movableLocal rfl
  have kept := JumpDest.bind_existing source "movable" 0#64 movableLocal
  by_cases order : slot.toNat < hole.toNat <;> by_cases lower : home.toNat ≤ hole.toNat <;> by_cases upper : slot.toNat < home.toNat <;>
    simp [homeLocal, holeLocal, slotLocal, movableLocal, assigned, kept, order, lower, upper, decision, truth, beforeHome, afterHome, selected, evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact, toExact, localVar,
      valueIsWord, valueWord, wordOpHOL, wordOp, AndOp.and, OrOp.or, BitVec.lt_def, BitVec.le_def, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, Nat.not_lt]

namespace Move
open NaturalLayout

theorem Locals.bind_flag (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (hole slot : Nat)
    (locals : Locals source kind plan hole slot) (flag : BitVec 64) : Locals (WitnessRadix.QueryBranch.bind source "movable" flag) kind plan hole slot := by
  exact ⟨(bind_lookup_other _ "movable" "keys" _ (by decide)).trans locals.keys,
    (bind_lookup_other _ "movable" "vals" _ (by decide)).trans locals.values,
    (bind_lookup_other _ "movable" "order" _ (by decide)).trans locals.order,
    (bind_lookup_other _ "movable" "order_pos" _ (by decide)).trans locals.position,
    (bind_lookup_other _ "movable" "klen" _ (by decide)).trans locals.length,
    (bind_lookup_other _ "movable" "stride" _ (by decide)).trans locals.stride,
    (bind_lookup_other _ "movable" "i" _ (by decide)).trans locals.hole,
    (bind_lookup_other _ "movable" "j" _ (by decide)).trans locals.slot⟩

end Move
end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.decision_execute
#print axioms InitECandidate.Solver.MutableTable.Delete.Move.Locals.bind_flag
