import InitECandidate.Solver.WitnessRadix.AllocationCallNormal
import InitECandidate.Solver.WitnessRadix.AllocationExpected

namespace InitECandidate.Solver.WitnessRadix.PersistentAlloc
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Natural cursor form of normal allocation inversion. Request room and
the new cursor bound are conclusions, not premises about future allocations. -/
theorem call_normal_expected {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (pointer amount next : Nat)
    (pointerBound : pointer ≤ 33806089496) (amountSmall : amount < 2 ^ 64)
    (lower : pointer + amount ≤ next) (upper : next < pointer + amount + 8) (aligned : next % 8 = 0)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values (BitVec.ofNat 64 amount)))
    (code : source.code.lookup (ofString "alloc") = some (formals, body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 pointer))))
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "alloc") arguments continuation) = (some (.returned value), target)) :
    pointer + amount ≤ 33806089496 ∧ next ≤ 33806089496 ∧ 1 ≤ source.clock ∧
      ∃ inner, evaluateHOLFiniteState (nextState source name pointer next) continuation = (some (.returned value), inner) ∧ target = restore source name inner := by
  have pointerNum : (BitVec.ofNat 64 pointer).toNat = pointer := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have amountNum : (BitVec.ofNat 64 amount).toNat = amount := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt amountSmall]
  obtain ⟨room, positive, inner, actual, restored⟩ := call_normal source target name arguments continuation (BitVec.ofNat 64 pointer) (BitVec.ofNat 64 amount)
    args code trapCode heapGlobal (by rw [pointerNum]; exact pointerBound) value normal
  have naturalRoom : pointer + amount ≤ 33806089496 := by simpa only [pointerNum, amountNum] using room
  have expected := rounded_expected (BitVec.ofNat 64 pointer) (BitVec.ofNat 64 amount) next
    (by rw [pointerNum, amountNum]; omega) (by rw [pointerNum, amountNum]; exact lower)
    (by rw [pointerNum, amountNum]; exact upper) aligned
  have checked := guards (BitVec.ofNat 64 pointer) (BitVec.ofNat 64 amount) room
  have nextBound := checked.2.2.2.1
  rw [expected, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at nextBound
  have stateEq : WitnessRadix.QueryBranch.bind (post {source with clock := source.clock - 1} (BitVec.ofNat 64 pointer) (BitVec.ofNat 64 amount)) name (BitVec.ofNat 64 pointer) = nextState source name pointer next := by
    simp only [post, expected, nextState]
  rw [stateEq] at actual
  exact ⟨naturalRoom, nextBound, positive, inner, actual, restored⟩

end InitECandidate.Solver.WitnessRadix.PersistentAlloc

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.call_normal_expected
