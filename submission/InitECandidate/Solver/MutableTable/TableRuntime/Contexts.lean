import InitECandidate.Solver.MutableTable.TableRuntime.Finish

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack PanSemStateFiniteExact WitnessRadix
open NaturalLayout

theorem preclear_locals {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat)
    (locals : Locals source kind (BitVec.ofNat 64 start) capacity) :
    Locals (usedState source kind start capacity) kind (BitVec.ofNat 64 start) capacity := by
  have keys := Locals.allocated source kind _ capacity locals "keys" (start + 72) (start + 72 + stride kind * capacity) (by decide) (by decide) (by decide)
  have storedKeys : Locals (keysStored source kind start capacity) kind (BitVec.ofNat 64 start) capacity := ⟨keys.tableLocal, keys.capLocal, keys.strideLocal⟩
  have vals := Locals.allocated (keysStored source kind start capacity) kind _ capacity storedKeys "vals"
    (start + 72 + stride kind * capacity) (start + 72 + stride kind * capacity + 8 * capacity) (by decide) (by decide) (by decide)
  have storedVals : Locals (valsStored source kind start capacity) kind (BitVec.ofNat 64 start) capacity := ⟨vals.tableLocal, vals.capLocal, vals.strideLocal⟩
  exact Locals.allocated (valsStored source kind start capacity) kind _ capacity storedVals "used"
    (start + 72 + stride kind * capacity + 8 * capacity)
    (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity) (by decide) (by decide) (by decide)

theorem finish_locals {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat)
    (locals : Locals source kind (BitVec.ofNat 64 start) capacity) :
    Locals (finishState source kind start capacity) kind (BitVec.ofNat 64 start) capacity := by
  have storedUsed : Locals (usedStored source kind start capacity) kind (BitVec.ofNat 64 start) capacity := ⟨locals.tableLocal, locals.capLocal, locals.strideLocal⟩
  have order := Locals.allocated (usedStored source kind start capacity) kind _ capacity storedUsed "order"
    (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity)
    (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity) (by decide) (by decide) (by decide)
  have storedOrder : Locals (orderStored source kind start capacity) kind (BitVec.ofNat 64 start) capacity := ⟨order.tableLocal, order.capLocal, order.strideLocal⟩
  have backup := Locals.allocated (orderStored source kind start capacity) kind _ capacity storedOrder "order_pos"
    (start + 72 + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity) (freshEnd kind start capacity)
    (by decide) (by decide) (by decide)
  exact ⟨backup.tableLocal, backup.capLocal, backup.strideLocal⟩

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.preclear_locals
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.finish_locals
