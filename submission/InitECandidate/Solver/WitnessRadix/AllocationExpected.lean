import InitECandidate.Solver.WitnessRadix.AllocationArithmetic
import InitECandidate.Solver.WitnessRadix.ProgramPrefix

namespace InitECandidate.Solver.WitnessRadix.PersistentAlloc
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

theorem rounded_expected (pointer amount : BitVec 64) (next : Nat)
    (fits : pointer.toNat + amount.toNat + 7 < 2 ^ 64)
    (lower : pointer.toNat + amount.toNat ≤ next) (upper : next < pointer.toNat + amount.toNat + 8)
    (aligned : next % 8 = 0) : rounded pointer amount = BitVec.ofNat 64 next := by
  apply BitVec.eq_of_toNat_eq
  rw [rounded_nat pointer amount fits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

def nextState {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (pointer next : Nat) :
    PanSemStateFiniteExact 64 F :=
  bind { source with
    globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 next)))
    clock := source.clock - 1 } name (BitVec.ofNat 64 pointer)

/-- Natural expected-cursor form of an actual allocation prefix step. -/
theorem prefix_allocate {F : Type} (source entered : PanSemStateFiniteExact 64 F)
    (name : String) (expression : ExpHOL 64) (rest : List ProgramPrefix.Action)
    (restoreRest : PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F)
    (pointer amount next : Nat)
    (read : eval source expression = some (.val (.word (BitVec.ofNat 64 amount))))
    (code : source.code.lookup (ofString "alloc") = some (formals, body, .one))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 pointer))))
    (fits : pointer + amount ≤ 33806089496) (lower : pointer + amount ≤ next)
    (upper : next < pointer + amount + 8) (aligned : next % 8 = 0) (enough : 1 ≤ source.clock)
    (continuation : ProgramPrefix.Executes (nextState source name pointer next) rest entered restoreRest) :
    ProgramPrefix.Executes source (.allocate name expression :: rest) entered
      (fun target => restore source name (restoreRest target)) := by
  have pointerSmall : pointer < 2 ^ 64 := by omega
  have amountSmall : amount < 2 ^ 64 := by omega
  have pointerNum : (BitVec.ofNat 64 pointer).toNat = pointer := by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pointerSmall]
  have amountNum : (BitVec.ofNat 64 amount).toNat = amount := by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt amountSmall]
  have rounded := rounded_expected (BitVec.ofNat 64 pointer) (BitVec.ofNat 64 amount) next
    (by rw [pointerNum, amountNum]; omega) (by rw [pointerNum, amountNum]; exact lower)
    (by rw [pointerNum, amountNum]; exact upper) aligned
  apply ProgramPrefix.Executes.allocate (BitVec.ofNat 64 pointer) (BitVec.ofNat 64 amount) read code heapGlobal
    (by rw [pointerNum, amountNum]; exact fits) enough
  simpa only [post, rounded, nextState] using continuation

end InitECandidate.Solver.WitnessRadix.PersistentAlloc

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.rounded_expected
#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.prefix_allocate
