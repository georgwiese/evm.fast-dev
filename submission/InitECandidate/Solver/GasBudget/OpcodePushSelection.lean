import InitECandidate.Solver.GasBudget.OpcodePushProgram
import InitECandidate.Solver.GasBudget.DispatchProgram
import InitECandidate.Solver.Input.UnaryCallData

namespace InitECandidate.Solver.GasBudget.OpcodePush
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def opcode (bytes : Nat) : BitVec 64 := BitVec.ofNat 64 (95 + bytes)
def arguments (bytes : Nat) : List (ExpHOL 64) :=
  if bytes = 0 then [.const 0#64] else [.op .sub [localVar "op", .const 95#64]]

private theorem selections : ∀ bytes ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] : List Nat),
    OpcodeDispatch.tree.choose (opcode bytes) = .invoke "op_push" (arguments bytes) := by
  simp only [List.forall_mem_cons]
  repeat first | constructor | rfl | exact List.forall_mem_nil _

theorem selection (bytes : Nat) (bounded : bytes ≤ 32) :
    OpcodeDispatch.tree.choose (opcode bytes) = .invoke "op_push" (arguments bytes) := by
  have member : bytes ∈ List.range 33 := List.mem_range.mpr (by omega)
  have values : List.range 33 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] := by decide
  rw [values] at member
  exact selections bytes member

theorem opcode_nat (bytes : Nat) (bounded : bytes ≤ 32) : (opcode bytes).toNat = 95 + bytes := by
  rw [opcode, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem bytes_nat (bytes : Nat) (bounded : bytes ≤ 32) : (BitVec.ofNat 64 bytes).toNat = bytes := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (bytes : Nat)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word (opcode bytes)))) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) (arguments bytes) =
      some [.val (.word (BitVec.ofNat 64 bytes))] := by
  have difference : opcode bytes - 95#64 = BitVec.ofNat 64 bytes := by
    unfold opcode
    rw [BitVec.ofNat_add, BitVec.add_comm]
    exact BitVec.add_sub_cancel _ _
  by_cases zero : bytes = 0
  · simp [arguments, zero, evalListHOLFinite, evalListHOLExact, evalHOLExact]
  · simp [arguments, zero, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, opLocal,
      valueIsWord, valueWord, wordOpHOL, wordOp, difference]

theorem lookup_bytes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (bytes : Nat)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word (opcode bytes))))
    (installed : Input.OriginalCode.Installed source.code)
    (values : List (ValueHOL 64)) (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) (arguments bytes) = some values)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "op_push") values = some (actual, callee, returnShape)) :
    actual = body ∧ returnShape = .one ∧ callee.lookup (ofString "nbytes") = some (.val (.word (BitVec.ofNat 64 bytes))) := by
  have valuesEq := Option.some.inj (args.symm.trans (arguments_read source bytes opLocal))
  obtain ⟨argument, singleton, bodyEq, shapeEq, typed, binding⟩ := Input.CallNormal.unary_lookup_data source.code.lookup
    (ofString "op_push") (ofString "nbytes") .one body .one (original_code source.code installed) values actual callee returnShape called
  have argumentEq := (List.cons.inj (singleton.symm.trans valuesEq)).1
  rw [argumentEq] at binding
  exact ⟨bodyEq, shapeEq, binding⟩

end InitECandidate.Solver.GasBudget.OpcodePush

#print axioms InitECandidate.Solver.GasBudget.OpcodePush.selection
#print axioms InitECandidate.Solver.GasBudget.OpcodePush.opcode_nat
#print axioms InitECandidate.Solver.GasBudget.OpcodePush.bytes_nat
#print axioms InitECandidate.Solver.GasBudget.OpcodePush.arguments_read
#print axioms InitECandidate.Solver.GasBudget.OpcodePush.lookup_bytes
