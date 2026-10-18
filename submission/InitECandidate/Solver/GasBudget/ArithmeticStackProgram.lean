import InitECandidate.Solver.GasBudget.ArithmeticCalls
import InitECandidate.Solver.GasBudget.StackPushFinish
import InitECandidate.Solver.GasBudget.OpcodeChargeSites

namespace InitECandidate.Solver.GasBudget.ArithmeticStackOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

inductive Kind where | op_add | op_mul | op_sub | op_signextend | op_shl | op_shr | op_sar

def Kind.site : Kind → OpcodeChargeSites.Kind
  | .op_add => .op_add | .op_mul => .op_mul | .op_sub => .op_sub | .op_signextend => .op_signextend
  | .op_shl => .op_shl | .op_shr => .op_shr | .op_sar => .op_sar

def quad : ShapeHOL := .comb [.one, .one, .one, .one]

def Kind.calls : Kind → List ArithmeticCalls.Call
  | .op_add => [⟨"r", quad, .u256_add, [localVar "x", localVar "y"], 0, rfl⟩]
  | .op_mul => [⟨"r", quad, .u256_mul, [localVar "x", localVar "y"], 7, rfl⟩]
  | .op_sub => [⟨"r", quad, .u256_sub, [localVar "x", localVar "y"], 0, rfl⟩]
  | .op_signextend => [⟨"bw", .one, .sat_word, [localVar "b"], 0, rfl⟩,
      ⟨"r", quad, .u256_signextend, [localVar "bw", localVar "x"], 6, rfl⟩]
  | .op_shl => [⟨"n", .one, .sat_word, [localVar "sh"], 0, rfl⟩,
      ⟨"r", quad, .u256_shl, [localVar "x", localVar "n"], 0, rfl⟩]
  | .op_shr => [⟨"n", .one, .sat_word, [localVar "sh"], 0, rfl⟩,
      ⟨"r", quad, .u256_shr, [localVar "x", localVar "n"], 0, rfl⟩]
  | .op_sar => [⟨"n", .one, .sat_word, [localVar "sh"], 0, rfl⟩,
      ⟨"r", quad, .u256_sar, [localVar "x", localVar "n"], 3, rfl⟩]

def Kind.bodyPrice (kind : Kind) : Nat := kind.site.names.length + ArithmeticCalls.budget kind.calls + 3

/-- Proof descriptions of the literal original arithmetic suffixes; these
equalities leave every actual expression, helper and lexical scope unchanged. -/
theorem suffix_shape (kind : Kind) : kind.site.suffix = ArithmeticCalls.program kind.calls (StackPush.finish [localVar "r"]) := by
  cases kind <;> simp only [Kind.site, Kind.calls, quad, ArithmeticCalls.program, StackPush.finish,
    OpcodeChargeSites.Kind.suffix, OpcodeChargeSites.stripPops, OpcodeChargeSites.Kind.body, OpcodeChargeSites.Kind.names,
    ArithmeticEffects.Kind.name, ArithmeticEffects.Kind.original,
    Guest.guestFn_op_add, Guest.guestFn_op_mul, Guest.guestFn_op_sub, Guest.guestFn_op_signextend,
    Guest.guestFn_op_shl, Guest.guestFn_op_shr, Guest.guestFn_op_sar,
    Guest.guestFn_u256_add, Guest.guestFn_u256_mul, Guest.guestFn_u256_sub, Guest.guestFn_sat_word,
    Guest.guestFn_u256_signextend, Guest.guestFn_u256_shl, Guest.guestFn_u256_shr, Guest.guestFn_u256_sar,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, localVar] <;> rfl

theorem prices : [Kind.op_add.bodyPrice, Kind.op_mul.bodyPrice, Kind.op_sub.bodyPrice, Kind.op_signextend.bodyPrice,
    Kind.op_shl.bodyPrice, Kind.op_shr.bodyPrice, Kind.op_sar.bodyPrice] = [6, 13, 6, 13, 7, 7, 10] := by decide

end InitECandidate.Solver.GasBudget.ArithmeticStackOpcode

#print axioms InitECandidate.Solver.GasBudget.ArithmeticStackOpcode.suffix_shape
#print axioms InitECandidate.Solver.GasBudget.ArithmeticStackOpcode.prices
