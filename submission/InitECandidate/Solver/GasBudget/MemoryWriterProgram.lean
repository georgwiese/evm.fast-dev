import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment
import InitECandidate.Solver.Input.ByteStoreClock
import InitECandidate.Solver.Input.ClockCostStoppingGuard
import InitECandidate.Solver.Input.ClockCostScoped

namespace InitECandidate.Solver.GasBudget.MemoryWriter
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

inductive Kind where | be32 | be64 | quad
def Kind.original : Kind → Decl (BitVec 64)
  | .be32 => Guest.guestFn_st_be32 | .be64 => Guest.guestFn_st_be64 | .quad => Guest.guestFn_u256_to_be32
def Kind.index : Kind → Nat | .be32 => 22 | .be64 => 23 | .quad => 81
def Kind.name : Kind → MlS
  | .be32 => ofString "st_be32" | .be64 => ofString "st_be64" | .quad => ofString "u256_to_be32"
def Kind.signature (kind : Kind) : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL :=
  match kind.original with | .function fn => (fn.params.map paramToHOL, progToHOL fn.body, shapeToHOL fn.returnShape) | _ => ([], .skip, .one)
def Kind.body (kind : Kind) := kind.signature.2.1

set_option maxRecDepth 100000 in
theorem original_index (kind : Kind) : (functionsHOL Input.OriginalCode.program)[kind.index]? = some (kind.name, kind.signature) := by cases kind <;> rfl

theorem original_code (kind : Kind) (code) (installed : Input.OriginalCode.Installed code) : code.lookup kind.name = some kind.signature :=
  Input.OriginalCode.indexed code installed kind.index _ (original_index kind)

theorem be32_price (code) : Input.ClockCost.Bound code Kind.be32.body 0 := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_st_be32, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none]
  refine Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store_byte code _ _) ?_
  refine Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store_byte code _ _) ?_
  refine Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store_byte code _ _) ?_
  refine Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store_byte code _ _) ?_
  exact Input.ClockCost.returned code _

end InitECandidate.Solver.GasBudget.MemoryWriter

#print axioms InitECandidate.Solver.GasBudget.MemoryWriter.original_index
#print axioms InitECandidate.Solver.GasBudget.MemoryWriter.original_code
#print axioms InitECandidate.Solver.GasBudget.MemoryWriter.be32_price
