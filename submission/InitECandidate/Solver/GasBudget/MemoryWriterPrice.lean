import InitECandidate.Solver.GasBudget.MemoryWriterProgram
import InitECandidate.Solver.GasBudget.ArithmeticQuietClock

namespace InitECandidate.Solver.GasBudget.MemoryWriter
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def fastTest (kind : Kind) : ExpHOL 64 := match kind.body with | .seq (.ite test _ _) _ => test | _ => .const 0#64
def fast (kind : Kind) : ProgHOL 64 := match kind.body with | .seq (.ite _ yes _) _ => yes | _ => .skip
def slow (kind : Kind) : ProgHOL 64 := match kind.body with | .seq (.ite _ _ _) rest => rest | _ => .skip

set_option maxRecDepth 10000 in
theorem guarded_body (kind : Kind) (checked : kind = .be64 ∨ kind = .quad) :
    kind.body = .seq (.ite (fastTest kind) (fast kind) .skip) (slow kind) := by
  rcases checked with rfl | rfl
  all_goals simp only [fastTest, fast, slow, Kind.body, Kind.signature, Kind.original,
    Guest.guestFn_st_be64, Guest.guestFn_u256_to_be32, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none]

set_option maxRecDepth 10000 in
theorem fast_stops (kind : Kind) (checked : kind = .be64 ∨ kind = .quad) : Input.NoFallthrough (fast kind) := by
  rcases checked with rfl | rfl
  all_goals simp only [fast, Kind.body, Kind.signature, Kind.original, Guest.guestFn_st_be64, Guest.guestFn_u256_to_be32,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  all_goals repeat' first | apply Input.NoFallthrough.scoped | apply Input.NoFallthrough.declared | apply Input.NoFallthrough.sequence | exact Input.NoFallthrough.returned _

theorem call_price (kind : Kind) (code) (installed : Input.OriginalCode.Installed code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) (price : Nat)
    (priced : Input.ClockCost.Bound code kind.body price) :
    Input.ClockCost.Bound code (.call (Input.LocalEffects.callInfo destination) kind.name arguments) (price + 1) :=
  Input.ClockCost.call_body code destination kind.name arguments kind.signature.1 kind.body kind.signature.2.2 price (original_code kind code installed) priced

theorem be64_fast_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code (fast .be64) 1 := by
  have entry := OriginalCodeEnvironment.arithmetic code installed .bswap64
  have swap := Input.ClockCost.of_quiet code _ (ArithmeticEffects.quiet_preserves .bswap64 code (by rfl))
  simp only [fast, Kind.body, Kind.signature, Kind.original, Guest.guestFn_st_be64, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none]
  refine Input.ClockCost.scoped_body code _ _ (ofString "bswap64") _ _ _ _ _ 0 0 entry swap ?_
  refine Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store code _ _) ?_
  exact Input.ClockCost.returned code _

theorem be64_slow_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code (slow .be64) 2 := by
  simp only [slow, Kind.body, Kind.signature, Kind.original, Guest.guestFn_st_be64, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none]
  refine Input.ClockCost.sequence code _ _ 1 1 (call_price .be32 code installed (some none) _ 0 (be32_price code)) ?_
  refine Input.ClockCost.sequence code _ _ 1 0 (call_price .be32 code installed (some none) _ 0 (be32_price code)) ?_
  exact Input.ClockCost.returned code _

theorem be64_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code Kind.be64.body 2 := by
  rw [guarded_body .be64 (Or.inl rfl)]
  exact Input.ClockCost.stopping_guard code _ _ _ 1 2 (fast_stops .be64 (Or.inl rfl)) (be64_fast_price code installed) (be64_slow_price code installed)

set_option maxRecDepth 10000 in
theorem quad_fast_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code (fast .quad) 4 := by
  have entry := OriginalCodeEnvironment.arithmetic code installed .bswap64
  have swap := Input.ClockCost.of_quiet code _ (ArithmeticEffects.quiet_preserves .bswap64 code (by rfl))
  have swapCall (arguments : List (ExpHOL 64)) : Input.ClockCost.Bound code
      (.call (Input.LocalEffects.callInfo (some (some (ofString "w")))) (ofString "bswap64") arguments) 1 :=
    Input.ClockCost.call_body code _ _ arguments _ _ _ 0 entry swap
  simp only [fast, Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_to_be32, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none]
  refine Input.ClockCost.scoped_body code _ _ (ofString "bswap64") _ _ _ _ _ 0 3 entry swap ?_
  refine Input.ClockCost.sequence code _ _ 0 3 (Input.ClockCost.store code _ _) ?_
  refine Input.ClockCost.sequence code _ _ 1 2 (swapCall _) ?_
  refine Input.ClockCost.sequence code _ _ 0 2 (Input.ClockCost.store code _ _) ?_
  refine Input.ClockCost.sequence code _ _ 1 1 (swapCall _) ?_
  refine Input.ClockCost.sequence code _ _ 0 1 (Input.ClockCost.store code _ _) ?_
  refine Input.ClockCost.sequence code _ _ 1 0 (swapCall _) ?_
  refine Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store code _ _) ?_
  exact Input.ClockCost.returned code _

theorem quad_slow_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code (slow .quad) 12 := by
  simp only [slow, Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_to_be32, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none]
  refine Input.ClockCost.sequence code _ _ 3 9 (call_price .be64 code installed (some none) _ 2 (be64_price code installed)) ?_
  refine Input.ClockCost.sequence code _ _ 3 6 (call_price .be64 code installed (some none) _ 2 (be64_price code installed)) ?_
  refine Input.ClockCost.sequence code _ _ 3 3 (call_price .be64 code installed (some none) _ 2 (be64_price code installed)) ?_
  refine Input.ClockCost.sequence code _ _ 3 0 (call_price .be64 code installed (some none) _ 2 (be64_price code installed)) ?_
  exact Input.ClockCost.returned code _

theorem quad_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code Kind.quad.body 12 := by
  rw [guarded_body .quad (Or.inr rfl)]
  exact Input.ClockCost.stopping_guard code _ _ _ 4 12 (fast_stops .quad (Or.inr rfl)) (quad_fast_price code installed) (quad_slow_price code installed)

end InitECandidate.Solver.GasBudget.MemoryWriter

#print axioms InitECandidate.Solver.GasBudget.MemoryWriter.fast_stops
#print axioms InitECandidate.Solver.GasBudget.MemoryWriter.call_price
#print axioms InitECandidate.Solver.GasBudget.MemoryWriter.be64_price
#print axioms InitECandidate.Solver.GasBudget.MemoryWriter.quad_price
