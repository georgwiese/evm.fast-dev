import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment
import InitECandidate.Solver.GasBudget.ArithmeticClockPrice

namespace InitECandidate.Solver.GasBudget.MemoryCostEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

inductive Kind where
  | ceil32
  | words_of
  | memory_gas_cost
  | extend_memory_cost1

def Kind.original : Kind → Decl (BitVec 64)
  | .ceil32 => Guest.guestFn_ceil32
  | .words_of => Guest.guestFn_words_of
  | .memory_gas_cost => Guest.guestFn_memory_gas_cost
  | .extend_memory_cost1 => Guest.guestFn_extend_memory_cost1

def Kind.signature (kind : Kind) : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL :=
  match kind.original with
  | .function fn => (fn.params.map paramToHOL, progToHOL fn.body, shapeToHOL fn.returnShape)
  | _ => ([], .skip, .one)
def Kind.name (kind : Kind) : MlS := match kind.original with | .function fn => ofString fn.name | _ => ofString ""
def Kind.body (kind : Kind) : ProgHOL 64 := kind.signature.2.1

def Kind.index : Kind → Nat
  | .ceil32 => 400
  | .words_of => 401
  | .memory_gas_cost => 415
  | .extend_memory_cost1 => 416

set_option maxRecDepth 100000 in
theorem original_index (kind : Kind) : (functionsHOL Input.OriginalCode.program)[kind.index]? = some (kind.name, kind.signature) := by
  cases kind <;> rfl

theorem entry (code) (installed : Input.OriginalCode.Installed code) (kind : Kind) : code.lookup kind.name = some kind.signature :=
  Input.OriginalCode.indexed code installed kind.index (kind.name, kind.signature) (original_index kind)

theorem pure_ceil32 (code) (installed : Input.OriginalCode.Installed code) : Input.LocalEffects.Preserves code Kind.ceil32.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_ceil32, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · refine Input.LocalEffects.scoped_body code _ _ (ofString "add_sat") _ _ _ _ _ (OriginalCodeEnvironment.arithmetic code installed .add_sat) (ArithmeticEffects.pure_add_sat code (OriginalCodeEnvironment.arithmetic code installed)) ?_
    exact Input.LocalEffects.returned code _

theorem price_ceil32 (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code Kind.ceil32.body 1 := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_ceil32, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.ClockCost.declared code _ _ _ _ 1
  apply Input.ClockCost.sequence code _ _ 0 1
  · apply Input.ClockCost.conditional code _ _ _ 0 0
    · exact Input.ClockCost.returned code _
    · exact Input.ClockCost.skip code
  · refine Input.ClockCost.scoped_body code _ _ (ofString "add_sat") _ _ _ _ _ 0 0 (OriginalCodeEnvironment.arithmetic code installed .add_sat) (ArithmeticEffects.price_add_sat code (OriginalCodeEnvironment.arithmetic code installed)) ?_
    exact Input.ClockCost.returned code _

theorem pure_words_of (code) (installed : Input.OriginalCode.Installed code) : Input.LocalEffects.Preserves code Kind.words_of.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_words_of, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  refine Input.LocalEffects.scoped_body code _ _ (ofString "ceil32") _ _ _ _ _ (entry code installed .ceil32) (pure_ceil32 code installed) ?_
  exact Input.LocalEffects.returned code _

theorem price_words_of (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code Kind.words_of.body 2 := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_words_of, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  refine Input.ClockCost.scoped_body code _ _ (ofString "ceil32") _ _ _ _ _ 1 0 (entry code installed .ceil32) (price_ceil32 code installed) ?_
  exact Input.ClockCost.returned code _

theorem pure_memory_gas_cost (code) (installed : Input.OriginalCode.Installed code) : Input.LocalEffects.Preserves code Kind.memory_gas_cost.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_memory_gas_cost, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  refine Input.LocalEffects.scoped_body code _ _ (ofString "words_of") _ _ _ _ _ (entry code installed .words_of) (pure_words_of code installed) ?_
  refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (OriginalCodeEnvironment.arithmetic code installed .mul64x64) (ArithmeticEffects.pure_mul64x64 code (OriginalCodeEnvironment.arithmetic code installed)) ?_
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · refine Input.LocalEffects.scoped_body code _ _ (ofString "add_sat") _ _ _ _ _ (OriginalCodeEnvironment.arithmetic code installed .add_sat) (ArithmeticEffects.pure_add_sat code (OriginalCodeEnvironment.arithmetic code installed)) ?_
    exact Input.LocalEffects.returned code _

theorem price_memory_gas_cost (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code Kind.memory_gas_cost.body 5 := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_memory_gas_cost, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  refine Input.ClockCost.scoped_body code _ _ (ofString "words_of") _ _ _ _ _ 2 2 (entry code installed .words_of) (price_words_of code installed) ?_
  refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 1 (OriginalCodeEnvironment.arithmetic code installed .mul64x64) (ArithmeticEffects.price_mul64x64 code (OriginalCodeEnvironment.arithmetic code installed)) ?_
  apply Input.ClockCost.sequence code _ _ 0 1
  · apply Input.ClockCost.conditional code _ _ _ 0 0
    · exact Input.ClockCost.returned code _
    · exact Input.ClockCost.skip code
  · refine Input.ClockCost.scoped_body code _ _ (ofString "add_sat") _ _ _ _ _ 0 0 (OriginalCodeEnvironment.arithmetic code installed .add_sat) (ArithmeticEffects.price_add_sat code (OriginalCodeEnvironment.arithmetic code installed)) ?_
    exact Input.ClockCost.returned code _

theorem pure_extend_memory_cost1 (code) (installed : Input.OriginalCode.Installed code) : Input.LocalEffects.Preserves code Kind.extend_memory_cost1.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_extend_memory_cost1, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  refine Input.LocalEffects.scoped_body code _ _ (ofString "u256_is_zero") _ _ _ _ _ (OriginalCodeEnvironment.arithmetic code installed .u256_is_zero) (ArithmeticEffects.pure_u256_is_zero code (OriginalCodeEnvironment.arithmetic code installed)) ?_
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · refine Input.LocalEffects.scoped_body code _ _ (ofString "sat_word") _ _ _ _ _ (OriginalCodeEnvironment.arithmetic code installed .sat_word) (ArithmeticEffects.pure_sat_word code (OriginalCodeEnvironment.arithmetic code installed)) ?_
    refine Input.LocalEffects.scoped_body code _ _ (ofString "sat_word") _ _ _ _ _ (OriginalCodeEnvironment.arithmetic code installed .sat_word) (ArithmeticEffects.pure_sat_word code (OriginalCodeEnvironment.arithmetic code installed)) ?_
    refine Input.LocalEffects.scoped_body code _ _ (ofString "add_sat") _ _ _ _ _ (OriginalCodeEnvironment.arithmetic code installed .add_sat) (ArithmeticEffects.pure_add_sat code (OriginalCodeEnvironment.arithmetic code installed)) ?_
    apply Input.LocalEffects.sequence
    · apply Input.LocalEffects.conditional
      · exact Input.LocalEffects.returned code _
      · exact Input.LocalEffects.skip code
    · apply Input.LocalEffects.declared
      refine Input.LocalEffects.scoped_body code _ _ (ofString "ceil32") _ _ _ _ _ (entry code installed .ceil32) (pure_ceil32 code installed) ?_
      refine Input.LocalEffects.scoped_body code _ _ (ofString "ceil32") _ _ _ _ _ (entry code installed .ceil32) (pure_ceil32 code installed) ?_
      apply Input.LocalEffects.sequence
      · apply Input.LocalEffects.conditional
        · exact Input.LocalEffects.returned code _
        · exact Input.LocalEffects.skip code
      · refine Input.LocalEffects.scoped_body code _ _ (ofString "memory_gas_cost") _ _ _ _ _ (entry code installed .memory_gas_cost) (pure_memory_gas_cost code installed) ?_
        refine Input.LocalEffects.scoped_body code _ _ (ofString "memory_gas_cost") _ _ _ _ _ (entry code installed .memory_gas_cost) (pure_memory_gas_cost code installed) ?_
        apply Input.LocalEffects.sequence
        · apply Input.LocalEffects.conditional
          · exact Input.LocalEffects.returned code _
          · exact Input.LocalEffects.skip code
        · exact Input.LocalEffects.returned code _

theorem price_extend_memory_cost1 (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code Kind.extend_memory_cost1.body 20 := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_extend_memory_cost1, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  refine Input.ClockCost.scoped_body code _ _ (ofString "u256_is_zero") _ _ _ _ _ 0 19 (OriginalCodeEnvironment.arithmetic code installed .u256_is_zero) (ArithmeticEffects.price_u256_is_zero code (OriginalCodeEnvironment.arithmetic code installed)) ?_
  apply Input.ClockCost.sequence code _ _ 0 19
  · apply Input.ClockCost.conditional code _ _ _ 0 0
    · exact Input.ClockCost.returned code _
    · exact Input.ClockCost.skip code
  · refine Input.ClockCost.scoped_body code _ _ (ofString "sat_word") _ _ _ _ _ 0 18 (OriginalCodeEnvironment.arithmetic code installed .sat_word) (ArithmeticEffects.price_sat_word code (OriginalCodeEnvironment.arithmetic code installed)) ?_
    refine Input.ClockCost.scoped_body code _ _ (ofString "sat_word") _ _ _ _ _ 0 17 (OriginalCodeEnvironment.arithmetic code installed .sat_word) (ArithmeticEffects.price_sat_word code (OriginalCodeEnvironment.arithmetic code installed)) ?_
    refine Input.ClockCost.scoped_body code _ _ (ofString "add_sat") _ _ _ _ _ 0 16 (OriginalCodeEnvironment.arithmetic code installed .add_sat) (ArithmeticEffects.price_add_sat code (OriginalCodeEnvironment.arithmetic code installed)) ?_
    apply Input.ClockCost.sequence code _ _ 0 16
    · apply Input.ClockCost.conditional code _ _ _ 0 0
      · exact Input.ClockCost.returned code _
      · exact Input.ClockCost.skip code
    · apply Input.ClockCost.declared code _ _ _ _ 16
      refine Input.ClockCost.scoped_body code _ _ (ofString "ceil32") _ _ _ _ _ 1 14 (entry code installed .ceil32) (price_ceil32 code installed) ?_
      refine Input.ClockCost.scoped_body code _ _ (ofString "ceil32") _ _ _ _ _ 1 12 (entry code installed .ceil32) (price_ceil32 code installed) ?_
      apply Input.ClockCost.sequence code _ _ 0 12
      · apply Input.ClockCost.conditional code _ _ _ 0 0
        · exact Input.ClockCost.returned code _
        · exact Input.ClockCost.skip code
      · refine Input.ClockCost.scoped_body code _ _ (ofString "memory_gas_cost") _ _ _ _ _ 5 6 (entry code installed .memory_gas_cost) (price_memory_gas_cost code installed) ?_
        refine Input.ClockCost.scoped_body code _ _ (ofString "memory_gas_cost") _ _ _ _ _ 5 0 (entry code installed .memory_gas_cost) (price_memory_gas_cost code installed) ?_
        apply Input.ClockCost.sequence code _ _ 0 0
        · apply Input.ClockCost.conditional code _ _ _ 0 0
          · exact Input.ClockCost.returned code _
          · exact Input.ClockCost.skip code
        · exact Input.ClockCost.returned code _

end InitECandidate.Solver.GasBudget.MemoryCostEffects

#print axioms InitECandidate.Solver.GasBudget.MemoryCostEffects.original_index
#print axioms InitECandidate.Solver.GasBudget.MemoryCostEffects.entry
#print axioms InitECandidate.Solver.GasBudget.MemoryCostEffects.pure_ceil32
#print axioms InitECandidate.Solver.GasBudget.MemoryCostEffects.price_ceil32
#print axioms InitECandidate.Solver.GasBudget.MemoryCostEffects.pure_words_of
#print axioms InitECandidate.Solver.GasBudget.MemoryCostEffects.price_words_of
#print axioms InitECandidate.Solver.GasBudget.MemoryCostEffects.pure_memory_gas_cost
#print axioms InitECandidate.Solver.GasBudget.MemoryCostEffects.price_memory_gas_cost
#print axioms InitECandidate.Solver.GasBudget.MemoryCostEffects.pure_extend_memory_cost1
#print axioms InitECandidate.Solver.GasBudget.MemoryCostEffects.price_extend_memory_cost1
