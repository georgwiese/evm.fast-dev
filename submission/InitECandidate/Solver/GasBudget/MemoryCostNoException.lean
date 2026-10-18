import InitECandidate.Solver.GasBudget.MemoryCostEffects
import InitECandidate.Solver.Input.NoExceptionScoped

namespace InitECandidate.Solver.GasBudget.MemoryCostEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem safe_add_sat (code) (installed : Input.OriginalCode.Installed code) : Input.NoException.Safe code ArithmeticEffects.Kind.add_sat.body := by
  simp only [ArithmeticEffects.Kind.body, ArithmeticEffects.Kind.signature, ArithmeticEffects.Kind.original, Guest.guestFn_add_sat, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.NoException.declared
  apply Input.NoException.sequence
  · apply Input.NoException.conditional
    · exact Input.NoException.returned code _
    · exact Input.NoException.skip code
  · exact Input.NoException.returned code _

theorem safe_sat_word (code) (installed : Input.OriginalCode.Installed code) : Input.NoException.Safe code ArithmeticEffects.Kind.sat_word.body := by
  simp only [ArithmeticEffects.Kind.body, ArithmeticEffects.Kind.signature, ArithmeticEffects.Kind.original, Guest.guestFn_sat_word, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.NoException.sequence
  · apply Input.NoException.conditional
    · exact Input.NoException.returned code _
    · exact Input.NoException.skip code
  · exact Input.NoException.returned code _

theorem safe_u256_is_zero (code) (installed : Input.OriginalCode.Installed code) : Input.NoException.Safe code ArithmeticEffects.Kind.u256_is_zero.body := by
  simp only [ArithmeticEffects.Kind.body, ArithmeticEffects.Kind.signature, ArithmeticEffects.Kind.original, Guest.guestFn_u256_is_zero, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.NoException.sequence
  · apply Input.NoException.conditional
    · exact Input.NoException.returned code _
    · exact Input.NoException.skip code
  · exact Input.NoException.returned code _

theorem safe_mul64x64 (code) (installed : Input.OriginalCode.Installed code) : Input.NoException.Safe code ArithmeticEffects.Kind.mul64x64.body := by
  simp only [ArithmeticEffects.Kind.body, ArithmeticEffects.Kind.signature, ArithmeticEffects.Kind.original, Guest.guestFn_mul64x64, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.NoException.declared
  apply Input.NoException.declared
  apply Input.NoException.declared
  apply Input.NoException.declared
  apply Input.NoException.declared
  apply Input.NoException.declared
  apply Input.NoException.declared
  apply Input.NoException.sequence
  · exact Input.NoException.primitive code _ _ _
  · apply Input.NoException.declared
    apply Input.NoException.sequence
    · exact Input.NoException.primitive code _ _ _
    · apply Input.NoException.declared
      exact Input.NoException.returned code _

theorem safe_ceil32 (code) (installed : Input.OriginalCode.Installed code) : Input.NoException.Safe code Kind.ceil32.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_ceil32, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.NoException.declared
  apply Input.NoException.sequence
  · apply Input.NoException.conditional
    · exact Input.NoException.returned code _
    · exact Input.NoException.skip code
  · refine Input.NoException.scoped_body code _ _ (ofString "add_sat") _ _ _ _ _ (OriginalCodeEnvironment.arithmetic code installed .add_sat) (safe_add_sat code installed) ?_
    exact Input.NoException.returned code _

theorem safe_words_of (code) (installed : Input.OriginalCode.Installed code) : Input.NoException.Safe code Kind.words_of.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_words_of, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  refine Input.NoException.scoped_body code _ _ (ofString "ceil32") _ _ _ _ _ (entry code installed .ceil32) (safe_ceil32 code installed) ?_
  exact Input.NoException.returned code _

theorem safe_memory_gas_cost (code) (installed : Input.OriginalCode.Installed code) : Input.NoException.Safe code Kind.memory_gas_cost.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_memory_gas_cost, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  refine Input.NoException.scoped_body code _ _ (ofString "words_of") _ _ _ _ _ (entry code installed .words_of) (safe_words_of code installed) ?_
  refine Input.NoException.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (OriginalCodeEnvironment.arithmetic code installed .mul64x64) (safe_mul64x64 code installed) ?_
  apply Input.NoException.sequence
  · apply Input.NoException.conditional
    · exact Input.NoException.returned code _
    · exact Input.NoException.skip code
  · refine Input.NoException.scoped_body code _ _ (ofString "add_sat") _ _ _ _ _ (OriginalCodeEnvironment.arithmetic code installed .add_sat) (safe_add_sat code installed) ?_
    exact Input.NoException.returned code _

theorem safe_extend_memory_cost1 (code) (installed : Input.OriginalCode.Installed code) : Input.NoException.Safe code Kind.extend_memory_cost1.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_extend_memory_cost1, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  refine Input.NoException.scoped_body code _ _ (ofString "u256_is_zero") _ _ _ _ _ (OriginalCodeEnvironment.arithmetic code installed .u256_is_zero) (safe_u256_is_zero code installed) ?_
  apply Input.NoException.sequence
  · apply Input.NoException.conditional
    · exact Input.NoException.returned code _
    · exact Input.NoException.skip code
  · refine Input.NoException.scoped_body code _ _ (ofString "sat_word") _ _ _ _ _ (OriginalCodeEnvironment.arithmetic code installed .sat_word) (safe_sat_word code installed) ?_
    refine Input.NoException.scoped_body code _ _ (ofString "sat_word") _ _ _ _ _ (OriginalCodeEnvironment.arithmetic code installed .sat_word) (safe_sat_word code installed) ?_
    refine Input.NoException.scoped_body code _ _ (ofString "add_sat") _ _ _ _ _ (OriginalCodeEnvironment.arithmetic code installed .add_sat) (safe_add_sat code installed) ?_
    apply Input.NoException.sequence
    · apply Input.NoException.conditional
      · exact Input.NoException.returned code _
      · exact Input.NoException.skip code
    · apply Input.NoException.declared
      refine Input.NoException.scoped_body code _ _ (ofString "ceil32") _ _ _ _ _ (entry code installed .ceil32) (safe_ceil32 code installed) ?_
      refine Input.NoException.scoped_body code _ _ (ofString "ceil32") _ _ _ _ _ (entry code installed .ceil32) (safe_ceil32 code installed) ?_
      apply Input.NoException.sequence
      · apply Input.NoException.conditional
        · exact Input.NoException.returned code _
        · exact Input.NoException.skip code
      · refine Input.NoException.scoped_body code _ _ (ofString "memory_gas_cost") _ _ _ _ _ (entry code installed .memory_gas_cost) (safe_memory_gas_cost code installed) ?_
        refine Input.NoException.scoped_body code _ _ (ofString "memory_gas_cost") _ _ _ _ _ (entry code installed .memory_gas_cost) (safe_memory_gas_cost code installed) ?_
        apply Input.NoException.sequence
        · apply Input.NoException.conditional
          · exact Input.NoException.returned code _
          · exact Input.NoException.skip code
        · exact Input.NoException.returned code _

end InitECandidate.Solver.GasBudget.MemoryCostEffects

#print axioms InitECandidate.Solver.GasBudget.MemoryCostEffects.safe_add_sat
#print axioms InitECandidate.Solver.GasBudget.MemoryCostEffects.safe_sat_word
#print axioms InitECandidate.Solver.GasBudget.MemoryCostEffects.safe_u256_is_zero
#print axioms InitECandidate.Solver.GasBudget.MemoryCostEffects.safe_mul64x64
#print axioms InitECandidate.Solver.GasBudget.MemoryCostEffects.safe_ceil32
#print axioms InitECandidate.Solver.GasBudget.MemoryCostEffects.safe_words_of
#print axioms InitECandidate.Solver.GasBudget.MemoryCostEffects.safe_memory_gas_cost
#print axioms InitECandidate.Solver.GasBudget.MemoryCostEffects.safe_extend_memory_cost1
