import InitECandidate.Solver.GasBudget.MemoryCostNoException
import InitECandidate.Solver.GasBudget.U256Zero
import InitECandidate.Solver.Input.RlpWrite.U256Value

namespace InitECandidate.Solver.GasBudget
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open Input.RlpWrite

private theorem source_or_zero (v : BitVec 64) : OrOp.or v 0#64 = v := BitVec.or_zero

namespace SatWord
def body := ArithmeticEffects.Kind.sat_word.body
def high (words : U256Value.Words) : BitVec 64 := OrOp.or (words 1) (OrOp.or (words 2) (words 3))
def resultWord (words : U256Value.Words) : BitVec 64 := if high words ≠ 0#64 then 18446744073709551615#64 else words 0

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Value.Words)
    (binding : source.locals.lookup (ofString "v") = some (U256Value.tuple words)) :
    evaluateHOLFiniteState source body = (some (.returned (.val (.word (resultWord words)))), emptyLocalsHOLFinite source) := by
  classical
  simp only [body, ArithmeticEffects.Kind.body, ArithmeticEffects.Kind.signature, ArithmeticEffects.Kind.original,
    Guest.guestFn_sat_word, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  by_cases nonzero : high words ≠ 0#64
  all_goals dsimp only [high] at nonzero
  all_goals simp [evaluateHOLFiniteState_seq, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_return,
    evalHOLExact, evalListHOLExact, toExact, binding, U256Value.tuple, valueIsWord, valueWord, wordOpHOL, wordOp,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, resultWord, high, nonzero, source_or_zero, shapeOfHOLExact, sizeOfShapeWithContextHOL,
    fixClockHOLFinite, emptyLocalsHOLFinite]

theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "sat_word") = some ([(ofString "v", U256Value.tupleShape)], body, .one) := by
  simpa only [body, ArithmeticEffects.Kind.name, ArithmeticEffects.Kind.body, ArithmeticEffects.Kind.signature,
    ArithmeticEffects.Kind.original, Guest.guestFn_sat_word, shapeToHOL, U256Value.tupleShape, List.map_cons, List.map_nil, paramToHOL]
    using OriginalCodeEnvironment.arithmetic code installed .sat_word
end SatWord

namespace U256Zero
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "u256_is_zero") = some ([(ofString "a", U256Value.tupleShape)], body, .one) := by
  simpa only [body, ArithmeticEffects.Kind.name, ArithmeticEffects.Kind.body, ArithmeticEffects.Kind.signature,
    ArithmeticEffects.Kind.original, Guest.guestFn_u256_is_zero, shapeToHOL, U256Value.tupleShape, List.map_cons, List.map_nil, paramToHOL]
    using OriginalCodeEnvironment.arithmetic code installed .u256_is_zero
end U256Zero

end InitECandidate.Solver.GasBudget

#print axioms InitECandidate.Solver.GasBudget.SatWord.execute
#print axioms InitECandidate.Solver.GasBudget.U256Zero.original_code
