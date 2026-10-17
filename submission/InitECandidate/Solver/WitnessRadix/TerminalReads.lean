import InitECandidate.Solver.WitnessRadix.TerminalProgram

namespace InitECandidate.Solver.WitnessRadix.TerminalProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem terminal_test {F : Type} (source : PanSemStateFiniteExact 64 F)
    (count bit : BitVec 64)
    (countLocal : source.locals.lookup (ofString "count") = some (.val (.word count)))
    (bitLocal : source.locals.lookup (ofString "bit") = some (.val (.word bit))) :
    eval source terminalTest = some (.val (.word (if count = 1#64 ∨ bit = 256#64 then 1#64 else 0#64))) := by
  classical
  by_cases sameCount : count = 1#64 <;> by_cases sameBit : bit = 256#64
  all_goals simp [eval, terminalTest, localVar, evalHOLExact, evalListHOLExact, toExact,
    countLocal, bitLocal, valueIsWord, valueWord, wordOpHOL, wordOp,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, sameCount, sameBit]
  all_goals decide

theorem ordinal_read {F : Type} (source : PanSemStateFiniteExact 64 F)
    (src start count ordinal : BitVec 64)
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (startLocal : source.locals.lookup (ofString "start") = some (.val (.word start)))
    (countLocal : source.locals.lookup (ofString "count") = some (.val (.word count)))
    (mapped : source.memaddrs (src + ((start + count) - 1#64) * 8#64))
    (stored : source.memory (src + ((start + count) - 1#64) * 8#64) = .word ordinal) :
    eval source ordinalExpression = some (.val (.word ordinal)) := by
  classical
  simp [eval, ordinalExpression, localVar, evalHOLExact, evalListHOLExact, toExact,
    srcLocal, startLocal, countLocal, isWfShapeExactHOL, memLoadHOLExact, mapped, stored,
    valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp]

end InitECandidate.Solver.WitnessRadix.TerminalProgram

#print axioms InitECandidate.Solver.WitnessRadix.TerminalProgram.terminal_test
#print axioms InitECandidate.Solver.WitnessRadix.TerminalProgram.ordinal_read
