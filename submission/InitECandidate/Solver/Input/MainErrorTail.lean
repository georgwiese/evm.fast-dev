import InitECandidate.Solver.Input.MainErrorProgram
import InitECandidate.Solver.Input.OutputCall
import InitECandidate.Solver.WitnessRadix.ByteStoreWord

namespace InitECandidate.Solver.Input.Main.ErrorHandler
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem suffix_cost (code) : ClockCost.Bound code suffix 0 := by
  exact ClockCost.sequence code halt (.return (.const 1#64)) 0 0
    (ClockCost.of_quiet code halt (QuietClock.external code (ofString "halt") .baseAddr (.const 0#64) .baseAddr (.const 0#64))) (ClockCost.returned code _)

/-- Appending the original error byte followed by the genuine output44 call
and halt has at most45 source ticks, including every stopping outcome. -/
theorem tail_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out error : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (outBinding : source.locals.lookup (ofString "out") = some (.val (.word out)))
    (errorBinding : source.locals.lookup (ofString "err_code") = some (.val (.word error)))
    (lengthBinding : source.locals.lookup (ofString "n") = some (.val (.word 43#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : AllocatedBytes.Arena out 44) :
    source.clock - (evaluateHOLFiniteState source tail).2.clock ≤ 45 := by
  have addressRead : eval source (.op .add [localVar "out",localVar "n"]) = some (.val (.word (out + 43#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,outBinding,lengthBinding,valueIsWord,valueWord,wordOpHOL,wordOp]
  have errorRead : eval source (localVar "err_code") = some (.val (.word error)) := by
    simp [eval,evalHOLExact,localVar,errorBinding]
  let middle := {source with memory := ByteStore.put source.memory source.be (out + 43#64) (BitVec.ofNat 8 error.toNat)}
  have appendRun : evaluateHOLFiniteState source append = (none,middle) := ByteStore.execute_word source _ _ (out + 43#64) error addressRead errorRead
    (AllocatedBytes.byte_mapped source out 44 43 domain arena (by decide))
  have args : evalListHOLFinite middle (h := fun address => Classical.propDecidable (middle.memaddrs address)) outputArgs = some (Output.values out 44) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,outputArgs,resultLength,localVar,middle,outBinding,lengthBinding,Output.values,valueIsWord,valueWord,wordOpHOL,wordOp]
  have outputCost := Output.call_cost middle outputArgs out 44 (by decide) installed args
  rw [tail,StateSteps.next_sequence source middle _ _ appendRun (Nat.le_refl _)]
  exact ClockCost.sequence_current middle _ suffix 45 0 outputCost (suffix_cost source.code)

end InitECandidate.Solver.Input.Main.ErrorHandler

#print axioms InitECandidate.Solver.Input.Main.ErrorHandler.suffix_cost
#print axioms InitECandidate.Solver.Input.Main.ErrorHandler.tail_cost
