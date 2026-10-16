import InitECandidate.Solver.CrepToLoopBound.ProgramCost
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Property

namespace InitECandidate.Solver.CrepToLoopBound
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

-- Original simulation and every original relation, augmented by a clock bound
-- and eligibility of the current program and installed code.
def Simulation {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (program : CrepProgHOL width) (source : CrepSemHOLState width F) : Prop :=
  CodeSafe limit source.code → ceiling program ≤ limit →
  ∀ (result : Option (CrepResultHOLExact width))
    (sourceFinal : CrepSemHOLState width F),
    ∀ (target : LoopSemStateFiniteExact width F)
    (context : CrepToLoopContextExact) (live : NumSet),
    evalCrepSemHOLProgExact source program = (result, sourceFinal) →
    result ≠ some .error →
    crepToLoopStateRelExact source target →
    crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs →
    crepToLoopGlobalsRelHOLExact source.globals target.globals →
    crepToLoopCodeRelExact context source.code target.code →
    crepToLoopLocalsRelExact context live source.locals target.locals →
    ∃ (extra : Nat) (targetResult : Option (LoopResultExact width))
      (targetFinal : LoopSemStateFiniteExact width F),
      extra ≤ (2 * limit + 3) * (source.clock - sourceFinal.clock) + cost program ∧
      LoopSemStateFiniteExact.evaluate (compileHOLExact context live program)
        { target with clock := target.clock + extra } = (targetResult, targetFinal) ∧
      crepToLoopStateRelExact sourceFinal targetFinal ∧
      crepToLoopMemRelHOLExact sourceFinal.memory targetFinal.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals targetFinal.globals ∧
      crepToLoopCodeRelExact context sourceFinal.code targetFinal.code ∧
      targetResult = resultToLoop result ∧
      localsResultRel context live result sourceFinal targetFinal

end InitECandidate.Solver.CrepToLoopBound
