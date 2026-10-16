import InitECandidate.Solver.StackRawCallBound.BasicLeaves
import InitECandidate.Solver.StackRawCallBound.ControlLeaves
import InitECandidate.Solver.StackRawCallBound.StackAccess
import InitECandidate.Solver.StackRawCallBound.MemoryFfi
import InitECandidate.Solver.StackRawCallBound.AllocationStore
import InitECandidate.Solver.StackRawCallBound.Install
import InitECandidate.Solver.StackRawCallBound.Instruction
import InitECandidate.Solver.StackRawCallBound.Seq
import InitECandidate.Solver.StackRawCallBound.If
import InitECandidate.Solver.StackRawCallBound.Loop
import InitECandidate.Solver.StackRawCallBound.JumpLower
import InitECandidate.Solver.StackRawCallBound.RawCall
import InitECandidate.Solver.StackRawCallBound.Call
import Flapjack.Compiler.Backend.Semantics.StackSem.Measure.CallSites

namespace InitECandidate.Solver.StackRawCallBound
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall
open StackSemMeasure StackSemStateOps StackSemControl

private theorem dropCredit {width : Nat} [NeZero width] {C F : Type}
    {credit allowance : Nat} {compiled : HolProg width} {info : Spt Nat}
    {target post : StackSemStateFiniteExact width C F}
    {result : Option (StackSemResult width)}
    (bounded : BoundedSimulation credit allowance compiled info target post result) :
    BoundedSimulation 0 allowance compiled info target post result := by
  obtain ⟨extra, targetPost, space, budget, relation, execution, guard⟩ := bounded
  exact ⟨extra, targetPost, space, by omega, relation, execution, guard⟩

private theorem compCorrectMeasure {width : Nat} [NeZero width] {C F : Type} :
    ∀ (measure : Nat × Nat) (program : HolProg width)
      (source : StackSemStateFiniteExact width C F),
      stackSemMeasure program source = measure →
      ∀ (info : Spt Nat) (target post : StackSemStateFiniteExact width C F)
        (result : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (program, source) = (result, post) ∧
        result ≠ some .error ∧ stateRel info source target →
      BoundedSimulation (callCredit program source.clock) (source.clock - post.clock) (compTop info program) info target post result ∧
      BoundedSimulation (callCredit program source.clock) (source.clock - post.clock) (comp info program) info target post result := by
  intro measure
  induction measure using Compiler.Backend.StackProps.EvaluateAddClock.lexNat_wf.induction with
  | _ measure ih =>
  intro p s hm info t post r hypothesis
  subst hm
  cases p
  case skip  => exact BasicLeaves.compCorrectSkip  info s t post r hypothesis
  case halt v => exact BasicLeaves.compCorrectHalt v info s t post r hypothesis
  case get v n => exact BasicLeaves.compCorrectGet v n info s t post r hypothesis
  case set n v => exact BasicLeaves.compCorrectSet n v info s t post r hypothesis
  case opCurrHeap b d src => exact BasicLeaves.compCorrectOpCurrHeap b d src info s t post r hypothesis
  case tick  => exact BasicLeaves.compCorrectTick  info s t post r hypothesis
  case ret v => exact ControlLeaves.compCorrectReturn v info s t post r hypothesis
  case raise v => exact ControlLeaves.compCorrectRaise v info s t post r hypothesis
  case «break» v => exact ControlLeaves.compCorrectBreak v info s t post r hypothesis
  case «continue» v => exact ControlLeaves.compCorrectContinue v info s t post r hypothesis
  case locValue a b c => exact StackAccessCase.compCorrectLocValue a b c info s t post r hypothesis
  case stackAlloc n => exact StackAccessCase.compCorrectStackAlloc n info s t post r hypothesis
  case stackFree n => exact StackAccessCase.compCorrectStackFree n info s t post r hypothesis
  case stackLoad a b => exact StackAccessCase.compCorrectStackLoad a b info s t post r hypothesis
  case stackLoadAny a b => exact StackAccessCase.compCorrectStackLoadAny a b info s t post r hypothesis
  case stackStore a b => exact StackAccessCase.compCorrectStackStore a b info s t post r hypothesis
  case stackStoreAny a b => exact StackAccessCase.compCorrectStackStoreAny a b info s t post r hypothesis
  case stackGetSize a => exact StackAccessCase.compCorrectStackGetSize a info s t post r hypothesis
  case stackSetSize a => exact StackAccessCase.compCorrectStackSetSize a info s t post r hypothesis
  case bitmapLoad a b => exact StackAccessCase.compCorrectBitmapLoad a b info s t post r hypothesis
  case codeBufferWrite a b => exact MemoryFfiCase.compCorrectCodeBufferWrite a b info s t post r hypothesis
  case dataBufferWrite a b => exact MemoryFfiCase.compCorrectDataBufferWrite a b info s t post r hypothesis
  case ffi n a b c d e => exact MemoryFfiCase.compCorrectFfi n a b c d e info s t post r hypothesis
  case alloc register => exact AllocationStoreCase.compCorrectAlloc register info s t post r hypothesis
  case storeConsts first second stub => exact AllocationStoreCase.compCorrectStoreConsts first second stub info s t post r hypothesis
  case install a b c d e => exact InstallCase.compCorrectInstall a b c d e info s t post r hypothesis
  case shMemOp op reg addr =>
    cases addr with
    | addr address offset =>
      exact MemoryFfiCase.compCorrectShMemOp op reg address offset info s t post r hypothesis
  case inst instruction =>
    have simulation : BoundedSimulation 0 (s.clock - post.clock) (comp info (.inst instruction)) info t post r := by
      simpa only [BoundedSimulation, Nat.add_comm] using
        evaluateCompInst instruction info s t post r hypothesis
    exact ⟨by simpa only [compTop] using simulation, simulation⟩
  case seq first second =>
    apply compCorrectSeq first second info s t post r
    · intro i target out res h
      exact (ih _ (seq_first_measure_lt first second s) first s rfl i target out res h).2
    · intro middle firstRun i target out res h
      have bound := StackSemEvaluateClock.evaluateClock first s none middle firstRun
      exact (ih _ (lexNat_of_le_of_size_lt bound (seq_second_size_lt first second))
        second middle rfl i target out res h).2
    · exact hypothesis
  case ite cmp reg operand first second =>
    apply compCorrectIf cmp reg operand first second info s t post r
    · intro x y left right compared i target out res h
      exact (ih _ (if_first_measure_lt cmp reg operand first second s)
        first s rfl i target out res h).2
    · intro x y left right compared i target out res h
      exact (ih _ (if_second_measure_lt cmp reg operand first second s)
        second s rfl i target out res h).2
    · exact hypothesis
  case loop body =>
    apply compCorrectLoop body info s t post r
    · intro i target out res h
      exact (ih _ (loop_body_measure_lt body s) body s rfl i target out res h).2
    · intro bodyResult middle bodyRun continues nonzero i target out res h
      have lower := LoopCase.loopReentryClockLess body s middle bodyResult bodyRun nonzero
      exact (ih _ (lexNat_of_clock_lt lower) (.loop body) (decClock middle)
        rfl i target out res h).2
    · exact hypothesis
  case jumpLower r1 r2 dest =>
    apply compCorrectJumpLower r1 r2 dest info s t post r
    · intro x y prog left right compared lookup nonzero i target out res h
      exact dropCredit (ih _ (callee_measure_lt prog (.jumpLower r1 r2 dest) s nonzero)
        prog (decClock s) rfl i target out res h).1
    · exact hypothesis
  case rawCall dest =>
    apply compCorrectRawCall dest info s t post r
    · intro first body lookup nonzero i target out res h
      exact (ih _ (callee_measure_lt body (.rawCall dest) s nonzero)
        body (decClock s) rfl i target out res h).2
    · exact hypothesis
  case call ret dest handler =>
    apply compCorrectCall ret dest handler info s t post r
    · cases ret with
      | none =>
        intro absent prog lookup nonzero i target out res h
        exact dropCredit (ih _ (callee_measure_lt prog (.call none dest handler) s nonzero)
          prog (decClock s) rfl i target out res h).1
      | some triple =>
        obtain ⟨body, link, l1, l2⟩ := triple
        refine ⟨?_, ?_, ?_⟩
        · intro prog lookup nonzero i target out res h
          have lower := callee_measure_lt prog (.call (some (body, link, l1, l2)) dest handler)
            (setVar link (.loc l1 l2) s) nonzero
          exact dropCredit (ih _ lower prog (decClock (setVar link (.loc l1 l2) s))
            rfl i target out res h).1
        · intro prog lookup nonzero middle calleeRun i target out res h
          have bound := StackSemEvaluateClock.evaluateClock prog
            (decClock (setVar link (.loc l1 l2) s)) _ middle calleeRun
          have lower : middle.clock < s.clock := by
            have decreased := decClock_clock_lt (setVar link (.loc l1 l2) s) nonzero
            exact Nat.lt_of_le_of_lt bound decreased
          exact (ih _ (lexNat_of_clock_lt lower) body middle rfl i target out res h).2
        · intro prog handlerBody hl1 hl2 lookup nonzero present middle calleeRun i target out res h
          have bound := StackSemEvaluateClock.evaluateClock prog
            (decClock (setVar link (.loc l1 l2) s)) _ middle calleeRun
          have lower : middle.clock < s.clock := by
            have decreased := decClock_clock_lt (setVar link (.loc l1 l2) s) nonzero
            exact Nat.lt_of_le_of_lt bound decreased
          exact (ih _ (lexNat_of_clock_lt lower) handlerBody middle rfl i target out res h).2
    · exact hypothesis

theorem compCorrect {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source target : StackSemStateFiniteExact width C F)
    (info : Spt Nat) (result : Option (StackSemResult width))
    (post : StackSemStateFiniteExact width C F)
    (hypothesis : StackSemEvaluate.evaluate (program, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation (callCredit program source.clock) (source.clock - post.clock) (compTop info program) info target post result ∧
    BoundedSimulation (callCredit program source.clock) (source.clock - post.clock) (comp info program) info target post result :=
  compCorrectMeasure (stackSemMeasure program source) program source rfl
    info target post result hypothesis

end InitECandidate.Solver.StackRawCallBound
#print axioms InitECandidate.Solver.StackRawCallBound.compCorrect
