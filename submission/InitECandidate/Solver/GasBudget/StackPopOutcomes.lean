import InitECandidate.Solver.GasBudget.StackPopEffects

namespace InitECandidate.Solver.GasBudget.StackPop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def returnEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp : BitVec 64) :=
  {bind (bind source "sp" sp) "sp" (sp - 1#64) with
    memory := StoreWord.put source.memory (frame + 16#64) (sp - 1#64)}

/-- A nonempty real pop reaches its actual tuple read after precisely the
original sp update. The tuple read may fail; no successful read is supplied. -/
theorem positive_execution (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp : BitVec 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (mapped : source.memaddrs (frame + 16#64)) (cell : source.memory (frame + 16#64) = .word sp)
    (nonzero : sp ≠ 0#64) :
    evaluateHOLFiniteState source body =
      (let output := evaluateHOLFiniteState (returnEntry source frame sp) (.return returnedValue)
       (output.1, restore source "sp" output.2)) := by
  classical
  have spRead := frame_read source frame 16#64 sp ev mapped cell
  let entered := bind source "sp" sp
  have spE : entered.locals.lookup (ofString "sp") = some (.val (.word sp)) := bind_lookup_same _ _ _
  have testRead : eval entered test = some (.val (.word 0#64)) := by
    simp [eval, test, evalHOLExact, toExact, localVar, spE, nonzero, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have guardRun : evaluateHOLFiniteState entered guard = (none, entered) := by
    simp only [eval] at testRead
    rw [guard, evaluateHOLFiniteState_ite, testRead]
    exact evaluateHOLFiniteState_skip entered
  have decrementRead : eval entered decremented = some (.val (.word (sp - 1#64))) := by
    simp [eval, decremented, evalHOLExact, evalListHOLExact, toExact, localVar, spE, valueIsWord, valueWord, wordOpHOL, wordOp]
  have decrementRun := StateSteps.assign_execute entered "sp" decremented sp (sp - 1#64) spE decrementRead
  let next := bind entered "sp" (sp - 1#64)
  have spN : next.locals.lookup (ofString "sp") = some (.val (.word (sp - 1#64))) := bind_lookup_same _ _ _
  have valueRead : eval next (localVar "sp") = some (.val (.word (sp - 1#64))) := by
    simpa only [eval, localVar, evalHOLExact, toExact] using spN
  have writeRun := StoreWord.execute next (frameAddress 16#64) (localVar "sp") (frame + 16#64) (sp - 1#64)
    (address_read next frame 16#64 ev) valueRead mapped
  have tailRun : evaluateHOLFiniteState entered tail =
      evaluateHOLFiniteState (returnEntry source frame sp) (.return returnedValue) := by
    rw [tail, StateSteps.next_sequence entered entered guard afterGuard guardRun (Nat.le_refl _)]
    rw [afterGuard, StateSteps.next_sequence entered next decrement _ decrementRun (Nat.le_refl _)]
    exact StateSteps.next_sequence next _ writeSP (.return returnedValue) writeRun (Nat.le_refl _)
  rw [body_shape]
  exact Input.ScalarScope.declare_execute source _ "sp" (frameLoad 16#64) sp tail _ spRead tailRun

theorem exception_empty (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp : BitVec 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (mapped : source.memaddrs (frame + 16#64)) (cell : source.memory (frame + 16#64) = .word sp)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source body = (some (.exception identifier payload), post)) : sp = 0#64 := by
  by_contra nonzero
  rw [positive_execution source frame sp ev mapped cell nonzero] at run
  have resultEq := congrArg Prod.fst run
  change (evaluateHOLFiniteState (returnEntry source frame sp) (.return returnedValue)).1 = some (.exception identifier payload) at resultEq
  rw [evaluateHOLFiniteState_return] at resultEq
  split at resultEq
  · cases resultEq
  · split at resultEq <;> cases resultEq

/-- The only real pop exception is original underflow, before any memory or
gas mutation. Installed exception metadata comes from the actual source entry. -/
theorem exception_underflow (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp : BitVec 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (mapped : source.memaddrs (frame + 16#64)) (cell : source.memory (frame + 16#64) = .word sp)
    (exceptionShape : source.eshapes.lookup (ofString "EvmErr") = some .one)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source body = (some (.exception identifier payload), post)) :
    sp = 0#64 ∧ identifier = ofString "EvmErr" ∧ payload = .val (.word 2#64) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite source ∧ post.clock = source.clock := by
  have zero := exception_empty source post frame sp ev mapped cell identifier payload run
  have zeroCell : source.memory (frame + 16#64) = .word 0#64 := cell.trans (congrArg HolWordLab.word zero)
  obtain ⟨middle, actual, frameEq, clock⟩ := empty_execute source frame ev mapped zeroCell exceptionShape
  rw [run] at actual
  have resultEq : identifier = ofString "EvmErr" ∧ payload = .val (.word 2#64) := by
    simpa only [Option.some.injEq, PanSemResultExact.exception.injEq] using congrArg Prod.fst actual
  have postEq := congrArg Prod.snd actual
  change post = middle at postEq
  exact ⟨zero, resultEq.1, resultEq.2, postEq ▸ frameEq, postEq ▸ clock⟩

end InitECandidate.Solver.GasBudget.StackPop

#print axioms InitECandidate.Solver.GasBudget.StackPop.positive_execution
#print axioms InitECandidate.Solver.GasBudget.StackPop.exception_empty
#print axioms InitECandidate.Solver.GasBudget.StackPop.exception_underflow
