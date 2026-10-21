import InitECandidate.Solver.Mpt.WitnessDecodeLookupProgram
import InitECandidate.Solver.Mpt.FailGuard
import InitECandidate.Solver.MutableTable.NodeDbTail32
import InitECandidate.Solver.Input.ClockCostSequenceReached

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A real absent lookup cannot enter materialization. A present result
enters the literal materializer call at the unchanged state, with its actual
slice. The failure branch includes invalid exception-shape outcomes. -/
theorem lookup_guard_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (answer : Option Graph.Slice)
    (installed : Input.OriginalCode.Installed source.code)
    (rCell : source.locals.lookup (ofString "r")=some (MutableTable.NodeDb.output answer))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterLookup=(outcome,post)) :
    source.clock-post.clock≤1 ∨ ∃ slice,answer=some slice ∧ evaluateHOLFiniteState source materializeCall=(outcome,post) := by
  cases answer with
  | none =>
    have test : eval source missingTest=some (.val (.word 1#64)) := by
      simp [eval,missingTest,localVar,evalHOLExact,toExact,rCell,MutableTable.NodeDb.output,MutableTable.NodeDb.triple,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have guard : evaluateHOLFiniteState source missingGuard=evaluateHOLFiniteState source missingCall := by
      simp only [eval] at test
      rw [missingGuard,evaluateHOLFiniteState_ite,test]
      rfl
    have price:=Fail.call_price source.code installed [.const 1#64] source rfl
    change source.clock-(evaluateHOLFiniteState source missingCall).2.clock≤1 at price
    have full:=Input.ClockCost.sequence_reached_current source missingGuard materializeCall 1 0 (by rw [guard]; exact price) (by
      intro middle normal
      rw [guard] at normal
      exact (Fail.call_not_normal source middle installed [.const 1#64] normal).elim)
    rw [← lookup_tail_shape.1,run] at full
    exact Or.inl full
  | some slice =>
    have guard : evaluateHOLFiniteState source missingGuard=(none,source) := by
      simp [missingGuard,missingTest,evaluateHOLFiniteState_ite,evalHOLExact,toExact,localVar,rCell,MutableTable.NodeDb.output,MutableTable.NodeDb.triple,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    rw [lookup_tail_shape.1,evaluateHOLFiniteState_seq_line780,guard] at run
    exact Or.inr ⟨slice,rfl,run⟩

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.lookup_guard_trace
