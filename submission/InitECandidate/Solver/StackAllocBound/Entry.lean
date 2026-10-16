import InitECandidate.Solver.StackAllocBound.Assembly

/-! The allocation-lowered entry call uses the same clock and retains the
source result and full FFI state. Source/compiler invariants remain explicit. -/
namespace InitECandidate.Solver.StackAllocBound
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackAlloc
open Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.StackSemEvaluate

theorem entrySimulation {width : Nat} [NeZero width] {C F : Type}
    (anything : WordSemGcFun width) (cr : CompileFn width C)
    (source postSource : StackSemStateFiniteExact width C F)
    (config : DataToWord.Config) (entry clock : Nat)
    (safe : StateSafe source) (pre : Pre cr config source source.regs)
    (result : Option (StackSemResult width))
    (run : evaluate (.call none (.inl entry) none, {source with clock := clock}) =
      (result, postSource)) (nonError : result ≠ some .error) :
    ∃ postTarget,
      evaluate (.call none (.inl entry) none,
        Tgt anything cr config {source with clock := clock} 0 source.regs) =
        (result, postTarget) ∧ postTarget.ffi = postSource.ffi := by
  obtain ⟨regs, targetRun, _⟩ := zeroCompCorrect anything cr
    (.call none (.inl entry) none) {source with clock := clock} rfl safe result postSource
    0 0 config source.regs run nonError (by simp [StackProps.allocArg])
      ⟨pre.code, pre.oracle, pre.gcFun, pre.useAlloc, pre.stack, pre.regs, pre.useStack, pre.buf, pre.compile⟩
  refine ⟨Res anything cr config postSource regs, ?_, rfl⟩
  simpa only [comp] using targetRun

end InitECandidate.Solver.StackAllocBound
#print axioms InitECandidate.Solver.StackAllocBound.entrySimulation
