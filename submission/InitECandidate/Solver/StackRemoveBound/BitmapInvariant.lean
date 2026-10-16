import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps

/-! Bitmap preservation when the compiler oracle adds no bitmap words. The
premise covers all future oracle entries and is preserved by actual evaluation. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang

def NoNewBitmaps {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) : Prop :=
  ∀ index, (state.compileOracle index).2.2 = []

theorem bitmapInvariant {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (initial : NoNewBitmaps source)
    (run : StackSemEvaluate.evaluate (program, source) = (result, post)) :
    post.bitmaps = source.bitmaps ∧ NoNewBitmaps post := by
  obtain ⟨count, oracle, code, bitmaps⟩ :=
    StackProps.EvaluateCodeBitmaps.evaluateCodeBitmaps program source result post run
  constructor
  · rw [bitmaps]
    have empty : ∀ index, (source.compileOracle index).2.2 = [] := initial
    simp [empty]
  · intro index
    rw [oracle]
    exact initial (index + count)

end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.bitmapInvariant
