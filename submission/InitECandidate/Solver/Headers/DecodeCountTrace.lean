import InitECandidate.Solver.Headers.DecodeCountSyntax
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.Headers.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def counted (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : BitVec 64) :=
  if count=23#64 then bind source "is_current" 1#64 else source

/-- Actual count dispatch reaches the original248-byte allocation only for
21 or23 fields, with its actual is_current assignment and no source tick. -/
theorem count_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (count : BitVec 64)
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word count)))
    (currentCell : source.locals.lookup (ofString "is_current")=some (.val (.word 0#64)))
    (shape : source.eshapes.lookup (ofString "HdrErr")=some .one)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterCurrent=(result,post)) :
    source.clock-post.clock≤0 ∨ (count=21#64 ∨ count=23#64) ∧ evaluateHOLFiniteState (counted source count) afterCount=(result,post) := by
  have dispatch : evaluateHOLFiniteState source countGuard=
      if count=23#64 then evaluateHOLFiniteState source (.assign .local (ofString "is_current") (.const 1#64))
      else if count≠21#64 then evaluateHOLFiniteState source (.raise (ofString "HdrErr") (.const 11#64)) else (none,source) := by
    simp [countGuard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,localVar,toExact,countCell,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [current_shape,evaluateHOLFiniteState_seq_line780,dispatch] at run
  by_cases current : count=23#64
  · rw [if_pos current] at run
    have assigned := WitnessRadix.StateSteps.assign_execute source "is_current" (.const 1#64) 0#64 1#64 currentCell rfl
    rw [assigned] at run
    exact Or.inr ⟨Or.inr current,by simpa only [counted,if_pos current] using run⟩
  · rw [if_neg current] at run
    by_cases parent : count=21#64
    · rw [if_neg (not_not_intro parent)] at run
      exact Or.inr ⟨Or.inl parent,by simpa only [counted,if_neg current] using run⟩
    · rw [if_pos parent] at run
      have raised : evaluateHOLFiniteState source (.raise (ofString "HdrErr") (.const 11#64))=
          (some (.exception (ofString "HdrErr") (.val (.word 11#64))),emptyLocalsHOLFinite source) := by
        simp [evaluateHOLFiniteState_raise,shape,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
      rw [raised] at run
      have endpoint : source.clock=post.clock := congrArg (fun output=>output.2.clock) run
      exact Or.inl (by omega)

end InitECandidate.Solver.Headers.Decode

#print axioms InitECandidate.Solver.Headers.Decode.count_trace
