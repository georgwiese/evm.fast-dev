import InitECandidate.Solver.Headers.DecodeCountSyntax
import InitECandidate.Solver.Input.PureGuardNormal
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.Headers.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def counted (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : BitVec 64) :=
  if count=23#64 then bind source "is_current" 1#64 else source

/-- Actual count dispatch reaches the original248-byte allocation only for
21 or23 fields, with its actual is_current assignment and no source tick. -/
theorem count_trace_any (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (count : BitVec 64)
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word count)))
    (currentCell : source.locals.lookup (ofString "is_current")=some (.val (.word 0#64)))
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
      have quiet:=Input.QuietClock.raised source.code (ofString "HdrErr") (.const 11#64) source rfl
      have stops:=Input.raise_ne_none source (ofString "HdrErr") (.const 11#64)
      generalize evaluated : evaluateHOLFiniteState source (.raise (ofString "HdrErr") (.const 11#64))=output at run quiet stops
      obtain ⟨answer,middle⟩:=output
      cases answer with
      | none=>exact (stops rfl).elim
      | some outcome=>
        have endpoint:=congrArg (fun output=>output.2.clock) run
        change middle.clock=post.clock at endpoint
        change middle.clock=source.clock at quiet
        exact Or.inl (by omega)

theorem count_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (count : BitVec 64)
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word count)))
    (currentCell : source.locals.lookup (ofString "is_current")=some (.val (.word 0#64)))
    (shape : source.eshapes.lookup (ofString "HdrErr")=some .one)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterCurrent=(result,post)) :
    source.clock-post.clock≤0 ∨ (count=21#64 ∨ count=23#64) ∧ evaluateHOLFiniteState (counted source count) afterCount=(result,post) :=
  count_trace_any source post count countCell currentCell result run

end InitECandidate.Solver.Headers.Decode

#print axioms InitECandidate.Solver.Headers.Decode.count_trace

#print axioms InitECandidate.Solver.Headers.Decode.count_trace_any
