import InitECandidate.Solver.Headers.DecodeCountEntry
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.PureGuardNormal

namespace InitECandidate.Solver.Headers.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem count_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (count : BitVec 64)
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word count)))
    (currentCell : source.locals.lookup (ofString "is_current")=some (.val (.word 0#64)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterCurrent=(some (.returned value),post)) :
    (count=21#64 ∨ count=23#64) ∧ evaluateHOLFiniteState (counted source count) afterCount=(some (.returned value),post) := by
  have dispatch : evaluateHOLFiniteState source countGuard=
      if count=23#64 then evaluateHOLFiniteState source (.assign .local (ofString "is_current") (.const 1#64))
      else if count≠21#64 then evaluateHOLFiniteState source (.raise (ofString "HdrErr") (.const 11#64)) else (none,source) := by
    simp [countGuard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,localVar,toExact,countCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [current_shape,evaluateHOLFiniteState_seq_line780,dispatch] at normal
  by_cases current : count=23#64
  · rw [if_pos current] at normal
    have assigned:=WitnessRadix.StateSteps.assign_execute source "is_current" (.const 1#64) 0#64 1#64 currentCell rfl
    rw [assigned] at normal
    exact ⟨Or.inr current,by simpa only [counted,if_pos current] using normal⟩
  · rw [if_neg current] at normal
    by_cases parent : count=21#64
    · rw [if_neg (not_not_intro parent)] at normal
      exact ⟨Or.inl parent,by simpa only [counted,if_neg current] using normal⟩
    · rw [if_pos parent] at normal
      have seqRun : evaluateHOLFiniteState source (.seq (.raise (ofString "HdrErr") (.const 11#64)) afterCount)=(some (.returned value),post) := by
        simpa only [evaluateHOLFiniteState_seq_line780] using normal
      have never:=(Input.PureGuard.raise (ofString "HdrErr") (.const 11#64)).summary source |>.2
      obtain ⟨middle,raised,_⟩ := Input.sequence_returned source post _ _ value never seqRun
      exact (Input.raise_ne_none source (ofString "HdrErr") (.const 11#64) (congrArg Prod.fst raised)).elim

/-- Real list bindings and successful count dispatch derive the21/23
constraint and exact original allocation continuation, with no shape or
successful future-allocation premise. -/
theorem list_count_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (array count : BitVec 64)
    (listCell : source.locals.lookup (ofString "lst")=some (Rlp.Slices.result array count))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterList=(some (.returned value),post)) :
    (count=21#64 ∨ count=23#64) ∧ ∃ inner,
      evaluateHOLFiniteState (counted (declared source array count) count) afterCount=(some (.returned value),inner) ∧
      post=restoreDeclared source array count inner := by
  rw [list_declarations source array count listCell] at normal
  let middle:=(evaluateHOLFiniteState (declared source array count) afterCurrent).2
  have resultEq:=congrArg Prod.fst normal
  have actual : evaluateHOLFiniteState (declared source array count) afterCurrent=(some (.returned value),middle) := Prod.ext resultEq rfl
  have endpoint : post=restoreDeclared source array count middle := (congrArg Prod.snd normal).symm
  have cells:=declared_cells source array count
  obtain ⟨valid,continued⟩ := count_returned (declared source array count) middle count cells.2.1 cells.2.2 value actual
  exact ⟨valid,middle,continued,endpoint⟩

end InitECandidate.Solver.Headers.Decode

#print axioms InitECandidate.Solver.Headers.Decode.count_returned
#print axioms InitECandidate.Solver.Headers.Decode.list_count_returned
