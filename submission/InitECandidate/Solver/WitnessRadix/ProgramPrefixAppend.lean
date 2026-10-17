import InitECandidate.Solver.WitnessRadix.ProgramPrefix

namespace InitECandidate.Solver.WitnessRadix.ProgramPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open QueryBranch

theorem program_append (left right : List Action) (continuation : ProgHOL 64) :
    program (left ++ right) continuation = program left (program right continuation) := by
  induction left with
  | nil => rfl
  | cons action rest ih => cases action <;> simp only [List.cons_append, program, ih]

theorem executes_append {F : Type} {source middle entered : PanSemStateFiniteExact 64 F}
    {left right : List Action} {restoreLeft restoreRight : PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F}
    (first : Executes source left middle restoreLeft) (second : Executes middle right entered restoreRight) :
    Executes source (left ++ right) entered (fun target => restoreLeft (restoreRight target)) := by
  induction first with
  | done source => exact second
  | declare word read next ih => exact .declare word read (ih second)
  | allocate pointer amount read code heapGlobal fits enough next ih =>
    exact .allocate pointer amount read code heapGlobal fits enough (ih second)
  | command run clock next ih => exact .command run clock (ih second)

end InitECandidate.Solver.WitnessRadix.ProgramPrefix

#print axioms InitECandidate.Solver.WitnessRadix.ProgramPrefix.program_append
#print axioms InitECandidate.Solver.WitnessRadix.ProgramPrefix.executes_append
