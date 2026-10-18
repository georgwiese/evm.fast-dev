import InitECandidate.Solver.Input.ScalarScope

namespace InitECandidate.Solver.Input.ArgumentValues
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

theorem head_of_list (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (first : ExpHOL 64) (rest : List (ExpHOL 64)) (expected returned : ValueHOL 64) (values : List (ValueHOL 64))
    (read : eval source first = some expected)
    (arguments : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) (first :: rest) =
      some (returned :: values)) : returned = expected := by
  simp only [eval] at read
  rw [evalListHOLFinite, evalListHOLExact, read] at arguments
  cases tail : @evalListHOLExact 64 Guest.HostMemory _ source.toExact
      (fun address => Classical.propDecidable (source.memaddrs address)) rest with
  | none => simp only [tail] at arguments; cases arguments
  | some values =>
    simp only [tail] at arguments
    exact (List.cons.inj (Option.some.inj arguments)).1.symm

theorem first_of_pair (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (first second : ExpHOL 64) (expected left right : BitVec 64)
    (read : eval source first = some (.val (.word expected)))
    (arguments : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [first, second] =
      some [.val (.word left), .val (.word right)]) : left = expected := by
  simp only [eval] at read
  rw [evalListHOLFinite, evalListHOLExact, read] at arguments
  cases rest : @evalListHOLExact 64 Guest.HostMemory _ source.toExact
      (fun address => Classical.propDecidable (source.memaddrs address)) [second] with
  | none => simp only [rest] at arguments; cases arguments
  | some values =>
    simp only [rest] at arguments
    have heads := (List.cons.inj (Option.some.inj arguments)).1
    exact (HolWordLab.word.inj (ValueHOL.val.inj heads)).symm

theorem ignored_call_eq (source : PanSemStateFiniteExact 64 Guest.HostMemory) (function : MlS)
    (first second : List (ExpHOL 64))
    (same : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) first =
      evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) second) :
    evaluateHOLFiniteState source (.call (some (none, none)) function first) =
      evaluateHOLFiniteState source (.call (some (none, none)) function second) := by
  rw [evaluateHOLFiniteState_call, evaluateHOLFiniteState_call, same]

theorem ignored_sequence_eq (source : PanSemStateFiniteExact 64 Guest.HostMemory) (function : MlS)
    (first second : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (same : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) first =
      evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) second) :
    evaluateHOLFiniteState source (.seq (.call (some (none, none)) function first) continuation) =
      evaluateHOLFiniteState source (.seq (.call (some (none, none)) function second) continuation) := by
  simp only [evaluateHOLFiniteState_seq_line780]
  rw [ignored_call_eq source function first second same]

end InitECandidate.Solver.Input.ArgumentValues

#print axioms InitECandidate.Solver.Input.ArgumentValues.first_of_pair
#print axioms InitECandidate.Solver.Input.ArgumentValues.head_of_list
#print axioms InitECandidate.Solver.Input.ArgumentValues.ignored_call_eq
#print axioms InitECandidate.Solver.Input.ArgumentValues.ignored_sequence_eq
