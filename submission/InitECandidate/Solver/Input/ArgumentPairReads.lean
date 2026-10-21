import InitECandidate.Solver.Input.ArgumentValues

namespace InitECandidate.Solver.Input.ArgumentValues
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

theorem pair_reads (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : ExpHOL 64) (left right : ValueHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [first,second]=some [left,right]) :
    eval source first=some left ∧ eval source second=some right := by
  cases firstEq : eval source first <;> cases secondEq : eval source second <;>
    simp_all [eval,evalListHOLFinite,evalListHOLExact]

end InitECandidate.Solver.Input.ArgumentValues

#print axioms InitECandidate.Solver.Input.ArgumentValues.pair_reads
