import InitECandidate.Solver.Input.VarList.Walk

namespace InitECandidate.Solver.Input.VarList
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem walk_previous (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index rounds : Nat) (previous : BitVec 64) (positive : 0<rounds) :
    (walk source input plan index previous rounds).locals.lookup (ofString "prev")=
      some (.val (.word (currentWord input plan.start (index+rounds-1)))) := by
  induction rounds generalizing source index previous with
  | zero=>omega
  | succ rounds ih=>
    cases rounds with
    | zero=>
      simpa only [walk,Nat.add_sub_cancel] using iteration_previous (decClockHOLFinite source) input plan index previous
    | succ rounds=>
      rw [walk,ih _ _ _ (by omega)]
      have number : index+1+(rounds+1)-1=index+(rounds+1+1)-1 := by omega
      rw [number]

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.walk_previous
