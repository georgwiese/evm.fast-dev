import InitECandidate.Solver.MutableTable.TruncateStep

namespace InitECandidate.Solver.MutableTable.Truncate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem stop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (count : Nat) (room : count < plan.capacity)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 count)) (limit : BitVec 64) (stopped : count ≤ limit.toNat)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (limitLocal : source.locals.lookup (ofString "n") = some (.val (.word limit))) :
    evaluateHOLFiniteState source tail = (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite source) := by
  have test := condition_read source kind plan valid domain count room header limit tableLocal limitLocal
  rw [if_neg (show ¬ limit.toNat < count from by omega)] at test
  rw [tail, loop, MemeqByteRuntime.loop_stop source condition loopBody returnZero test]
  simp [returnZero, evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]

end InitECandidate.Solver.MutableTable.Truncate

#print axioms InitECandidate.Solver.MutableTable.Truncate.stop_execute
