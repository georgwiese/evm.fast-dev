import InitECandidate.Solver.Mpt.CommonPrefixProgram
import InitECandidate.Solver.Input.ClockCostCurrent

namespace InitECandidate.Solver.Mpt.CommonPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem after_minimum_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat) (small : length≤64)
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source afterMinimum).2.clock≤length := by
  rw [afterMinimum]
  apply Input.ClockCost.declared_current source "i" (.const 0#64) 0#64 loopAndAfter length rfl
  let current:=bind source "i" 0#64
  have currentN : current.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))):=
    (bind_lookup_other source "i" "n" 0#64 (by decide)).trans nCell
  have valid : Input.GuardedCounterLoop.Invariant length current:=⟨0#64,bind_lookup_same _ _ _,currentN,by change 0≤length; omega⟩
  have cost:=Input.GuardedCounterLoop.cost test loopBody 1 length (by decide) small guarded (test_reads length small) current valid
  exact Input.ClockCost.sequence_current current (.while test loopBody) (.return (localVar "n")) length 0 cost (Input.ClockCost.returned current.code _)

/-- All original comparison outcomes cost at most the shorter path plus
one min-call tick. Arbitrary byte contents, failed reads and short clocks
are included; no future comparison success or clock funding is supplied. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (left right : BitVec 64)
    (small : min left.toNat right.toNat≤64) (installed : Input.OriginalCode.Installed source.code)
    (leftCell : source.locals.lookup (ofString "al")=some (.val (.word left)))
    (rightCell : source.locals.lookup (ofString "bl")=some (.val (.word right))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤min left.toNat right.toNat+1 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) minimumArguments=
      some [.val (.word left),.val (.word right)]:=by
    simp [minimumArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,leftCell,rightCell]
  rw [body_shape]
  by_cases zero : source.clock=0
  · rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    obtain ⟨callee,called,a,b⟩:=GasBudget.Minimum.environment source.code.lookup left right (minimum_code source.code installed)
    simp [args,called,zero]
  · have actual:=GasBudget.Minimum.call_execute source left right "n" minimumArguments afterMinimum args (minimum_code source.code installed) (by omega)
    let current:=bind {source with clock:=source.clock-1} "n" (GasBudget.Minimum.selected left right)
    have selectedEq : GasBudget.Minimum.selected left right=BitVec.ofNat 64 (min left.toNat right.toNat):=by
      rw [←GasBudget.Minimum.selected_number left right]
      simp
    have currentN : current.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 (min left.toNat right.toNat)))):=by
      rw [←selectedEq]
      exact bind_lookup_same _ _ _
    have cost:=after_minimum_cost current (min left.toNat right.toNat) small currentN
    change source.clock-1-(evaluateHOLFiniteState current afterMinimum).2.clock≤min left.toNat right.toNat at cost
    rw [actual]
    change source.clock-(evaluateHOLFiniteState current afterMinimum).2.clock≤min left.toNat right.toNat+1
    omega

end InitECandidate.Solver.Mpt.CommonPrefix

#print axioms InitECandidate.Solver.Mpt.CommonPrefix.after_minimum_cost
#print axioms InitECandidate.Solver.Mpt.CommonPrefix.body_cost
