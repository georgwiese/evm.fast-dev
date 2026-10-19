import InitECandidate.Solver.Rlp.ReadLengthProgram
import InitECandidate.Solver.Input.ClockCostCurrentGuard

namespace InitECandidate.Solver.Rlp.ReadLength
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat) (index : BitVec 64)
    (small : length<2^64)
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (bounded : index.toNat≤length) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤length-index.toNat := by
  rw [loop_shape]
  simpa only [condition,localVar,Nat.zero_add,Nat.one_mul] using Input.CounterFlow.loop_cost source.code (ofString "i") (ofString "n") loopBody 0 length small
    (loop_body_price source.code) loop_body_advance loop_body_limit source index rfl indexCell lengthCell bounded

theorem after_guard_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length<2^64)
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source afterGuard).2.clock≤length := by
  rw [after_guard_shape]
  apply Input.ClockCost.declared_current source "v" (.const 0#64) 0#64 _ length rfl
  let initial := bind source "v" 0#64
  apply Input.ClockCost.declared_current initial "i" (.const 0#64) 0#64 _ length rfl
  let entered := bind initial "i" 0#64
  have currentIndex : entered.locals.lookup (ofString "i")=some (.val (.word 0#64)) := bind_lookup_same _ _ _
  have currentLength : entered.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))) :=
    (bind_lookup_other initial "i" "n" 0#64 (by decide)).trans ((bind_lookup_other source "v" "n" 0#64 (by decide)).trans lengthCell)
  have cost := loop_cost entered length 0#64 small currentIndex currentLength (by simp)
  have joined := Input.ClockCost.sequence_current entered loop (.return (localVar "v")) length 0
    (by simpa only [BitVec.toNat_zero,Nat.sub_zero] using cost) (Input.ClockCost.returned entered.code _)
  exact joined

/-- All original length-reader outcomes are bounded from the actual current
length word. The failing guard and byte loop are alternatives, so their
allowances are combined by maximum. No byte mapping/funding premise is used. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length<2^64)
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤max 1 length := by
  have firstCost := Fail.call_price source.code installed [.const 2#64] source rfl
  have stops : (evaluateHOLFiniteState source failure).1≠none := by
    intro normal
    exact Fail.call_not_normal source (evaluateHOLFiniteState source failure).2 installed [.const 2#64] (Prod.ext normal rfl)
  rw [body_shape]
  exact Input.ClockCost.stopping_guard_current source guardTest failure afterGuard 1 length stops firstCost (after_guard_cost source length small lengthCell)

theorem body_cost_eight (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length≤8)
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤8 := by
  have cost := body_cost source length (by omega) lengthCell installed
  omega

end InitECandidate.Solver.Rlp.ReadLength

#print axioms InitECandidate.Solver.Rlp.ReadLength.loop_cost
#print axioms InitECandidate.Solver.Rlp.ReadLength.after_guard_cost
#print axioms InitECandidate.Solver.Rlp.ReadLength.body_cost
#print axioms InitECandidate.Solver.Rlp.ReadLength.body_cost_eight
