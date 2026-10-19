import InitECandidate.Solver.Mpt.AccountDecodeOutput
import InitECandidate.Solver.Mpt.FailGuard
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.Input.AssignNormal

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def balanceReset : ProgHOL 64 := .seq (.assign .local (ofString "i") (.const 0#64)) (.seq balanceLoop afterBalance)

theorem after_balance_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code afterBalance 2 := by
  rw [after_balance_shape]
  apply Input.ClockCost.sequence code _ _ 1 1
  · apply Input.ClockCost.conditional code _ _ _ 0 1
    · exact Input.ClockCost.store code _ _
    · apply Input.ClockCost.sequence code _ _ 1 0
      · exact Input.ClockCost.conditional code _ _ _ 1 0 (Fail.call_price code installed _) (Input.ClockCost.skip code)
      · exact Input.ClockCost.store code _ _
  · apply Input.ClockCost.sequence code _ _ 1 0
    · apply Input.ClockCost.conditional code _ _ _ 0 1
      · exact Input.ClockCost.store code _ _
      · apply Input.ClockCost.sequence code _ _ 1 0
        · exact Input.ClockCost.conditional code _ _ _ 1 0 (Fail.call_price code installed _) (Input.ClockCost.skip code)
        · exact Input.ClockCost.store code _ _
    · exact Input.ClockCost.returned code _

theorem balance_reset_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload flag : BitVec 64)
    (cell : source.locals.lookup (ofString "f1")=some (Rlp.Item.result pointer header payload flag))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source balanceReset).2.clock≤payload.toNat+2 := by
  have priced := Input.ClockCost.sequence_reached_current source (.assign .local (ofString "i") (.const 0#64))
    (.seq balanceLoop afterBalance) 0 (payload.toNat+2) (Input.ClockCost.assign source.code _ _ source rfl) ?_
  · simpa only [balanceReset,Nat.zero_add] using priced
  · intro middle normal
    have same := Input.assign_none source middle "i" (.const 0#64) 0#64 rfl normal
    have currentCell : middle.locals.lookup (ofString "f1")=some (Rlp.Item.result pointer header payload flag) := by
      rw [same]
      exact (bind_lookup_other _ "i" "f1" _ (by decide)).trans cell
    have indexCell : middle.locals.lookup (ofString "i")=some (.val (.word 0#64)) := by rw [same]; exact bind_lookup_same _ _ _
    have currentInstalled : Input.OriginalCode.Installed middle.code := by rw [same]; exact installed
    have loopCost := balance_loop_cost middle pointer header payload flag 0#64 currentCell indexCell (by simp)
    exact Input.ClockCost.sequence_current middle balanceLoop afterBalance payload.toNat 2 (by simpa using loopCost) (after_balance_price middle.code currentInstalled)

theorem balance_phase_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (out pointer header payload flag : BitVec 64)
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (cell : source.locals.lookup (ofString "f1")=some (Rlp.Item.result pointer header payload flag))
    (output : Output out) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source balancePhase).2.clock≤payload.toNat+4 := by
  rw [balance_phase_shape]
  change source.clock-(evaluateHOLFiniteState source (.seq clearCall balanceReset)).2.clock≤payload.toNat+4
  have priced := Input.ClockCost.sequence_reached_current source clearCall balanceReset 2 (payload.toNat+2)
    (clear_cost source out outputCell output domain installed) ?_
  · omega
  · intro middle normal
    obtain ⟨funded,same⟩ := clear_none source middle out outputCell output domain installed normal
    have currentCell : middle.locals.lookup (ofString "f1")=some (Rlp.Item.result pointer header payload flag) := by rw [same]; exact cell
    have currentInstalled : Input.OriginalCode.Installed middle.code := by rw [same]; exact installed
    exact balance_reset_cost middle pointer header payload flag currentCell currentInstalled

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.after_balance_price
#print axioms InitECandidate.Solver.Mpt.AccountDecode.balance_reset_cost
#print axioms InitECandidate.Solver.Mpt.AccountDecode.balance_phase_cost
