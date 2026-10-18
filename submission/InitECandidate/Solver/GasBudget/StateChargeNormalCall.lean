import InitECandidate.Solver.GasBudget.StateChargeNormal
import InitECandidate.Solver.GasBudget.StateChargeBudget
import InitECandidate.Solver.Input.IgnoredCallNormal

namespace InitECandidate.Solver.GasBudget.StateCharge
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual original state-gas call, with both affordability and available
clocks derived. The combined state/regular sum may overflow; actual add_sat
still selects the right branch. The capped regular ledger prevents spill
counter wrap and is preserved by the exact executed writes. -/
theorem call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas state spill amount : BitVec 64)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions = some [.val (.word amount)])
    (code : source.code.lookup (ofString "charge_state_gas") = some (formals, body, .one))
    (pools : Pools source frame gas state spill)
    (addCode : source.code.lookup (ofString "add_sat") = some (AddExact.formals, AddExact.body, .one))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "charge_state_gas") expressions) = (none, target)) :
    ∃ paid, paid ≤ 2 ∧ paid ≤ source.clock ∧ 1 ≤ paid ∧ target.clock = source.clock - paid ∧
      amount.toNat ≤ state.toNat + gas.toNat ∧
      target.memory = WitnessRadix.WordWrites.write source.memory (poolWrites frame gas state spill amount) ∧
      target = {source with memory := target.memory, clock := source.clock - paid} ∧
      regularBudget target.memory frame = regularBudget source.memory frame := by
  obtain ⟨callee, called, amountLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "charge_state_gas") "amount" body amount code
  obtain ⟨positive, post, returned, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "charge_state_gas") expressions [.val (.word amount)] body callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  have entryPools : Pools entry frame gas state spill := ⟨pools.ev, pools.mapped, pools.gas, pools.state, pools.spill⟩
  obtain ⟨paid, bound, fits, affordable, returnedEq, memory, frameEq⟩ := body_bound entry post frame gas state spill amount entryPools amountLocal addCode returned bodyRun
  rw [returnedEq] at bodyRun
  have regularFits : gas.toNat + spill.toNat < 2 ^ 64 := by
    simp only [regularBudget, wordAt, pools.gas, pools.spill, WitnessRadix.MemoryBytes.wordBits] at cap
    omega
  have callerFrame : emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - (paid + 1)} := by
    change emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - 1 - paid} at frameEq
    have subtract : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
    simpa only [subtract] using frameEq
  have actual := ignored_return source post (ofString "charge_state_gas") expressions [.val (.word amount)] body callee (paid + 1) args called positive bodyRun callerFrame
  have same := congrArg Prod.snd (normal.symm.trans actual)
  change target = {source with memory := post.memory, clock := source.clock - (paid + 1)} at same
  have budget := preserves_regular_budget source frame gas state spill amount pools affordable regularFits
  have postMemory : post.memory = WitnessRadix.WordWrites.write source.memory (poolWrites frame gas state spill amount) := memory
  refine ⟨paid + 1, by omega, ?_, by omega, ?_, affordable, ?_, ?_, ?_⟩
  · change paid ≤ source.clock - 1 at fits
    omega
  · rw [same]
  · rw [same]; exact postMemory
  · rw [same]
  · rw [same, postMemory]; exact budget

end InitECandidate.Solver.GasBudget.StateCharge

#print axioms InitECandidate.Solver.GasBudget.StateCharge.call_normal
