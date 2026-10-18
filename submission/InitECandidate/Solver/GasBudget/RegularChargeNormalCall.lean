import InitECandidate.Solver.GasBudget.RegularChargeEntry
import InitECandidate.Solver.Input.IgnoredCallNormal

namespace InitECandidate.Solver.GasBudget.RegularCharge
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A reached actual normal charge derives its available call clock, frame
cell mappings/words and affordability. The physical capped ledger supplies
non-wrap, so both debit and counter credit are exact natural arithmetic. -/
theorem call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame amount : BitVec 64)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions = some [.val (.word amount)])
    (code : source.code.lookup (ofString "charge_gas") = some (formals, body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "charge_gas") expressions) = (none, target)) :
    ∃ gas used : BitVec 64,
      1 ≤ source.clock ∧ target.clock = source.clock - 1 ∧
      source.memaddrs (frame + 64#64) ∧ source.memaddrs (frame + 184#64) ∧
      source.memory (frame + 64#64) = .word gas ∧ source.memory (frame + 184#64) = .word used ∧ amount ≤ gas ∧
      target = {source with memory := target.memory, clock := source.clock - 1} ∧
      regularBudget target.memory frame = regularBudget source.memory frame ∧
      (wordAt target.memory (frame + 64#64)).toNat + amount.toNat = gas.toNat ∧
      (wordAt target.memory (frame + 184#64)).toNat = used.toNat + amount.toNat := by
  obtain ⟨callee, called, amountLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "charge_gas") "amount" body amount code
  obtain ⟨positive, post, returned, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "charge_gas") expressions [.val (.word amount)] body callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨gas, used, gasMapped, usedMapped, gasCell, usedCell, affordable⟩ := normal_entry entry post frame amount ev amountLocal returned bodyRun
  have fits := ledger_fits source frame gas used gasCell usedCell cap
  obtain ⟨memory, actual, budget, debit, credit⟩ := call_execute source frame gas used amount expressions args code ev gasMapped usedMapped gasCell usedCell affordable fits positive
  have same := congrArg Prod.snd (normal.symm.trans actual)
  change target = {source with memory := memory, clock := source.clock - 1} at same
  refine ⟨gas, used, positive, ?_, gasMapped, usedMapped, gasCell, usedCell, affordable, ?_, ?_, ?_, ?_⟩
  · rw [same]
  · rw [same]
  · rw [same]; exact budget
  · rw [same]; exact debit
  · rw [same]; exact credit

/-- Every positive actual charge strictly advances the irreversible regular
counter, provided the incoming physical ledger is capped. -/
theorem positive_progress (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame amount used : BitVec 64)
    (usedCell : source.memory (frame + 184#64) = .word used)
    (credit : (wordAt target.memory (frame + 184#64)).toNat = used.toNat + amount.toNat) (positive : 0 < amount.toNat) :
    (wordAt source.memory (frame + 184#64)).toNat < (wordAt target.memory (frame + 184#64)).toNat := by
  rw [credit]
  simp only [wordAt, usedCell, WitnessRadix.MemoryBytes.wordBits]
  omega

end InitECandidate.Solver.GasBudget.RegularCharge

#print axioms InitECandidate.Solver.GasBudget.RegularCharge.call_normal
#print axioms InitECandidate.Solver.GasBudget.RegularCharge.positive_progress
