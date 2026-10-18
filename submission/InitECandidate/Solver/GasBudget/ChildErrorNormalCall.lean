import InitECandidate.Solver.GasBudget.ChildErrorCall
import InitECandidate.Solver.Input.IgnoredCallNormal

namespace InitECandidate.Solver.GasBudget.ChildError
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual child-error incorporation needs no supplied clock allowance or
sum-fit oracle. The capped live parent/child ledger supplies no-wrap; the
normal caller supplies its single call clock. Spill remains accounted for. -/
theorem call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (parent child : BitVec 64) (p c : Amounts)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions = some [.val (.word child)])
    (code : source.code.lookup (ofString "incorporate_child_on_error") = some (formals, body, .one))
    (ready : Ready source parent child p c)
    (cap : regularBudget source.memory parent + regularBudget source.memory child ≤ 16777216)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "incorporate_child_on_error") expressions) = (none, target)) :
    1 ≤ source.clock ∧ target.clock = source.clock - 1 ∧
      (∃ memory, target = {source with memory := memory, clock := source.clock - 1}) ∧
      regularBudget target.memory parent + (wordAt source.memory (child + 192#64)).toNat =
        regularBudget source.memory parent + regularBudget source.memory child ∧
      regularBudget target.memory parent ≤ 16777216 := by
  obtain ⟨callee, called, childLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "incorporate_child_on_error") "child" body child code
  obtain ⟨positive, post, returned, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "incorporate_child_on_error") expressions _ body callee .one args called normal
  have pGas : source.memory (parent + 64#64) = .word p.gas := ready.parentCells 64 (by simp [offsets])
  have pUsed : source.memory (parent + 184#64) = .word p.used := ready.parentCells 184 (by simp [offsets])
  have cGas : source.memory (child + 64#64) = .word c.gas := ready.childCells 64 (by simp [offsets])
  have cUsed : source.memory (child + 184#64) = .word c.used := ready.childCells 184 (by simp [offsets])
  have capped := cap
  simp only [regularBudget, wordAt, pGas, pUsed, cGas, cUsed, WitnessRadix.MemoryBytes.wordBits] at capped
  have gasFits : p.gas.toNat + c.gas.toNat < 2 ^ 64 := by omega
  have usedFits : p.used.toNat + c.used.toNat < 2 ^ 64 := by omega
  obtain ⟨memory, actual, transferred⟩ := call_execute source parent child p c expressions args code ready gasFits usedFits positive
  have targetEq := congrArg Prod.snd (normal.symm.trans actual)
  change target = {source with memory := memory, clock := source.clock - 1} at targetEq
  subst target
  exact ⟨positive, rfl, ⟨memory, rfl⟩, transferred, by change regularBudget memory parent ≤ 16777216; omega⟩

end InitECandidate.Solver.GasBudget.ChildError

#print axioms InitECandidate.Solver.GasBudget.ChildError.call_normal
