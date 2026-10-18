import InitECandidate.Solver.GasBudget.ChildErrorMemory
import InitECandidate.Solver.GasBudget.FrameSums

namespace InitECandidate.Solver.GasBudget.ChildError
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Real child-error completion preserves the live used sum when the child
is removed, and preserves budget after accounting for the child's omitted
spill. Current ancestor ownership and live budget cap remain explicit. -/
theorem call_sums (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (parent child : BitVec 64) (p c : Amounts)
    (ancestors : List (BitVec 64))
    (ancestorSafe : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      ancestor + BitVec.ofNat 64 offset ∉ (writes parent p c).map Prod.fst)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions = some [.val (.word child)])
    (code : source.code.lookup (ofString "incorporate_child_on_error") = some (formals, body, .one))
    (ready : Ready source parent child p c)
    (cap : regularBudget source.memory parent + regularBudget source.memory child ≤ 16777216)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "incorporate_child_on_error") expressions) = (none, target)) :
    1 ≤ source.clock ∧ target.clock = source.clock - 1 ∧
      FrameSums.used target.memory (parent :: ancestors) = FrameSums.used source.memory (parent :: child :: ancestors) ∧
      FrameSums.budget target.memory (parent :: ancestors) + (wordAt source.memory (child + 192#64)).toNat =
        FrameSums.budget source.memory (parent :: child :: ancestors) ∧
      FrameSums.budget target.memory (parent :: ancestors) ≤ FrameSums.budget source.memory (parent :: child :: ancestors) := by
  obtain ⟨positive, canonical⟩ := call_memory source target parent child p c expressions args code ready normal
  have memoryEq := congrArg PanSemStateFiniteExact.memory canonical
  change target.memory = WordWrites.write source.memory (writes parent p c) at memoryEq
  have parentGas : source.memory (parent + 64#64) = .word p.gas := ready.parentCells 64 (by simp [offsets])
  have parentUsed : source.memory (parent + 184#64) = .word p.used := ready.parentCells 184 (by simp [offsets])
  have childGas : source.memory (child + 64#64) = .word c.gas := ready.childCells 64 (by simp [offsets])
  have childUsed : source.memory (child + 184#64) = .word c.used := ready.childCells 184 (by simp [offsets])
  have numbers := cap
  simp only [regularBudget, wordAt, parentGas, parentUsed, childGas, childUsed, MemoryBytes.wordBits] at numbers
  have gasFits : p.gas.toNat + c.gas.toNat < 2^64 := by omega
  have usedFits : p.used.toNat + c.used.toNat < 2^64 := by omega
  have ancestorWords : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      target.memory (ancestor + BitVec.ofNat 64 offset) = source.memory (ancestor + BitVec.ofNat 64 offset) := by
    intro ancestor member offset inside
    rw [memoryEq]
    exact WordWrites.write_away source.memory _ _ (ancestorSafe ancestor member offset inside)
  have ancestorBudget := FrameSums.budget_congr source.memory target.memory ancestors ancestorWords
  have ancestorUsed := FrameSums.used_congr source.memory target.memory ancestors (by intro ancestor member; exact ancestorWords ancestor member 184 (by simp))
  have distinct : ((writes parent p c).map Prod.fst).Nodup := by
    simp [writes, offsets_ne parent 64#64 72#64 (by decide), offsets_ne parent 64#64 184#64 (by decide), offsets_ne parent 72#64 184#64 (by decide)]
  have combinedUsed : target.memory (parent + 184#64) = .word (p.used + c.used) := by
    rw [memoryEq]
    exact WordWrites.write_unique source.memory _ (parent + 184#64, p.used + c.used) distinct (by simp [writes])
  have usedSum : FrameSums.used target.memory (parent :: ancestors) = FrameSums.used source.memory (parent :: child :: ancestors) := by
    change (wordAt target.memory (parent + 184#64)).toNat + FrameSums.used target.memory ancestors =
      (wordAt source.memory (parent + 184#64)).toNat + ((wordAt source.memory (child + 184#64)).toNat + FrameSums.used source.memory ancestors)
    rw [ancestorUsed]
    simp only [wordAt, combinedUsed, parentUsed, childUsed, MemoryBytes.wordBits, BitVec.toNat_add_of_lt usedFits]
    omega
  have transfer := budget_transfer source parent child p c ready gasFits usedFits
  rw [← memoryEq] at transfer
  have budgetSum : FrameSums.budget target.memory (parent :: ancestors) + (wordAt source.memory (child + 192#64)).toNat = FrameSums.budget source.memory (parent :: child :: ancestors) := by
    change regularBudget target.memory parent + FrameSums.budget target.memory ancestors + _ =
      regularBudget source.memory parent + (regularBudget source.memory child + FrameSums.budget source.memory ancestors)
    rw [ancestorBudget]
    omega
  exact ⟨positive, by rw [canonical], usedSum, budgetSum, by omega⟩

end InitECandidate.Solver.GasBudget.ChildError

#print axioms InitECandidate.Solver.GasBudget.ChildError.call_sums
