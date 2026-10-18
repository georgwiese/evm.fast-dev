import InitECandidate.Solver.GasBudget.ChildSuccessNormalPrefix
import InitECandidate.Solver.GasBudget.FrameSums

namespace InitECandidate.Solver.GasBudget.ChildSuccess
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

theorem memory_after_away (memory : Memory) (parent : BitVec 64) (p c : ChildError.Amounts) (parentSpill childSpill address : BitVec 64)
    (notGas : address ≠ parent + 64#64) (notState : address ≠ parent + 72#64)
    (notUsed : address ≠ parent + 184#64) (notSpill : address ≠ parent + 192#64) :
    memoryAfter memory parent p c parentSpill childSpill address = memory address := by
  unfold memoryAfter
  rw [WordWrites.write_away _ _ address (by simp [Repayment.writes, notGas, notState, notSpill])]
  rw [StoreWord.put, if_neg notSpill]
  exact WordWrites.write_away memory _ address (by simp [ChildError.writes, notGas, notState, notUsed])

theorem memory_after_used (memory : Memory) (parent : BitVec 64) (p c : ChildError.Amounts) (parentSpill childSpill : BitVec 64) :
    memoryAfter memory parent p c parentSpill childSpill (parent + 184#64) = .word (p.used + c.used) := by
  have distinct : ((ChildError.writes parent p c).map Prod.fst).Nodup := by
    simp [ChildError.writes, offsets_ne parent 64#64 72#64 (by decide), offsets_ne parent 64#64 184#64 (by decide), offsets_ne parent 72#64 184#64 (by decide)]
  have first := WordWrites.write_unique memory (ChildError.writes parent p c) (parent + 184#64, p.used + c.used) distinct (by simp [ChildError.writes])
  unfold memoryAfter
  rw [WordWrites.write_away _ _ (parent + 184#64) (by simp [Repayment.writes,
    offsets_ne parent 184#64 64#64 (by decide), offsets_ne parent 184#64 72#64 (by decide), offsets_ne parent 184#64 192#64 (by decide)])]
  rw [StoreWord.put, if_neg (offsets_ne parent 184#64 192#64 (by decide))]
  exact first

/-- The genuine successful-child prefix reaches its real log/union suffix
with live used and budget sums conserved as the child is merged/removed.
The later log/table suffix and reachable ancestor ownership remain open. -/
theorem body_normal_sums (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (parent child : BitVec 64)
    (p c : ChildError.Amounts) (parentSpill childSpill : BitVec 64) (ancestors : List (BitVec 64))
    (apart : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat), ∀ field ∈ ([64, 72, 184, 192] : List Nat),
      ancestor + BitVec.ofNat 64 offset ≠ parent + BitVec.ofNat 64 field)
    (ready : Ready source parent child p c parentSpill childSpill)
    (code : source.code.lookup (ofString "incorporate_child_on_error") = some (ChildError.formals, ChildError.body, .one))
    (cap : regularBudget source.memory parent + regularBudget source.memory child ≤ 16777216)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    1 ≤ source.clock ∧ ∃ entered finish,
      emptyLocalsHOLFinite entered = emptyLocalsHOLFinite {source with memory := entered.memory, clock := source.clock - 1} ∧
      FrameSums.used entered.memory (parent :: ancestors) = FrameSums.used source.memory (parent :: child :: ancestors) ∧
      FrameSums.budget entered.memory (parent :: ancestors) = FrameSums.budget source.memory (parent :: child :: ancestors) ∧
      evaluateHOLFiniteState entered suffix = (some (.returned returned), finish) ∧ post = restore source "rep" finish := by
  have priorContract := body_normal_prefix source post parent child p c parentSpill childSpill ready code cap returned normal
  have positive := priorContract.1
  obtain ⟨entered, memoryEq, frame, budget, locals, execute⟩ := execute_prefix_full source parent child p c parentSpill childSpill ready code (by omega) positive
  have whole := normal
  rw [body_shape, execute suffix] at whole
  let finish := (evaluateHOLFiniteState entered suffix).2
  have result := congrArg Prod.fst whole
  change (evaluateHOLFiniteState entered suffix).1 = some (.returned returned) at result
  have final := congrArg Prod.snd whole
  have ancestorWords : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      entered.memory (ancestor + BitVec.ofNat 64 offset) = source.memory (ancestor + BitVec.ofNat 64 offset) := by
    intro ancestor member offset inside
    rw [memoryEq]
    exact memory_after_away source.memory parent p c parentSpill childSpill _
      (apart ancestor member offset inside 64 (by simp)) (apart ancestor member offset inside 72 (by simp))
      (apart ancestor member offset inside 184 (by simp)) (apart ancestor member offset inside 192 (by simp))
  have ancestorBudget := FrameSums.budget_congr source.memory entered.memory ancestors ancestorWords
  have ancestorUsed := FrameSums.used_congr source.memory entered.memory ancestors (by intro ancestor member; exact ancestorWords ancestor member 184 (by simp))
  have parentGas : source.memory (parent + 64#64) = .word p.gas := ready.parentCells 64 (by simp [ChildError.offsets])
  have parentUsed : source.memory (parent + 184#64) = .word p.used := ready.parentCells 184 (by simp [ChildError.offsets])
  have childGas : source.memory (child + 64#64) = .word c.gas := ready.childCells 64 (by simp [ChildError.offsets])
  have childUsed : source.memory (child + 184#64) = .word c.used := ready.childCells 184 (by simp [ChildError.offsets])
  have numbers := cap
  simp only [regularBudget, wordAt, parentGas, parentUsed, childGas, childUsed, MemoryBytes.wordBits] at numbers
  have usedFits : p.used.toNat + c.used.toNat < 2^64 := by omega
  have combinedUsed : entered.memory (parent + 184#64) = .word (p.used + c.used) := by rw [memoryEq]; exact memory_after_used _ _ _ _ _ _
  have usedSum : FrameSums.used entered.memory (parent :: ancestors) = FrameSums.used source.memory (parent :: child :: ancestors) := by
    change (wordAt entered.memory (parent + 184#64)).toNat + FrameSums.used entered.memory ancestors =
      (wordAt source.memory (parent + 184#64)).toNat + ((wordAt source.memory (child + 184#64)).toNat + FrameSums.used source.memory ancestors)
    rw [ancestorUsed]
    simp only [wordAt, combinedUsed, parentUsed, childUsed, MemoryBytes.wordBits, BitVec.toNat_add_of_lt usedFits]
    omega
  have budgetSum : FrameSums.budget entered.memory (parent :: ancestors) = FrameSums.budget source.memory (parent :: child :: ancestors) := by
    change regularBudget entered.memory parent + FrameSums.budget entered.memory ancestors =
      regularBudget source.memory parent + (regularBudget source.memory child + FrameSums.budget source.memory ancestors)
    rw [ancestorBudget, budget]
    omega
  exact ⟨positive, entered, finish, frame, usedSum, budgetSum, Prod.ext result rfl, final.symm⟩

end InitECandidate.Solver.GasBudget.ChildSuccess

#print axioms InitECandidate.Solver.GasBudget.ChildSuccess.memory_after_away
#print axioms InitECandidate.Solver.GasBudget.ChildSuccess.memory_after_used
#print axioms InitECandidate.Solver.GasBudget.ChildSuccess.body_normal_sums
