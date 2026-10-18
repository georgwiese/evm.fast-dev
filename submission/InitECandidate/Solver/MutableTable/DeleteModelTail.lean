import InitECandidate.Solver.MutableTable.DeleteModelPost

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix

def tailPrice (kind : KeyHash.Kind) (count : Nat) : Nat := scanPrice kind * (count - 1) + 1

/-- Actual cap read, absent return or complete present-deletion suffix.
The present ordinal is obtained from the real physical occupied list. -/
theorem model_tail (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (room : slots.length < plan.capacity) (occupied : MemoryModel.Occupied source kind plan slots)
    (bits : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length)) (index : BitVec 64)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (presentMember : index ≠ BitVec.ofNat 64 plan.capacity → index.toNat ∈ slots)
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : tailPrice kind slots.length ≤ source.clock) :
    ∃ paid memory target next flag, paid ≤ tailPrice kind slots.length ∧
      evaluateHOLFiniteState source afterIndex = (some (.returned (.val (.word flag))), target) ∧
      ModelPost source kind plan slots paid memory target next flag := by
  let cap := BitVec.ofNat 64 plan.capacity
  let entered := bind source "cap" cap
  let test : ProgHOL 64 := .ite (.cmp .equal (localVar "i") (localVar "cap")) returnZero .skip
  have mappedCap : source.memaddrs (cell plan .header 0 + 16#64) := by
    rw [domain, constant_cell]
    exact mapped kind plan valid .header 16 (by change 16 < 72; decide) (by decide)
  have storedCap : source.memory (cell plan .header 0 + 16#64) = .word cap := by
    rw [constant_cell]
    exact header 16 cap (by simp [MemoryModel.headerEntries, cap])
  have capRead := Find.table_read source _ 16#64 cap tableLocal mappedCap storedCap
  have enteredI : entered.locals.lookup (ofString "i") = some (.val (.word index)) := (bind_lookup_other _ "cap" "i" _ (by decide)).trans indexLocal
  have enteredCap : entered.locals.lookup (ofString "cap") = some (.val (.word cap)) := bind_lookup_same _ _ _
  by_cases absent : index = cap
  · have testRun : evaluateHOLFiniteState entered test = (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite entered) := by
      simp [test, evaluateHOLFiniteState_ite, localVar, evalHOLExact, toExact, enteredI, enteredCap, absent,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, returnZero, evaluateHOLFiniteState_return, shapeOfHOLExact]
    have inner : evaluateHOLFiniteState entered (.seq test (program headerActions afterHeaders)) = (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite entered) :=
      StateSteps.stopped_sequence entered _ test _ _ testRun (Nat.le_refl _)
    have scopeRun := Input.ScalarScope.declare_execute source _ "cap" (Find.tableLoad 16#64) cap (.seq test (program headerActions afterHeaders)) _ capRead inner
    let target := restore source "cap" (emptyLocalsHOLFinite entered)
    refine ⟨0, source.memory, target, slots, 0#64, Nat.zero_le _, scopeRun, ?_⟩
    exact ⟨by simp only [target, entered, restore, emptyLocalsHOLFinite, Nat.sub_zero, WitnessRadix.QueryBranch.bind, setVarHOLFinite], Or.inl ⟨rfl, rfl, rfl⟩, header,
      MemoryModel.Occupied.of_fields source target kind plan slots occupied rfl rfl rfl⟩
  · obtain ⟨deleted, selected⟩ := List.mem_iff_get.mp (presentMember absent)
    have indexWord : BitVec.ofNat 64 (slots.get deleted) = index := by
      rw [selected, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have enteredModel := MemoryModel.Occupied.of_fields source entered kind plan slots occupied rfl rfl rfl
    have enteredT : entered.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))) := (bind_lookup_other _ "cap" "t" _ (by decide)).trans tableLocal
    obtain ⟨paid, memory, target, next, bounded, presentRun, frame, length, nextHeader, nextModel⟩ :=
      present_execute entered kind plan valid domain little slots room enteredModel deleted bits small power header enteredT
        (by rw [indexWord]; exact enteredI) enteredCap hashCode copyCode enough
    have skipRun : evaluateHOLFiniteState entered test = (none, entered) := by
      simp [test, evaluateHOLFiniteState_ite, localVar, evalHOLExact, toExact, enteredI, enteredCap, absent,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have inner : evaluateHOLFiniteState entered (.seq test (program headerActions afterHeaders)) = (some (.returned (.val (.word 1#64))), target) := by
      rw [StateSteps.next_sequence entered entered test _ skipRun (Nat.le_refl _), presentRun]
    have scopeRun := Input.ScalarScope.declare_execute source _ "cap" (Find.tableLoad 16#64) cap (.seq test (program headerActions afterHeaders)) _ capRead inner
    refine ⟨paid, memory, restore source "cap" target, next, 1#64, bounded, scopeRun, ?_⟩
    refine ⟨frame, Or.inr ⟨rfl, ?_⟩, nextHeader, MemoryModel.Occupied.of_fields target _ kind plan next nextModel rfl rfl rfl⟩
    have positive : 0 < slots.length := by have := deleted.isLt; omega
    omega

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.model_tail
