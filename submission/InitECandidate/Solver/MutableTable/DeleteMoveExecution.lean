import InitECandidate.Solver.MutableTable.DeleteMoveStores
import InitECandidate.Solver.MutableTable.DeleteMovePending

namespace InitECandidate.Solver.MutableTable.Delete.Move
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem stores_copy_memory (input : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (hole slot ordinal : Nat) (value : BitVec 64) (holeInside : hole < plan.capacity) :
    storesMemory (CopyGeneral.resultMemory input be (cell plan .keys 0 + BitVec.ofNat 64 slot * BitVec.ofNat 64 (stride kind))
      (cell plan .keys 0 + BitVec.ofNat 64 hole * BitVec.ofNat 64 (stride kind)) (KeyHash.keySize kind)) plan hole ordinal value =
      memory input be kind plan hole slot ordinal value := by
  simp only [storesMemory, memory, copiedMemory, MemoryModel.copiedValueMemory, MemoryModel.valueMemory, parameters,
    natural_word_address kind plan valid .values hole holeInside]

/-- Complete real movable deletion branch: actual general memcpy, all reads
and stores, hole assignment and local restoration. The resulting pending
invariant and unchanged physical header follow from the executed memory. -/
theorem execute_pending (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat)
    (pending : Delete.Pending source kind plan count deleted entries hole) (moved : Fin count) (active : moved ≠ deleted)
    (locals : Locals source kind plan hole (entries moved)) (value : BitVec 64)
    (valueCell : source.memory (cell plan .values (8 * entries moved)) = .word value)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 count))
    (code : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ≤ source.clock) :
    ∃ paid, paid ≤ MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ∧
      evaluateHOLFiniteState source Delete.moveBranch =
        (none, WitnessRadix.QueryBranch.bind {source with
          memory := (memory source.memory source.be kind plan hole (entries moved) moved.val value)
          clock := source.clock - paid} "i" (BitVec.ofNat 64 (entries moved))) ∧
      Delete.Pending (WitnessRadix.QueryBranch.bind {source with
          memory := (memory source.memory source.be kind plan hole (entries moved) moved.val value)
          clock := source.clock - paid} "i" (BitVec.ofNat 64 (entries moved)))
        kind plan count deleted (Function.update entries moved hole) (entries moved) ∧
      MemoryModel.Header (memory source.memory source.be kind plan hole (entries moved) moved.val value) kind plan (BitVec.ofNat 64 count) := by
  let slot := entries moved
  let src := cell plan .keys 0 + BitVec.ofNat 64 slot * BitVec.ofNat 64 (stride kind)
  let dst := cell plan .keys 0 + BitVec.ofNat 64 hole * BitVec.ofNat 64 (stride kind)
  let paid := CopyGeneral.cost src dst (KeyHash.keySize kind) + 1
  let copied := CopyGeneral.callState source src dst (KeyHash.keySize kind)
  have slotInside : slot < plan.capacity := pending.inside moved active
  have ordinalInside : moved.val < plan.capacity := Nat.lt_trans moved.isLt pending.room
  have sourceVector : (BitVec.ofNat 64 slot).toNat < plan.capacity := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans slotInside (capacity_small kind plan valid))]
    exact slotInside
  have destinationVector : (BitVec.ofNat 64 hole).toNat < plan.capacity := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans pending.holeInside (capacity_small kind plan valid))]
    exact pending.holeInside
  have srcFits : src.toNat + KeyHash.keySize kind < 2 ^ 64 := slot_fits kind plan valid 0#64 _ sourceVector
  have dstFits : dst.toNat + KeyHash.keySize kind < 2 ^ 64 := slot_fits kind plan valid 0#64 _ destinationVector
  have srcMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress src offset)) := by
    intro offset inside
    rw [domain]
    exact slot_mapped kind plan valid 0#64 _ sourceVector offset inside
  have dstMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress dst offset)) := by
    intro offset inside
    rw [domain]
    exact slot_mapped kind plan valid 0#64 _ destinationVector offset inside
  have paidBound : paid ≤ MemeqByteRuntime.price (KeyHash.keySize kind) + 1 := Nat.add_le_add_right (CopyMapped.cost_le_price src dst _) 1
  have smallWidth : KeyHash.keySize kind ≤ 64 := by cases kind <;> decide
  have copyRun := CopyGeneral.call_execute source _ src dst (KeyHash.keySize kind) (copy_arguments source kind plan hole slot locals) code
    (CopyMapped.of_regions source src dst _ srcFits dstFits srcMapped dstMapped) (by omega) (Nat.le_trans paidBound enough)
  have valueKept : copied.memory (cell plan .values (8 * slot)) = .word value :=
    (CopyGeneral.call_memory_away source src dst _ _ (pool_key_away kind plan valid src (BitVec.ofNat 64 hole) destinationVector .values (by decide) _
      (by change 8 * slot < 8 * plan.capacity; omega))).trans valueCell
  have positionKept : copied.memory (cell plan .position (8 * slot)) = .word (BitVec.ofNat 64 moved.val) :=
    (CopyGeneral.call_memory_away source src dst _ _ (pool_key_away kind plan valid src (BitVec.ofNat 64 hole) destinationVector .position (by decide) _
      (by change 8 * slot < 8 * plan.capacity; omega))).trans (pending.position moved active)
  have tailRun := after_copy_execute copied kind plan valid domain hole slot moved.val value pending.holeInside slotInside ordinalInside
    (Locals.of_locals source copied kind plan hole slot locals rfl) valueKept positionKept
  refine ⟨paid, paidBound, ?_, ?_, Move.header source.memory source.be kind plan valid hole slot moved.val value _ pending.holeInside ordinalInside header⟩
  · rw [branch_shape, StateSteps.next_sequence source copied Delete.copyCall afterCopy copyRun (Nat.sub_le _ _), tailRun]
    change (none, WitnessRadix.QueryBranch.bind {source with
      memory := (storesMemory (CopyGeneral.resultMemory source.memory source.be src dst (KeyHash.keySize kind)) plan hole moved.val value)
      clock := source.clock - paid} "i" (BitVec.ofNat 64 slot)) = _
    rw [stores_copy_memory source.memory source.be kind plan valid hole slot moved.val value pending.holeInside]
  · have post := Delete.Pending.after_move source kind plan valid count deleted entries hole pending moved active value
    exact Delete.Pending.of_fields _ _ kind plan count deleted _ _ post rfl rfl rfl

end InitECandidate.Solver.MutableTable.Delete.Move

#print axioms InitECandidate.Solver.MutableTable.Delete.Move.stores_copy_memory
#print axioms InitECandidate.Solver.MutableTable.Delete.Move.execute_pending
