import InitECandidate.Solver.MutableTable.TableRuntime.ClearFrame
import InitECandidate.Solver.MutableTable.TableRuntime.Call
import InitECandidate.Solver.MutableTable.MemoryModel

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

theorem result_before (memory : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (start capacity : Nat)
    (valid : Valid kind (fresh kind start capacity)) (offset : Nat) (before : offset < 48) (value : BitVec 64)
    (member : (cell (fresh kind start capacity) .header offset, value) ∈ beforeWrites kind start capacity) :
    resultMemory memory be kind start capacity (cell (fresh kind start capacity) .header offset) = .word value := by
  rw [resultMemory, WordWrites.write_away _ _ _ (after_away kind start capacity valid offset before),
    clear_pool_away _ be kind start capacity valid .header (by decide) offset (by change offset < 72; omega)]
  exact WordWrites.write_unique memory _ _ (before_distinct kind start capacity valid) member

theorem result_after (memory : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (start capacity : Nat)
    (valid : Valid kind (fresh kind start capacity)) (entry : BitVec 64 × BitVec 64) (member : entry ∈ afterWrites kind start capacity) :
    resultMemory memory be kind start capacity entry.1 = .word entry.2 :=
  WordWrites.write_unique _ _ entry (after_distinct kind start capacity valid) member

/-- The complete original constructor memory establishes the actual nine
header words for every original key width. -/
theorem result_header (memory : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (start capacity : Nat)
    (valid : Valid kind (fresh kind start capacity)) :
    MemoryModel.Header (resultMemory memory be kind start capacity) kind (fresh kind start capacity) 0#64 := by
  intro offset value member
  simp only [MemoryModel.headerEntries, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact result_before memory be kind start capacity valid 0 (by decide) _ (by simp [beforeWrites, cell, fresh, BitVec.ofNat_add])
  · exact result_before memory be kind start capacity valid 8 (by decide) _ (by simp [beforeWrites, cell, fresh, BitVec.ofNat_add])
  · exact result_before memory be kind start capacity valid 16 (by decide) _ (by simp [beforeWrites, cell, fresh, BitVec.ofNat_add])
  · exact result_before memory be kind start capacity valid 24 (by decide) _ (by simp [beforeWrites, cell, fresh, BitVec.ofNat_add])
  · exact result_before memory be kind start capacity valid 32 (by decide) _ (by simp [beforeWrites, cell, fresh, BitVec.ofNat_add])
  · exact result_before memory be kind start capacity valid 40 (by decide) _ (by simp [beforeWrites, cell, fresh, BitVec.ofNat_add])
  · exact result_after memory be kind start capacity valid (cell (fresh kind start capacity) .header 48, cell (fresh kind start capacity) .used 0) (by simp [afterWrites, usedAddress, cell, fresh, BitVec.ofNat_add])
  · exact result_after memory be kind start capacity valid (cell (fresh kind start capacity) .header 56, cell (fresh kind start capacity) .order 0) (by simp [afterWrites, usedAddress, cell, fresh, BitVec.ofNat_add])
  · exact result_after memory be kind start capacity valid (cell (fresh kind start capacity) .header 64, cell (fresh kind start capacity) .position 0) (by simp [afterWrites, usedAddress, cell, fresh, BitVec.ofNat_add])

theorem entered_header {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat)
    (valid : Valid kind (fresh kind start capacity)) :
    MemoryModel.Header (enteredState source kind start capacity).memory kind (fresh kind start capacity) 0#64 := by
  rw [entered_memory]
  exact result_header source.memory source.be kind start capacity valid

theorem caller_header {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (kind : KeyHash.Kind) (start capacity : Nat)
    (valid : Valid kind (fresh kind start capacity)) :
    MemoryModel.Header (callState source name kind start capacity).memory kind (fresh kind start capacity) 0#64 :=
  result_header source.memory source.be kind start capacity valid

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.result_before
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.result_after
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.result_header
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.entered_header
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.caller_header
