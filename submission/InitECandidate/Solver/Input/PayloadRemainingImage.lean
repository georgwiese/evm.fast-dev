import InitECandidate.Solver.Input.PayloadRemainingProgram
import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- The concrete eleven final field values at this physical payload state. -/
def RemainingImage (input : Guest.InputBlob) (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record : BitVec 64) (length : Nat) (count : BitVec 64) : Prop :=
  ∀ field ∈ remainingFields input pointer (BitVec.ofNat 64 length) (offsetWords input 2) (offsetWords input 3) count,
    state.memory (record + BitVec.ofNat 64 field.1) = .word field.2.2

/-- Literal source-order writes materialize every remaining field. -/
theorem remaining_image (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer record count : BitVec 64) (length : Nat) (room : record.toNat + 136 ≤ 33806089496) :
    RemainingImage input (emptyLocalsHOLFinite (applyFields source record
      (remainingFields input pointer (BitVec.ofNat 64 length) (offsetWords input 2) (offsetWords input 3) count)))
      pointer record length count := by
  intro field member
  have actual := applyFields_cell source record room _
    (fun item present => (remaining_valid input pointer (BitVec.ofNat 64 length) (offsetWords input 2) (offsetWords input 3) count item present).1)
    field.1 (remaining_valid input pointer (BitVec.ofNat 64 length) (offsetWords input 2) (offsetWords input 3) count field member).1
  simp only [remainingFields, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simpa [cellValue, remainingFields, emptyLocalsHOLFinite] using actual

theorem RemainingImage.of_memory {input : Guest.InputBlob}
    {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer record count : BitVec 64} {length : Nat}
    (data : RemainingImage input source pointer record length count) (room : record.toNat + 136 ≤ 33806089496)
    (memory : ∀ query : BitVec 64, record.toNat ≤ query.toNat → query.toNat < record.toNat + 136 → target.memory query = source.memory query) :
    RemainingImage input target pointer record length count := by
  intro field member
  have small := (remaining_valid input pointer (BitVec.ofNat 64 length) (offsetWords input 2) (offsetWords input 3) count field member).1
  have encoded : (BitVec.ofNat 64 field.1).toNat = field.1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have number : (record + BitVec.ofNat 64 field.1).toNat = record.toNat + field.1 := by
    rw [BitVec.toNat_add_of_lt (by rw [encoded]; omega), encoded]
  exact (memory _ (by rw [number]; omega) (by rw [number]; omega)).trans (data field member)

theorem RemainingImage.of_frame {input : Guest.InputBlob}
    {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer record count : BitVec 64} {length : Nat}
    (data : RemainingImage input source pointer record length count)
    (frame : LocalEffects.erase target = LocalEffects.erase source) : RemainingImage input target pointer record length count := by
  have memory := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) frame
  change target.memory = source.memory at memory
  intro field member
  rw [memory]
  exact data field member

/-- The actual variable-size withdrawal/balance fields consumed by hashing. -/
theorem RemainingImage.hash_fields {input : Guest.InputBlob}
    {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer record count : BitVec 64} {length : Nat}
    (data : RemainingImage input source pointer record length count) :
    source.memory (record + 48#64) = .word (pointer + 62#64 + offsetWords input 2) ∧
    source.memory (record + 56#64) = .word count ∧
    source.memory (record + 64#64) = .word (pointer + 62#64 + offsetWords input 3) ∧
    source.memory (record + 72#64) = .word (BitVec.ofNat 64 length - offsetWords input 3) := by
  exact ⟨data (48, .op .add [localVar "p", localVar "o_wd"], pointer + 62#64 + offsetWords input 2) (by simp [remainingFields]),
    data (56, localVar "nwd", count) (by simp [remainingFields]),
    data (64, .op .add [localVar "p", localVar "o_bal"], pointer + 62#64 + offsetWords input 3) (by simp [remainingFields]),
    data (72, .op .sub [localVar "len", localVar "o_bal"], BitVec.ofNat 64 length - offsetWords input 3) (by simp [remainingFields])⟩

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.remaining_image
#print axioms InitECandidate.Solver.Input.Payload.RemainingImage.of_memory
#print axioms InitECandidate.Solver.Input.Payload.RemainingImage.of_frame
#print axioms InitECandidate.Solver.Input.Payload.RemainingImage.hash_fields
