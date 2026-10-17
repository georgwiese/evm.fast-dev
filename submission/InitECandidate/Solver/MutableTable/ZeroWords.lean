import InitECandidate.Solver.WitnessRadix.ZeroMemory
import InitECandidate.Solver.WitnessRadix.Copy32Memory

namespace InitECandidate.Solver.MutableTable.ZeroWords
open Flapjack WitnessRadix

theorem writes_preserve (memory : WordWrites.Memory) (writes : List (BitVec 64×BitVec 64))
    (zero : ∀ entry∈writes,entry.2=0#64) (query : BitVec 64) (old : memory query=.word 0#64) :
    WordWrites.write memory writes query=.word 0#64 := by
  induction writes generalizing memory with
  | nil=>exact old
  | cons entry rest ih=>
    rw [WordWrites.write]
    apply ih _ (by intro next member;exact zero next (List.mem_cons_of_mem entry member))
    by_cases same : query=entry.1
    · simp only [StoreWord.put,if_pos same,zero entry (List.mem_cons_self)]
    · simpa only [StoreWord.put,if_neg same] using old

theorem writes_member (memory : WordWrites.Memory) (writes : List (BitVec 64×BitVec 64))
    (zero : ∀ entry∈writes,entry.2=0#64) (query : BitVec 64) (member : (query,0#64)∈writes) :
    WordWrites.write memory writes query=.word 0#64 := by
  induction writes generalizing memory with
  | nil=>simp at member
  | cons entry rest ih=>
    rcases List.mem_cons.mp member with same | tail
    · rw [← same,WordWrites.write]
      apply writes_preserve _ rest (by intro next member;exact zero next (List.mem_cons_of_mem entry member)) query
      simp [StoreWord.put]
    · exact ih _ (by intro next member;exact zero next (List.mem_cons_of_mem entry member)) tail

theorem block_preserves (memory : WordWrites.Memory) (dst query : BitVec 64) (old : memory query=.word 0#64) :
    Copy32.memory memory dst (fun _=>0#64) query=.word 0#64 := by
  apply writes_preserve _ _ _ query old
  intro entry member
  simp only [Copy32.writes,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

theorem block_cell (memory : WordWrites.Memory) (dst : BitVec 64) (limb : Fin 4) :
    Copy32.memory memory dst (fun _=>0#64) (dst+BitVec.ofNat 64 (8*limb.val))=.word 0#64 := by
  apply writes_member _ _ _ _ (Copy32.write_member dst (fun _=>0#64) limb)
  intro entry member
  simp only [Copy32.writes,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

theorem memory32_preserves (memory : WordWrites.Memory) (dst query : BitVec 64) (index blocks : Nat)
    (old : memory query=.word 0#64) : Zero.memory32 memory dst index blocks query=.word 0#64 := by
  induction blocks generalizing memory index with
  | zero=>exact old
  | succ blocks ih=>exact ih _ _ (block_preserves memory _ query old)

theorem memoryWord_preserves (memory : WordWrites.Memory) (dst query : BitVec 64) (index blocks : Nat)
    (old : memory query=.word 0#64) : Zero.memoryWord memory dst index blocks query=.word 0#64 := by
  induction blocks generalizing memory index with
  | zero=>exact old
  | succ blocks ih=>
    apply ih
    by_cases same : query=dst+BitVec.ofNat 64 index
    · simp [StoreWord.put,same]
    · simpa only [StoreWord.put,if_neg same] using old

theorem memory32_cell (memory : WordWrites.Memory) (dst : BitVec 64) (index blocks slot : Nat)
    (inside : slot<4*blocks) :
    Zero.memory32 memory dst index blocks (dst+BitVec.ofNat 64 (index+8*slot))=.word 0#64 := by
  induction blocks generalizing memory index slot with
  | zero=>omega
  | succ blocks ih=>
    rw [Zero.memory32]
    by_cases first : slot<4
    · apply memory32_preserves
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using block_cell memory (dst+BitVec.ofNat 64 index) ⟨slot,first⟩
    · have arithmetic : index+8*slot=(index+32)+8*(slot-4):=by omega
      rw [arithmetic]
      exact ih _ (index+32) (slot-4) (by omega)

theorem memoryWord_cell (memory : WordWrites.Memory) (dst : BitVec 64) (index blocks slot : Nat)
    (inside : slot<blocks) :
    Zero.memoryWord memory dst index blocks (dst+BitVec.ofNat 64 (index+8*slot))=.word 0#64 := by
  induction blocks generalizing memory index slot with
  | zero=>omega
  | succ blocks ih=>
    rw [Zero.memoryWord]
    cases slot with
    | zero=>apply memoryWord_preserves;simp [StoreWord.put]
    | succ slot=>
      have arithmetic : index+8*(slot+1)=index+8+8*slot:=by omega
      rw [arithmetic]
      exact ih _ (index+8) slot (by omega)

/-- Every complete word of the actual aligned memzero result is zero.
No separation assumption is needed: all writes carry the same zero value. -/
theorem final_cell (memory : WordWrites.Memory) (dst : BitVec 64) (length slot : Nat)
    (inside : 8*(slot+1)≤length) :
    Zero.finalMemory memory dst length (dst+BitVec.ofNat 64 (8*slot))=.word 0#64 := by
  unfold Zero.finalMemory
  by_cases first : slot<4*(length/32)
  · apply memoryWord_preserves
    simpa only [Nat.zero_add] using memory32_cell memory dst 0 (length/32) slot first
  · have arithmetic : 8*slot=32*(length/32)+8*(slot-4*(length/32)):=by omega
    rw [arithmetic]
    apply memoryWord_cell
    omega

end InitECandidate.Solver.MutableTable.ZeroWords

#print axioms InitECandidate.Solver.MutableTable.ZeroWords.writes_member
#print axioms InitECandidate.Solver.MutableTable.ZeroWords.memory32_cell
#print axioms InitECandidate.Solver.MutableTable.ZeroWords.memoryWord_cell
#print axioms InitECandidate.Solver.MutableTable.ZeroWords.final_cell
