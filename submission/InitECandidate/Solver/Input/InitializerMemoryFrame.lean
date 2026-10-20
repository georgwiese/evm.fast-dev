import InitECandidate.Solver.Input.InitializerQuads
import InitECandidate.Solver.Input.InitializerAliases

namespace InitECandidate.Solver.Input.InitializerAllocations
open Flapjack PanSemStateFiniteExact

theorem template_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (actions : List Action) :
    (template source cursor actions).memory = source.memory := by
  induction actions generalizing source cursor with
  | nil => rfl
  | cons action rest ih => exact ih (reserve source action cursor) (cursor + action.bytes)

end InitECandidate.Solver.Input.InitializerAllocations

namespace InitECandidate.Solver.Input.InitializerQuads
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Every destination is a physical limb of one of the actual stored tuples. -/
theorem writes_member (pointer : BitVec 64) (offset : Nat) (words : List Words) (entry : BitVec 64 × BitVec 64)
    (member : entry ∈ writes pointer offset words) :
    ∃ tupleIndex < words.length,∃ limb < 4,entry.1 = byteAddress pointer (offset + 32 * tupleIndex + 8 * limb) := by
  induction words generalizing offset with
  | nil => simp [writes] at member
  | cons word rest ih =>
    rw [writes,List.mem_append] at member
    rcases member with first | later
    · have choices : entry = (pointer + BitVec.ofNat 64 offset,word 0) ∨ entry = (pointer + BitVec.ofNat 64 offset + 8#64,word 1) ∨
          entry = (pointer + BitVec.ofNat 64 offset + 16#64,word 2) ∨ entry = (pointer + BitVec.ofNat 64 offset + 24#64,word 3) := by
        simpa [RlpWrite.U256Value.wordWrites] using first
      rcases choices with rfl | rfl | rfl | rfl
      · exact ⟨0,by simp,0,by decide,by simp [byteAddress]⟩
      · exact ⟨0,by simp,1,by decide,by simp [byteAddress,BitVec.ofNat_add,BitVec.add_assoc]⟩
      · exact ⟨0,by simp,2,by decide,by simp [byteAddress,BitVec.ofNat_add,BitVec.add_assoc]⟩
      · exact ⟨0,by simp,3,by decide,by simp [byteAddress,BitVec.ofNat_add,BitVec.add_assoc]⟩
    · obtain ⟨tupleIndex,inside,limb,small,address⟩ := ih (offset + 32) later
      refine ⟨tupleIndex + 1,by simp only [List.length_cons]; omega,limb,small,?_⟩
      convert address using 2 <;> omega

/-- Fresh table stores leave every earlier physical word intact. -/
theorem written_before (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64) (offset : Nat) (words : List Words)
    (fits : pointer.toNat + offset + 32 * words.length < 2 ^ 64) (before : query.toNat < pointer.toNat) :
    (written source pointer offset words).memory query = source.memory query := by
  apply WordWrites.write_away
  intro member
  obtain ⟨entry,entryMember,equal⟩ := List.mem_map.mp member
  obtain ⟨tupleIndex,inside,limb,small,address⟩ := writes_member pointer offset words entry entryMember
  have number := byteAddress_toNat pointer (offset + 32 * tupleIndex + 8 * limb) (by omega)
  rw [equal] at address
  have same := congrArg BitVec.toNat address
  rw [number] at same
  omega

end InitECandidate.Solver.Input.InitializerQuads

#print axioms InitECandidate.Solver.Input.InitializerAllocations.template_memory
#print axioms InitECandidate.Solver.Input.InitializerQuads.writes_member
#print axioms InitECandidate.Solver.Input.InitializerQuads.written_before
