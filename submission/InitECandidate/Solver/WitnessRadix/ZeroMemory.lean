import InitECandidate.Solver.WitnessRadix.ZeroExecution

namespace InitECandidate.Solver.WitnessRadix.Zero
open Flapjack PanSemStateFiniteExact

theorem block_memory_away (memory : WordWrites.Memory) (dst index query : BitVec 64)
    (away : ∀ limb : Fin 4, query ≠ dst + index + BitVec.ofNat 64 (8 * limb.val)) :
    Copy32.memory memory (dst + index) (fun _ => 0#64) query = memory query := by
  apply WordWrites.write_away
  have a0 := away 0
  have a1 := away 1
  have a2 := away 2
  have a3 := away (⟨3, by decide⟩ : Fin 4)
  simp at a0 a1 a2 a3
  simp [Copy32.writes, a0, a1, a2, a3]

theorem memory32_away (memory : WordWrites.Memory) (dst query : BitVec 64) (index blocks : Nat)
    (away : ∀ offset < 32 * blocks, query ≠ byteAddress dst (index + offset)) :
    memory32 memory dst index blocks query = memory query := by
  induction blocks generalizing memory index with
  | zero => rfl
  | succ blocks ih =>
    rw [memory32, ih]
    · apply block_memory_away
      intro limb
      have distinct := away (8 * limb.val) (by have := limb.isLt; omega)
      simpa only [byteAddress, BitVec.ofNat_add, BitVec.add_assoc] using distinct
    · intro offset inside
      have distinct := away (32 + offset) (by omega)
      simpa only [Nat.add_assoc] using distinct

theorem memoryWord_away (memory : WordWrites.Memory) (dst query : BitVec 64) (index blocks : Nat)
    (away : ∀ offset < 8 * blocks, query ≠ byteAddress dst (index + offset)) :
    memoryWord memory dst index blocks query = memory query := by
  induction blocks generalizing memory index with
  | zero => rfl
  | succ blocks ih =>
    rw [memoryWord, ih]
    · have distinct := away 0 (by omega)
      have distinct' : query ≠ dst + BitVec.ofNat 64 index := by
        simpa only [Nat.add_zero, byteAddress] using distinct
      exact if_neg distinct'
    · intro offset inside
      have distinct := away (8 + offset) (by omega)
      simpa only [Nat.add_assoc] using distinct

def finalMemory (memory : WordWrites.Memory) (dst : BitVec 64) (length : Nat) : WordWrites.Memory :=
  memoryWord (memory32 memory dst 0 (length / 32)) dst (32 * (length / 32)) ((length % 32) / 8)

theorem final_frame {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (length : Nat) :
    emptyLocalsHOLFinite (finalState source dst length) = emptyLocalsHOLFinite { source with
      memory := finalMemory source.memory dst length
      clock := source.clock - price length } := by
  let initial := QueryBranch.bind source "i" 0#64
  let first := state32 initial dst 0 (length / 32)
  have firstFrame := state32_frame initial dst 0 (length / 32)
  have memory : first.memory = memory32 source.memory dst 0 (length / 32) := congrArg (fun state => state.memory) firstFrame
  have clock : first.clock = source.clock - length / 32 := congrArg (fun state => state.clock) firstFrame
  change emptyLocalsHOLFinite (stateWord first dst (32 * (length / 32)) ((length % 32) / 8)) = _
  rw [stateWord_frame, memory, clock]
  have updated := congrArg (fun state : PanSemStateFiniteExact 64 F => { state with
    memory := finalMemory source.memory dst length
    clock := source.clock - price length }) firstFrame
  have clockSub : source.clock - length / 32 - (length % 32) / 8 = source.clock - price length := by
    unfold price; omega
  simpa only [clockSub, emptyLocalsHOLFinite, finalMemory, initial, first, QueryBranch.bind, setVarHOLFinite] using updated

theorem final_memory_away (memory : WordWrites.Memory) (dst query : BitVec 64) (length : Nat)
    (away : ∀ offset < length, query ≠ byteAddress dst offset) :
    finalMemory memory dst length query = memory query := by
  rw [finalMemory, memoryWord_away]
  · apply memory32_away
    intro offset inside
    simpa only [Nat.zero_add] using away offset (by omega)
  · intro offset inside
    exact away (32 * (length / 32) + offset) (by omega)

end InitECandidate.Solver.WitnessRadix.Zero

#print axioms InitECandidate.Solver.WitnessRadix.Zero.final_frame
#print axioms InitECandidate.Solver.WitnessRadix.Zero.final_memory_away
