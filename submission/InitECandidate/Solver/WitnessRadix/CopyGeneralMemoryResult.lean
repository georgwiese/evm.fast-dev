import InitECandidate.Solver.WitnessRadix.CopyGeneralMemory

namespace InitECandidate.Solver.WitnessRadix.CopyGeneral
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open CopyContext

def prefixMemory (memory : WordWrites.Memory) (src dst : BitVec 64) (length : Nat) : WordWrites.Memory :=
  CopyWords.memoryWalk (CopyWords.memoryWalk memory src dst 0 32 CopyWords.wordOffsets (length/32)) src dst
    (32*(length/32)) 8 [0] ((length%32)/8)
def suffixMemory (memory : WordWrites.Memory) (be : Bool) (src dst : BitVec 64) (index length : Nat) : WordWrites.Memory :=
  CopyBytes.memoryWalk (CopyBytes.memoryWalk memory be src dst index 8 CopyBytes.byteOffsets ((length-index)/8)) be src dst
    (index + 8*((length-index)/8)) 1 [0] ((length-index)%8)
def resultMemory (memory : WordWrites.Memory) (be : Bool) (src dst : BitVec 64) (length : Nat) : WordWrites.Memory :=
  if aligned src dst then suffixMemory (prefixMemory memory src dst length) be src dst (CopyWords.prefixIndex length) length
  else suffixMemory memory be src dst 0 length

theorem byte_walk_be {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (index step rounds : Nat) (offsets : List Nat) :
    (CopyBytes.walk source src dst index step offsets rounds).be = source.be := by
  have h := congrArg (fun state : PanSemStateFiniteExact 64 F => state.be) (byte_walk_control source src dst index step rounds offsets)
  exact h

theorem word_walk_be {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (index step rounds : Nat) (offsets : List Nat) :
    (CopyWords.walk source src dst index step offsets rounds).be = source.be := by
  have h := congrArg (fun state : PanSemStateFiniteExact 64 F => state.be) (word_walk_control source src dst index step rounds offsets)
  exact h

theorem core_memory {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length : Nat) :
    (coreState source src dst length).memory = resultMemory source.memory source.be src dst length := by
  unfold coreState resultMemory
  split <;> simp only [CopyBytes.suffixState, CopyWords.prefixState, byte_walk_memory, word_walk_memory,
    byte_walk_be, word_walk_be, prefixMemory, suffixMemory]

theorem resultMemory_away (memory : WordWrites.Memory) (be : Bool) (src dst query : BitVec 64) (length : Nat)
    (away : Away dst query length) : resultMemory memory be src dst length query = memory query := by
  let source : PanSemStateFiniteExact 64 Unit := {
    locals := HolFiniteMapExact.empty
    globals := HolFiniteMapExact.empty
    structs := []
    code := HolFiniteMapExact.empty
    eshapes := HolFiniteMapExact.empty
    memory := memory
    memaddrs := fun _ => True
    shMemaddrs := fun _ => False
    clock := 0
    be := be
    ffi := { oracle := fun _ state _ _ => .ret state [], ffiState := (), ioEvents := [] }
    baseAddr := 0#64
    topAddr := 0#64 }
  have h := core_memory_away source src dst query length away
  rw [core_memory] at h
  exact h

end InitECandidate.Solver.WitnessRadix.CopyGeneral

#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.byte_walk_be
#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.word_walk_be
#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.core_memory
#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.resultMemory_away
