import InitECandidate.Solver.WitnessRadix.ZeroLoop32
import InitECandidate.Solver.WitnessRadix.ZeroLoopWord

namespace InitECandidate.Solver.WitnessRadix.Zero
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def memory32 (memory : WordWrites.Memory) (dst : BitVec 64) (index : Nat) : Nat → WordWrites.Memory
  | 0 => memory
  | blocks + 1 => memory32 (Copy32.memory memory (dst + BitVec.ofNat 64 index) (fun _ => 0#64)) dst (index + 32) blocks

theorem state32_frame {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (index blocks : Nat) :
    emptyLocalsHOLFinite (state32 source dst index blocks) = emptyLocalsHOLFinite { source with
      memory := memory32 source.memory dst index blocks
      clock := source.clock - blocks } := by
  induction blocks generalizing source index with
  | zero => simp [state32, memory32]
  | succ blocks ih =>
    rw [state32, ih]
    have clock : source.clock - 1 - blocks = source.clock - (blocks + 1) := by omega
    simp only [blockPost, QueryBranch.bind, setVarHOLFinite, decClockHOLFinite, emptyLocalsHOLFinite, memory32, clock]

theorem state32_other {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (index blocks : Nat)
    (name : MlS) (different : ofString "i" ≠ name) :
    (state32 source dst index blocks).locals.lookup name = source.locals.lookup name := by
  induction blocks generalizing source index with
  | zero => rfl
  | succ blocks ih =>
    rw [state32, ih]
    simp [blockPost, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, different, decClockHOLFinite]

theorem state32_index {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (index blocks : Nat)
    (initial : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index)))) :
    (state32 source dst index blocks).locals.lookup (ofString "i") =
      some (.val (.word (BitVec.ofNat 64 (index + 32 * blocks)))) := by
  induction blocks generalizing source index with
  | zero => simpa only [state32, Nat.mul_zero, Nat.add_zero] using initial
  | succ blocks ih =>
    rw [state32]
    have initial' : (blockPost (decClockHOLFinite source) dst (BitVec.ofNat 64 index)).locals.lookup (ofString "i") =
        some (.val (.word (BitVec.ofNat 64 (index + 32)))) := by
      change (bind _ "i" _).locals.lookup (ofString "i") = _
      rw [bind_lookup_same, BitVec.ofNat_add_ofNat index 32]
    have next := ih _ (index + 32) initial'
    have total : index + 32 + 32 * blocks = index + 32 * (blocks + 1) := by omega
    simpa only [total] using next

def memoryWord (memory : WordWrites.Memory) (dst : BitVec 64) (index : Nat) : Nat → WordWrites.Memory
  | 0 => memory
  | blocks + 1 => memoryWord (StoreWord.put memory (dst + BitVec.ofNat 64 index) 0#64) dst (index + 8) blocks

theorem stateWord_frame {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (index blocks : Nat) :
    emptyLocalsHOLFinite (stateWord source dst index blocks) = emptyLocalsHOLFinite { source with
      memory := memoryWord source.memory dst index blocks
      clock := source.clock - blocks } := by
  induction blocks generalizing source index with
  | zero => simp [stateWord, memoryWord]
  | succ blocks ih =>
    rw [stateWord, ih]
    have clock : source.clock - 1 - blocks = source.clock - (blocks + 1) := by omega
    simp only [wordPost, QueryBranch.bind, setVarHOLFinite, decClockHOLFinite, emptyLocalsHOLFinite, memoryWord, clock]

theorem stateWord_other {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (index blocks : Nat)
    (name : MlS) (different : ofString "i" ≠ name) :
    (stateWord source dst index blocks).locals.lookup name = source.locals.lookup name := by
  induction blocks generalizing source index with
  | zero => rfl
  | succ blocks ih =>
    rw [stateWord, ih]
    simp [wordPost, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, different, decClockHOLFinite]

theorem stateWord_index {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (index blocks : Nat)
    (initial : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index)))) :
    (stateWord source dst index blocks).locals.lookup (ofString "i") =
      some (.val (.word (BitVec.ofNat 64 (index + 8 * blocks)))) := by
  induction blocks generalizing source index with
  | zero => simpa only [stateWord, Nat.mul_zero, Nat.add_zero] using initial
  | succ blocks ih =>
    rw [stateWord]
    have initial' : (wordPost (decClockHOLFinite source) dst (BitVec.ofNat 64 index)).locals.lookup (ofString "i") =
        some (.val (.word (BitVec.ofNat 64 (index + 8)))) := by
      change (bind _ "i" _).locals.lookup (ofString "i") = _
      rw [bind_lookup_same, BitVec.ofNat_add_ofNat index 8]
    have next := ih _ (index + 8) initial'
    have total : index + 8 + 8 * blocks = index + 8 * (blocks + 1) := by omega
    simpa only [total] using next

end InitECandidate.Solver.WitnessRadix.Zero

#print axioms InitECandidate.Solver.WitnessRadix.Zero.state32_frame
#print axioms InitECandidate.Solver.WitnessRadix.Zero.state32_other
#print axioms InitECandidate.Solver.WitnessRadix.Zero.state32_index
#print axioms InitECandidate.Solver.WitnessRadix.Zero.stateWord_frame
#print axioms InitECandidate.Solver.WitnessRadix.Zero.stateWord_other
#print axioms InitECandidate.Solver.WitnessRadix.Zero.stateWord_index
