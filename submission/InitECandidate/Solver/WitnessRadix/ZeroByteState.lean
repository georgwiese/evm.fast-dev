import InitECandidate.Solver.WitnessRadix.ZeroLoopTail

namespace InitECandidate.Solver.WitnessRadix.Zero
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def memoryByte (memory : WordWrites.Memory) (be : Bool) (dst : BitVec 64) (index : Nat) : Nat → WordWrites.Memory
  | 0 => memory
  | blocks + 1 => memoryByte (byteMemory memory be (dst + BitVec.ofNat 64 index)) be dst (index + 1) blocks

theorem stateByte_frame {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (index blocks : Nat) :
    emptyLocalsHOLFinite (stateByte source dst index blocks) = emptyLocalsHOLFinite { source with
      memory := memoryByte source.memory source.be dst index blocks
      clock := source.clock - blocks } := by
  induction blocks generalizing source index with
  | zero => simp [stateByte, memoryByte]
  | succ blocks ih =>
    rw [stateByte, ih]
    have clock : source.clock - 1 - blocks = source.clock - (blocks + 1) := by omega
    simp only [bytePost, QueryBranch.bind, setVarHOLFinite, decClockHOLFinite, emptyLocalsHOLFinite, memoryByte, clock]

theorem stateByte_other {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (index blocks : Nat)
    (name : MlS) (different : ofString "i" ≠ name) :
    (stateByte source dst index blocks).locals.lookup name = source.locals.lookup name := by
  induction blocks generalizing source index with
  | zero => rfl
  | succ blocks ih =>
    rw [stateByte, ih]
    simp [bytePost, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, different, decClockHOLFinite]

theorem stateByte_index {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (index blocks : Nat)
    (initial : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index)))) :
    (stateByte source dst index blocks).locals.lookup (ofString "i") =
      some (.val (.word (BitVec.ofNat 64 (index + 1 * blocks)))) := by
  induction blocks generalizing source index with
  | zero => simpa only [stateByte, Nat.mul_zero, Nat.add_zero] using initial
  | succ blocks ih =>
    rw [stateByte]
    have initial' : (bytePost (decClockHOLFinite source) dst (BitVec.ofNat 64 index)).locals.lookup (ofString "i") =
        some (.val (.word (BitVec.ofNat 64 (index + 1)))) := by
      change (bind _ "i" _).locals.lookup (ofString "i") = _
      rw [bind_lookup_same, BitVec.ofNat_add_ofNat index 1]
    have next := ih _ (index + 1) initial'
    have total : index + 1 + 1 * blocks = index + 1 * (blocks + 1) := by omega
    simpa only [total] using next

end InitECandidate.Solver.WitnessRadix.Zero

#print axioms InitECandidate.Solver.WitnessRadix.Zero.stateByte_frame
#print axioms InitECandidate.Solver.WitnessRadix.Zero.stateByte_other
#print axioms InitECandidate.Solver.WitnessRadix.Zero.stateByte_index
