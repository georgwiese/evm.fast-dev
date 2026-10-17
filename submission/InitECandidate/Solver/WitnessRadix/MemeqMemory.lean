import InitECandidate.Solver.WitnessRadix.WordBits
import InitECandidate.Solver.WitnessRadix.MemoryBytes
import InitECandidate.Solver.WitnessRadix.MemeqUnaligned

namespace InitECandidate.Solver.WitnessRadix.Memeq32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

noncomputable local instance : DecidableEq ByteKeys.Key := Classical.decEq _

/-- Uniform fixed-source memeq summary for 32-byte keys at every alignment.
It follows from the actual initial byte views, ABI, endian/range facts and
four available clocks; no call or comparison execution is an input premise. -/
theorem memory_execute {F : Type} (state : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64) (left right : ByteKeys.Key)
    (argA : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (argB : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (length : state.locals.lookup (ofString "n") = some (.val (.word 32#64)))
    (leftView : MemoryBytes.ByteView state a left) (rightView : MemoryBytes.ByteView state b right)
    (leftFits : a.toNat + 32 < 2 ^ 64) (rightFits : b.toNat + 32 < 2 ^ 64)
    (little : state.be = false) (enough : 4 ≤ state.clock) :
    ∃ paid, paid ≤ 4 ∧ evaluateHOLFiniteState state body =
      (some (.returned (.val (.word (if left = right then 1#64 else 0#64)))),
        restore state "i" (emptyLocalsHOLFinite { state with clock := state.clock - paid })) := by
  classical
  by_cases aligned : (a ||| b) &&& 7#64 = 0#64
  · have masks : a &&& 7#64 = 0#64 ∧ b &&& 7#64 = 0#64 := by
      rw [BitVec.and_or_distrib_right, BitVec.or_eq_zero_iff] at aligned
      exact aligned
    have aAligned : a.toNat % 8 = 0 := by
      rw [← WordBits.mask7 a, masks.1]
      rfl
    have bAligned : b.toNat % 8 = 0 := by
      rw [← WordBits.mask7 b, masks.2]
      rfl
    let leftWords := MemoryBytes.wordsOf state a
    let rightWords := MemoryBytes.wordsOf state b
    have leftCells := MemoryBytes.byteView_words state a left aAligned leftFits leftView
    have rightCells := MemoryBytes.byteView_words state b right bAligned rightFits rightView
    have leftBytes := MemoryBytes.wordView_bytes state a leftWords aAligned leftFits little leftCells
    have rightBytes := MemoryBytes.wordView_bytes state b rightWords bAligned rightFits little rightCells
    have leftEq := MemoryBytes.byteView_unique state a (WordKeys.key leftWords) left leftBytes leftView
    have rightEq := MemoryBytes.byteView_unique state b (WordKeys.key rightWords) right rightBytes rightView
    have run := aligned_memory state a b leftWords rightWords argA argB length aligned
      leftCells.mapped rightCells.mapped leftCells.stored rightCells.stored
    rw [leftEq, rightEq] at run
    refine ⟨0, Nat.zero_le _, ?_⟩
    simpa [QueryBranch.restore, QueryBranch.bind, setVarHOLFinite, emptyLocalsHOLFinite] using run
  · exact unaligned_memory state a b left right argA argB length aligned leftView rightView enough

end InitECandidate.Solver.WitnessRadix.Memeq32

#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.memory_execute
