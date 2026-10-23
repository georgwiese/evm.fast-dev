import InitECandidate.Solver.Mpt.NibblesConcatProgram
import InitECandidate.Solver.Mpt.TriePathBytesCopy
import InitECandidate.Solver.Mpt.TriePathBytesJoin
import InitECandidate.Solver.WitnessRadix.CopyFreshFrame

namespace InitECandidate.Solver.Mpt.NibblesConcat
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

def copyMemory (memory : WordWrites.Memory) (out a al b bl : BitVec 64) : WordWrites.Memory:=
  CopyGeneral.resultMemory (CopyGeneral.resultMemory memory false a out al.toNat) false b (out+al) bl.toNat

/-- Both original copies yield the full joined nibble path. The second
copy may share a backing word with the first path's final bytes; byte
projection preserves those bytes. Every older persistent word survives. -/
theorem memory_path (memory : WordWrites.Memory) (domain : BitVec 64 → Prop) (out a al b bl : BitVec 64)
    (left : TrieWalk.NibbleSpan memory domain false a al.toNat) (right : TrieWalk.NibbleSpan memory domain false b bl.toNat)
    (sourceA : AllocatedBytes.Arena a al.toNat) (sourceB : AllocatedBytes.Arena b bl.toNat)
    (destination : AllocatedBytes.Arena out (al.toNat+bl.toNat)) (aligned : out.toNat%8=0)
    (leftBefore : a.toNat+al.toNat≤out.toNat) (rightBefore : b.toNat+bl.toNat≤out.toNat)
    (mapped : ∀ offset<al.toNat+bl.toNat,domain (panByteAlignHOL (width:=64) (byteAddress out offset))) :
    TrieWalk.NibbleSpan (copyMemory memory out a al b bl) domain false out (al.toNat+bl.toNat) ∧
      ∀ query : BitVec 64,query.toNat<out.toNat → copyMemory memory out a al b bl query=memory query := by
  let first:=CopyGeneral.resultMemory memory false a out al.toNat
  have fits : out.toNat+al.toNat+bl.toNat<2^64:=by have upper:=destination.upper; omega
  have addition : (out+al).toNat=out.toNat+al.toNat:=BitVec.toNat_add_of_lt (by omega)
  have word : BitVec.ofNat 64 al.toNat=al:=by simp
  have shifted (offset : Nat) : byteAddress (out+al) offset=byteAddress out (al.toNat+offset):=by
    simp only [byteAddress,BitVec.ofNat_add,word,BitVec.add_assoc]
  have firstArena : AllocatedBytes.Arena out al.toNat:=destination.weaken out (al.toNat+bl.toNat) al.toNat (by omega)
  have secondArena : AllocatedBytes.Arena (out+al) bl.toNat:=⟨by rw [addition]; have lower:=destination.lower; omega,
    by rw [addition]; have upper:=destination.upper; omega⟩
  have firstFrame (query : BitVec 64) (before : query.toNat<out.toNat) : first query=memory query:=
    CopyGeneral.result_before_floor memory false a out query al.toNat out.toNat aligned (Nat.le_refl _) (by omega) before
  have currentRight:=right.of_agreement memory first domain domain false false b bl.toNat rfl rfl (by
    intro offset inside
    have number:=byteAddress_toNat b offset (by have upper:=right.fits; omega)
    have backing:=AllocatedBytes.aligned_number (byteAddress b offset)
    exact firstFrame _ (by rw [backing,number]; omega))
  have firstSpan:=left.copy_little memory domain a out al.toNat sourceA firstArena leftBefore (by intro offset inside; exact mapped offset (by omega))
  have secondSpan:=currentRight.copy_little first domain b (out+al) bl.toNat sourceB secondArena (by rw [addition]; omega) (by
    intro offset inside
    rw [shifted]
    exact mapped _ (by omega))
  have retained:=firstSpan.of_little_byte_agreement first (copyMemory memory out a al b bl) domain out al.toNat (by
    intro offset inside
    exact CopyByteContent.result_byte_away first b (out+al) (byteAddress out offset) bl.toNat
      (by rw [addition]; omega) (by
        intro index inSecond equal
        have number:=congrArg BitVec.toNat equal
        rw [byteAddress_toNat out offset (by omega),byteAddress_toNat (out+al) index (by rw [addition]; omega),addition] at number
        omega))
  refine ⟨retained.join (copyMemory memory out a al b bl) domain false out al.toNat bl.toNat
    (by simpa only [byteAddress,word,copyMemory,first] using secondSpan) fits,?_⟩
  intro query before
  exact (CopyGeneral.result_before_floor first false b (out+al) query bl.toNat out.toNat aligned (by rw [addition]; omega) (by rw [addition]; omega) before).trans (firstFrame query before)

end InitECandidate.Solver.Mpt.NibblesConcat

#print axioms InitECandidate.Solver.Mpt.NibblesConcat.memory_path
