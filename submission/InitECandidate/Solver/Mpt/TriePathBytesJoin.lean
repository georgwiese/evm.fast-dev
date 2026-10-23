import InitECandidate.Solver.Mpt.TriePathBytes

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Adjacent full nibble spans join without imposing word alignment at
the shared boundary or truncating either borrowed path to64 bytes. -/
theorem NibbleSpan.join (memory : Memory) (domain : BitVec 64 → Prop) (be : Bool) (pointer : BitVec 64)
    (firstLength secondLength : Nat) (first : NibbleSpan memory domain be pointer firstLength)
    (second : NibbleSpan memory domain be (byteAddress pointer firstLength) secondLength)
    (fits : pointer.toNat+firstLength+secondLength<2^64) :
    NibbleSpan memory domain be pointer (firstLength+secondLength) := by
  have shifted (offset : Nat) (afterFirst : firstLength≤offset) :
      byteAddress (byteAddress pointer firstLength) (offset-firstLength)=byteAddress pointer offset:=by
    calc
      byteAddress (byteAddress pointer firstLength) (offset-firstLength)=byteAddress pointer (firstLength+(offset-firstLength)):=by
        simp only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc]
      _=byteAddress pointer offset:=by rw [Nat.add_sub_of_le afterFirst]
  refine ⟨by omega,?_,?_⟩
  · intro offset inside
    by_cases early : offset<firstLength
    · exact first.mapped offset early
    · have read:=second.mapped (offset-firstLength) (by omega)
      simpa only [shifted offset (by omega)] using read
  · intro offset inside
    by_cases early : offset<firstLength
    · exact first.nibble offset early
    · have read:=second.nibble (offset-firstLength) (by omega)
      simpa only [shifted offset (by omega)] using read

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.NibbleSpan.join
