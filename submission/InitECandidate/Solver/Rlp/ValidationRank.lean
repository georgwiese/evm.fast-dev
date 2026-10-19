import InitECandidate.Solver.Rlp.HeaderValue

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack

def rank (rootEnd position : BitVec 64) (depth : Nat) (active : Bool) : Nat :=
  2*(rootEnd.toNat-position.toNat)+depth+(if active then 1 else 0)
def nextPosition (position header payload flag : BitVec 64) : BitVec 64 :=
  if flag=0#64 then position+header+payload else position+header
def nextEnd (ending position header payload flag : BitVec 64) : BitVec 64 :=
  if flag=0#64 then ending else position+header+payload
def nextDepth (depth : Nat) (flag : BitVec 64) : Nat := if flag=0#64 then depth else depth+1

/-- The actual validated header data gives nonwrapping endpoints and strict
rank descent for either original parse branch, including a list push. This
arithmetic still needs composition with physical stores and the real loop. -/
theorem parse_progress (rootEnd position ending header payload flag : BitVec 64) (depth : Nat)
    (ordered : position.toNat≤ending.toNat) (within : ending.toNat≤rootEnd.toNat)
    (positive : 1≤header.toNat+payload.toNat)
    (extent : header.toNat+payload.toNat≤(ending-position).toNat)
    (binary : flag=0#64 ∨ flag=1#64) (listHeader : flag=1#64 → 1≤header.toNat) :
    (position+header).toNat=position.toNat+header.toNat ∧
      (position+header+payload).toNat=position.toNat+header.toNat+payload.toNat ∧
      (nextPosition position header payload flag).toNat≤(nextEnd ending position header payload flag).toNat ∧
      (nextEnd ending position header payload flag).toNat≤rootEnd.toNat ∧
      position.toNat<(nextPosition position header payload flag).toNat ∧
      rank rootEnd (nextPosition position header payload flag) (nextDepth depth flag) true<rank rootEnd position depth true := by
  have remain : (ending-position).toNat=ending.toNat-position.toNat := BitVec.toNat_sub_of_le ordered
  rw [remain] at extent
  have rootBound := rootEnd.isLt
  have headerNumber : (position+header).toNat=position.toNat+header.toNat := BitVec.toNat_add_of_lt (by omega)
  have afterNumber : (position+header+payload).toNat=position.toNat+header.toNat+payload.toNat := by
    rw [BitVec.toNat_add_of_lt (by rw [headerNumber]; omega),headerNumber]
  refine ⟨headerNumber,afterNumber,?_⟩
  by_cases zero : flag=0#64
  · simp only [nextPosition,nextEnd,nextDepth,if_pos zero,rank,afterNumber,Bool.true_eq,↓reduceIte]
    omega
  · have one : flag=1#64 := binary.resolve_left zero
    have positiveHeader := listHeader one
    simp only [nextPosition,nextEnd,nextDepth,if_neg zero,rank,headerNumber,afterNumber,Bool.true_eq,↓reduceIte]
    omega

theorem pop_progress (rootEnd position : BitVec 64) (depth : Nat) :
    rank rootEnd position depth true<rank rootEnd position (depth+1) true := by unfold rank; omega
theorem stop_progress (rootEnd position : BitVec 64) : rank rootEnd position 0 false<rank rootEnd position 0 true := by
  unfold rank
  simp

theorem initial (pointer length : BitVec 64) (fits : pointer.toNat+length.toNat<2^64) :
    rank (pointer+length) pointer 0 true=2*length.toNat+1 := by
  have number := BitVec.toNat_add_of_lt fits
  unfold rank
  rw [number]
  simp

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.parse_progress
#print axioms InitECandidate.Solver.Rlp.Validation.pop_progress
#print axioms InitECandidate.Solver.Rlp.Validation.stop_progress
#print axioms InitECandidate.Solver.Rlp.Validation.initial
