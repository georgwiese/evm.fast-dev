import InitECandidate.Solver.Rlp.ReadLengthObservation
import InitECandidate.Solver.Rlp.HeaderValue

namespace InitECandidate.Solver.Rlp.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual first byte and, in a long case, the observed original
length-reader result. This records input provenance in addition to Valid. -/
def Encoded (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload flag : BitVec 64) : Prop :=
  ∃ loaded : UInt8, ReadLength.byte source pointer=some loaded ∧
    let b := BitVec.ofNat 64 loaded.toNat
    if b.toNat<128 then header=0#64 ∧ payload=1#64 ∧ flag=0#64
    else if b.toNat≤183 then header=1#64 ∧ payload=b-128#64 ∧ flag=0#64
    else if b.toNat≤191 then header=1#64+(b-183#64) ∧ flag=0#64 ∧
      ReadLength.Observed source (pointer+1#64) (b-183#64) payload
    else if b.toNat≤247 then header=1#64 ∧ payload=b-192#64 ∧ flag=1#64
    else header=1#64+(b-247#64) ∧ flag=1#64 ∧
      ReadLength.Observed source (pointer+1#64) (b-247#64) payload

theorem Encoded.unique (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer leftHeader leftPayload leftFlag rightHeader rightPayload rightFlag : BitVec 64)
    (left : Encoded source pointer leftHeader leftPayload leftFlag)
    (right : Encoded source pointer rightHeader rightPayload rightFlag) :
    leftHeader=rightHeader ∧ leftPayload=rightPayload ∧ leftFlag=rightFlag := by
  obtain ⟨leftByte,leftRead,left⟩ := left
  obtain ⟨rightByte,rightRead,right⟩ := right
  have same : leftByte=rightByte := Option.some.inj (leftRead.symm.trans rightRead)
  subst rightByte
  dsimp only at left right
  split_ifs at left right with singleCase shortStringCase longStringCase shortListCase
  · exact ⟨left.1.trans right.1.symm,left.2.1.trans right.2.1.symm,left.2.2.trans right.2.2.symm⟩
  · exact ⟨left.1.trans right.1.symm,left.2.1.trans right.2.1.symm,left.2.2.trans right.2.2.symm⟩
  · exact ⟨left.1.trans right.1.symm,ReadLength.Observed.unique source _ _ _ _ left.2.2 right.2.2,left.2.1.trans right.2.1.symm⟩
  · exact ⟨left.1.trans right.1.symm,left.2.1.trans right.2.1.symm,left.2.2.trans right.2.2.symm⟩
  · exact ⟨left.1.trans right.1.symm,ReadLength.Observed.unique source _ _ _ _ left.2.2 right.2.2,left.2.1.trans right.2.1.symm⟩

end InitECandidate.Solver.Rlp.Header

#print axioms InitECandidate.Solver.Rlp.Header.Encoded.unique
