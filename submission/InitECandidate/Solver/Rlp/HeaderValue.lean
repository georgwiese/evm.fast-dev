import InitECandidate.Solver.Rlp.HeaderProgram

namespace InitECandidate.Solver.Rlp.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def result (header payload flag : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word header),.val (.word payload),.val (.word flag)]

/-- A current decoded header advances by a positive item size inside its
actual input extent. Its header occupies at most nine bytes. -/
def Valid (length : Nat) (value : ValueHOL 64) : Prop :=
  ∃ header payload flag,value=result header payload flag ∧ header.toNat≤9 ∧
    1≤header.toNat+payload.toNat ∧ header.toNat+payload.toNat≤length ∧ (flag=0#64 ∨ flag=1#64) ∧
      (flag=1#64 → 1≤header.toNat)

theorem Valid.total_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (length : Nat) (value : ValueHOL 64)
    (small : length<2^64) (cell : source.locals.lookup (ofString name)=some value) (valid : Valid length value) :
    ∃ total : BitVec 64,eval source (.op .add [.rfield 0 (localVar name),.rfield 1 (localVar name)])=some (.val (.word total)) ∧
      1≤total.toNat ∧ total.toNat≤length := by
  obtain ⟨header,payload,flag,valueEq,headerBound,positive,bounded,binary⟩ := valid
  rw [valueEq] at cell
  have number : (header+payload).toNat=header.toNat+payload.toNat := BitVec.toNat_add_of_lt (by omega)
  refine ⟨header+payload,?_,by rw [number]; exact positive,by rw [number]; exact bounded⟩
  simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,cell,result,valueIsWord,valueWord,wordOpHOL,wordOp]

theorem payload_span (domain : BitVec 64 → Prop) (pointer header payload : BitVec 64) (length : Nat)
    (fits : pointer.toNat+length<2^64)
    (mapped : ∀ offset<length,domain (panByteAlignHOL (width := 64) (byteAddress pointer offset)))
    (inside : header.toNat+payload.toNat≤length) :
    (pointer+header).toNat+payload.toNat<2^64 ∧
      ∀ offset<payload.toNat,domain (panByteAlignHOL (width := 64) (byteAddress (pointer+header) offset)) := by
  have number : (pointer+header).toNat=pointer.toNat+header.toNat := BitVec.toNat_add_of_lt (by omega)
  refine ⟨by rw [number]; omega,?_⟩
  intro offset bounded
  have available := mapped (header.toNat+offset) (by omega)
  simpa only [byteAddress,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc] using available

end InitECandidate.Solver.Rlp.Header

#print axioms InitECandidate.Solver.Rlp.Header.Valid.total_read
#print axioms InitECandidate.Solver.Rlp.Header.payload_span
