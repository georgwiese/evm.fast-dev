import InitECandidate.Solver.Input.HeaderPair

namespace InitECandidate.Solver.Input.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def prefixCode : ProgHOL 64 := .seq storeFirst (.seq storeSecond guardCall)
def offsetWords (input : Guest.InputBlob) (position : Nat) : BitVec 64 :=
  if position=0 then firstWord input else secondWord input

/-- Normal execution of the actual two stores and first container guard proves
le32(input,2)=16. It preserves input bytes and pays at most four source clocks. -/
theorem guard_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array total : BitVec 64) (heap : Blob.HeapInput source input pointer) (inside : 10≤input.length%2^64)
    (pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word (pointer+2#64))))
    (arrayGlobal : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (totalLocal : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (upper : pointer.toNat+input.length%2^64+8≤33806089496)
    (arrayLower : 2701131776≤array.toNat) (arrayBefore : array.toNat+16≤pointer.toNat)
    (code : source.code.lookup (ofString "ssz_check_offsets")=some (Offsets.formals,Offsets.body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 4≤source.clock)
    (run : evaluateHOLFiniteState source prefixCode=(none,post)) :
    Guest.GasLimit.le32 input 2=16 ∧ 16≤Guest.GasLimit.le32 input 6 ∧
      Guest.GasLimit.le32 input 6≤total.toNat ∧ Blob.HeapInput post input pointer ∧
      ∃ paid,paid≤4 ∧ post={pairState source input array with clock:=source.clock-paid} := by
  classical
  obtain ⟨pairRun,pairHeap,firstCell,secondCell,firstRun,secondRun,firstMapped,secondMapped⟩:=
    pair_execute source input pointer array heap inside pointerLocal arrayGlobal domain pointerAligned arrayAligned upper arrayLower arrayBefore
  have prefixRun : evaluateHOLFiniteState source prefixCode=evaluateHOLFiniteState (pairState source input array) guardCall := by
    rw [prefixCode,WitnessRadix.StateSteps.next_sequence source (firstState source input array) _ _ firstRun (Nat.le_refl _),
      WitnessRadix.StateSteps.next_sequence (firstState source input array) (pairState source input array) _ _ secondRun (Nat.le_refl _)]
  have guardRun : evaluateHOLFiniteState (pairState source input array) guardCall=(none,post) := prefixRun.symm.trans run
  have args : evalListHOLFinite (pairState source input array)
      (h:=fun address=>Classical.propDecidable ((pairState source input array).memaddrs address)) guardArguments=
      some (Offsets.arguments array 16#64 total 2) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,guardArguments,Offsets.arguments,
      offsets,localVar,pairState,firstState,arrayGlobal,totalLocal]
  have mapped : ∀ position<2,(pairState source input array).memaddrs (array+BitVec.ofNat 64 (8*position)) := by
    intro position small
    have alternatives : position=0 ∨ position=1 := by omega
    rcases alternatives with rfl|rfl
    · simpa [pairState,firstState] using firstMapped
    · simpa [pairState,firstState] using secondMapped
  have cells : ∀ position<2,(pairState source input array).memory (array+BitVec.ofNat 64 (8*position))=.word (offsetWords input position) := by
    intro position small
    have alternatives : position=0 ∨ position=1 := by omega
    rcases alternatives with rfl|rfl
    · simpa [offsetWords] using firstCell
    · simpa [offsetWords] using secondCell
  obtain ⟨first,valid,paid,bound,postEq⟩:=Offsets.call_normal_first (pairState source input array) post guardArguments array 16#64 total
    (offsetWords input) 2 (by decide) (by decide) args code failCode exceptionShape mapped cells enough guardRun
  have rawSmall : Guest.GasLimit.le32 input 2<2^64 := by
    have bound:=HostGas.le32_lt input 2
    rw [HostGas.le32_eq input 2 (by decide)] at bound
    omega
  have number:=congrArg BitVec.toNat first
  change (BitVec.ofNat 64 (Guest.GasLimit.le32 input 2)).toNat=16 at number
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt rawSmall] at number
  have secondSmall : Guest.GasLimit.le32 input 6<2^64 := by
    have bound:=HostGas.le32_lt input 6
    rw [HostGas.le32_eq input 6 (by decide)] at bound
    omega
  have secondEncoded : (secondWord input).toNat=Guest.GasLimit.le32 input 6 := by
    rw [secondWord,BitVec.toNat_ofNat,Nat.mod_eq_of_lt secondSmall]
  have secondValid:=valid 1 (by decide)
  change 16≤(secondWord input).toNat ∧ (secondWord input).toNat≤total.toNat ∧ _ at secondValid
  rw [secondEncoded] at secondValid
  refine ⟨number,secondValid.1,secondValid.2.1,?_,paid,bound,postEq⟩
  rw [postEq]
  exact pairHeap

end InitECandidate.Solver.Input.Header

#print axioms InitECandidate.Solver.Input.Header.guard_normal
