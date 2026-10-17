import InitECandidate.Solver.Input.HeaderEntryNormal
import InitECandidate.Solver.Input.HeaderAfterNormal

namespace InitECandidate.Solver.Input.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- From an actual normal return of the fixed decoder: derive its schema,
encoded minimum length, first container offsets, and the exact next continuation.
The mathematical list length remains unrestricted. -/
theorem first_container (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer array : BitVec 64)
    (heap : Blob.HeapInput source input pointer)
    (pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthLocal : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 (input.length%2^64)))))
    (arrayGlobal : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (upper : pointer.toNat+input.length%2^64+8≤33806089496)
    (arrayLower : 2701131776≤array.toNat) (arrayBefore : array.toNat+16≤pointer.toNat)
    (code : source.code.lookup (ofString "ssz_check_offsets")=some (Offsets.formals,Offsets.body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 4≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    18≤input.length%2^64 ∧ Guest.GasLimit.byte input 0=21 ∧ Guest.GasLimit.byte input 1=1 ∧
    Guest.GasLimit.le32 input 2=16 ∧ 16≤Guest.GasLimit.le32 input 6 ∧
    Guest.GasLimit.le32 input 6≤input.length%2^64-2 ∧
      ∃ next paid,paid≤4 ∧
        next={pairState (shifted source pointer (input.length%2^64)) input array with clock:=source.clock-paid} ∧
        Blob.HeapInput next input pointer ∧ evaluateHOLFiniteState next continuation=(some (.returned value),post) := by
  obtain ⟨extent,schema0,schema1,tailRun⟩:=normal_entry source post input pointer heap pointerLocal lengthLocal failCode exceptionShape (by omega) value run
  let entered:=shifted source pointer (input.length%2^64)
  have enteredHeap : Blob.HeapInput entered input pointer := Blob.HeapInput.of_fields source entered input pointer rfl rfl rfl heap
  have p : entered.locals.lookup (ofString "p")=some (.val (.word (pointer+2#64))) := by
    exact (bind_lookup_other (WitnessRadix.QueryBranch.bind source "p" (pointer+2#64)) "len" "p" _ (by decide)).trans (bind_lookup_same _ _ _)
  have n : entered.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 (input.length%2^64-2)))) := bind_lookup_same _ _ _
  obtain ⟨first,low,high,next,paid,bound,nextEq,nextHeap,nextRun⟩:=after_normal entered post input pointer array
    (BitVec.ofNat 64 (input.length%2^64-2)) enteredHeap (by omega) p arrayGlobal n domain pointerAligned arrayAligned upper arrayLower arrayBefore
    code failCode exceptionShape enough value tailRun
  have lengthSmall : input.length%2^64<2^64 := Nat.mod_lt _ (by decide)
  have encoded : (BitVec.ofNat 64 (input.length%2^64-2)).toNat=input.length%2^64-2 := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [encoded] at high
  exact ⟨extent,schema0,schema1,first,low,high,next,paid,bound,nextEq,nextHeap,nextRun⟩

end InitECandidate.Solver.Input.Header

#print axioms InitECandidate.Solver.Input.Header.first_container
