import InitECandidate.Solver.Input.BytesList.BodyNormal
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.Input.BytesList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual returned byte-list data and source cost at any supplied clock.
Clock padding funds inversion only; all conclusions concern the original run. -/
theorem normal_summary_any_clock (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array limit maximum : BitVec 64) (start length : Nat)
    (heap : Blob.HeapInput source input pointer) (inside : start+length≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))))
    (l : source.locals.lookup (ofString "lim")=some (.val (.word limit)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (lower : 2701131776≤pointer.toNat) (aligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (arrayAfter : pointer.toNat+input.length%2^64+8≤array.toNat)
    (room : array.toNat+4*length≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word array)))
    (arrayBound : array.toNat ≤ 2952790016)
    (trapCode : source.code.lookup (ofString "trap_with") = some (Trap.formals, Trap.body, .one))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one)
    (varCode : source.code.lookup (ofString "ssz_split_var_list")=some (VarList.formals,VarList.body,VarList.returnShape))
    (m : source.locals.lookup (ofString "maxb")=some (.val (.word maximum)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=pairValue (VarList.decodedArray array length) (VarList.decodedCount input start length) ∧
      VarList.Records post input pointer array start length ∧ VarList.decodedCount input start length≤limit.toNat ∧ Blob.HeapInput post input pointer ∧
      (∀ position<VarList.decodedCount input start length,
        (VarList.recordLength input start length (VarList.decodedCount input start length) position).toNat≤maximum.toNat) ∧
      source.clock-(2*(length/4)+2)≤post.clock ∧ post.clock≤source.clock ∧
      (∀ query : BitVec 64,query.toNat<array.toNat→post.memory query=source.memory query) ∧
      WitnessRadix.BackingLayout.control post=WitnessRadix.BackingLayout.control
        (if length=0 then source else WitnessRadix.PersistentAlloc.post source array
          (BitVec.ofNat 64 (16*(Guest.GasLimit.le32 input start/4)))) := by
  let padding := 2*(length/4)+4
  have paddedRun := panPropsEvaluateAddClockEq body source (some (.returned value)) post padding ⟨run, by simp⟩
  obtain ⟨tuple, records, countLimit, bytes, lengths, lowerClock, upperClock, memory, control⟩ :=
    body_normal {source with clock := source.clock + padding} {post with clock := post.clock + padding}
      input pointer array limit maximum start length heap inside p n l domain lower aligned arrayAligned arrayAfter room
      heapGlobal arrayBound trapCode allocCode failCode exceptionShape varCode m
      (by change 2*(length/4)+4 ≤ source.clock+padding; dsimp only [padding]; omega) value paddedRun
  have originalControl : WitnessRadix.BackingLayout.control post = WitnessRadix.BackingLayout.control
      (if length=0 then source else WitnessRadix.PersistentAlloc.post source array
        (BitVec.ofNat 64 (16*(Guest.GasLimit.le32 input start/4)))) := by
    by_cases empty : length = 0
    · simp only [if_pos empty] at control ⊢
      exact control
    · simp only [if_neg empty] at control ⊢
      exact control
  refine ⟨tuple, VarList.Records.of_memory _ post input pointer array start length rfl records,
    countLimit, Blob.HeapInput.of_fields _ post input pointer rfl rfl rfl bytes, lengths, ?_, ?_, memory, originalControl⟩
  · change source.clock+padding-(2*(length/4)+2) ≤ post.clock+padding at lowerClock
    omega
  · change post.clock+padding ≤ source.clock+padding at upperClock
    omega

end InitECandidate.Solver.Input.BytesList

#print axioms InitECandidate.Solver.Input.BytesList.normal_summary_any_clock
