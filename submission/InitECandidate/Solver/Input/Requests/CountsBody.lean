import InitECandidate.Solver.Input.Requests.CountsTrace
import InitECandidate.Solver.Input.Requests.Output
import InitECandidate.Solver.Input.StructureFieldFrame

namespace InitECandidate.Solver.Input.Requests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Complete original five-list request suffix. Each actual non-timeout
execution either raises its real list error within335 source ticks or returns
the allocated request with all ten exact cells, arithmetic and input bytes.
Every word outside that actual80-byte structure and the full control/FFI
frame survive; no parser validity or future normal-return premise is assumed. -/
theorem counts_body (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (blob pointer cursor total : BitVec 64)
    (words : Nat → BitVec 64) (model : CountLocals source words total pointer cursor)
    (installed : OriginalCode.Installed source.code) (shape : source.eshapes.lookup (ofString "SszErr") = some .one)
    (heap : Blob.HeapInput source input blob) (domain : source.memaddrs = InitE.ordinaryDomain) (arena : Arena cursor 80)
    (blobAligned : blob.toNat % 8 = 0) (cursorAligned : cursor.toNat % 8 = 0)
    (afterInput : blob.toNat + input.length % 2^64 + 8 ≤ cursor.toNat)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source countCalls = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (∃ error : BitVec 64,(error = 30#64 ∨ error = 31#64) ∧ result = some (.exception (ofString "SszErr") (.val (.word error))) ∧ source.clock - post.clock ≤ 335) ∨
    (result = some (.returned (.val (.word cursor))) ∧ Blob.HeapInput post input blob ∧ source.clock - post.clock ≤ 335 ∧ post.clock ≤ source.clock ∧
      BackingLayout.control post = BackingLayout.control source ∧
      (∀ query,query.toNat < cursor.toNat ∨ cursor.toNat + 80 ≤ query.toNat → post.memory query = source.memory query) ∧
      ∃ counts : Nat → BitVec 64, (∀ index < 5,post.memory (cursor + BitVec.ofNat 64 (16*index)) = .word (pointer + words index) ∧
        post.memory (cursor + BitVec.ofNat 64 (16*index+8)) = .word (counts index)) ∧
        (∀ index < 5,(counts index).toNat = (countSpan words total index).toNat / (elementSize index).toNat ∧ (countSpan words total index).toNat % (elementSize index).toNat = 0)) := by
  rcases counts_trace source post words total pointer cursor 0 5 rfl model installed shape result run notTimeout with rejected | normal
  · exact Or.inl rejected
  · obtain ⟨target,innerPost,counts,restoreStack,done,remaining,restored,pure⟩ := normal
    have memory : target.memory = source.memory := by have h := congrArg PanSemStateFiniteExact.memory done.frame; exact h
    have addresses : target.memaddrs = source.memaddrs := by have h := congrArg PanSemStateFiniteExact.memaddrs done.frame; exact h
    have endian : target.be = source.be := by have h := congrArg PanSemStateFiniteExact.be done.frame; exact h
    have bytes := Blob.HeapInput.of_fields source target input blob memory.symm addresses.symm endian.symm heap
    have output := output_execute target input blob pointer cursor total words counts done.model (fun index small => done.bindings index (by omega) small)
      bytes (addresses.trans domain) arena blobAligned cursorAligned afterInput
    have observed := output.1.symm.trans remaining
    have resultEq : result = some (.returned (.val (.word cursor))) := (congrArg Prod.fst observed).symm
    have innerEq : innerPost = emptyLocalsHOLFinite (Payload.applyFields target cursor (outputFields pointer words counts)) := (congrArg Prod.snd observed).symm
    have finalFrame : emptyLocalsHOLFinite post = emptyLocalsHOLFinite (Payload.applyFields target cursor (outputFields pointer words counts)) := by
      rw [restored,innerEq]
      exact pure _
    have finalMemory : post.memory = (Payload.applyFields target cursor (outputFields pointer words counts)).memory := by
      have h := congrArg PanSemStateFiniteExact.memory finalFrame
      exact h
    have finalDomain : post.memaddrs = target.memaddrs := by have h := congrArg PanSemStateFiniteExact.memaddrs finalFrame; exact h
    have finalEndian : post.be = target.be := by have h := congrArg PanSemStateFiniteExact.be finalFrame; exact h
    have finalClock : post.clock = target.clock := by have h := congrArg PanSemStateFiniteExact.clock finalFrame; exact h
    have finalHeap := Blob.HeapInput.of_fields (Payload.applyFields target cursor (outputFields pointer words counts)) post input blob finalMemory.symm finalDomain.symm finalEndian.symm output.2
    have targetControl : BackingLayout.control target = BackingLayout.control source := by
      have h := congrArg BackingLayout.control done.frame
      exact h
    have finalControl : BackingLayout.control post = BackingLayout.control source := by
      have h := congrArg BackingLayout.control finalFrame
      exact h.trans targetControl
    have validFields : ∀ field ∈ outputFields pointer words counts,field.1 < 80 := by intro field member; have bounds := output_valid pointer words counts field member; omega
    have outside (query : BitVec 64) (away : query.toNat < cursor.toNat ∨ cursor.toNat + 80 ≤ query.toNat) : post.memory query = source.memory query := by
      rw [finalMemory]
      exact (StructureStore.apply_fields_outside target cursor 80 arena (outputFields pointer words counts) validFields query away).trans (congrFun memory query)
    have cells (index : Nat) (small : index < 5) : post.memory (cursor + BitVec.ofNat 64 (16*index)) = .word (pointer + words index) ∧
        post.memory (cursor + BitVec.ofNat 64 (16*index+8)) = .word (counts index) := by
      rw [finalMemory]
      exact output_cells target cursor pointer words counts arena index small
    have cost := done.cost
    exact Or.inr ⟨resultEq,finalHeap,by rw [finalClock]; exact cost,by rw [finalClock]; exact done.forward,finalControl,outside,counts,cells,
      fun index small => done.arithmetic index (by omega) small⟩

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.counts_body
