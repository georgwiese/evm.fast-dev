import InitECandidate.Solver.GasBudget.MsgNewNormal
import InitECandidate.Solver.MutableTable.ZeroWords

namespace InitECandidate.Solver.GasBudget.MsgNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix MutableTable

def callState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (start : Nat) :=
  bind {source with
    globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (start + 176))))
    memory := Zero.finalMemory source.memory (BitVec.ofNat 64 start) 176
    clock := source.clock - 10} name (BitVec.ofNat 64 start)

/-- Original scoped msg_new call, deriving its complete176byte reservation,
clear result, exact10source-clock cost and actual normal continuation. -/
theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat) (name : String) (continuation : ProgHOL 64)
    (lower : 2701131776 ≤ start) (bounded : start ≤ 33806089496) (aligned : start % 8 = 0)
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (msgCode : source.code.lookup (ofString "msg_new") = some (formals, body, .one))
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "msg_new") [] continuation) = (some (.returned value), post)) :
    MemoryRegion.Valid ⟨start, 176⟩ ∧ 10 ≤ source.clock ∧ ∃ inner,
      evaluateHOLFiniteState (callState source name start) continuation = (some (.returned value), inner) ∧ post = restore source name inner := by
  have positive := Input.CallNormal.normal_clock source post (ofString name) .one (ofString "msg_new") [] continuation value normal
  obtain ⟨callee, called⟩ := environment source.code.lookup msgCode
  obtain ⟨calleePost, returned, bodyRun⟩ := Input.CallNormal.callee_return source post (ofString name) .one (ofString "msg_new") [] [] body continuation callee .one rfl called positive value normal
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨region, fits, returnedEq, frame⟩ := body_normal entry calleePost start lower bounded aligned domain heap allocCode trapCode zeroCode returned bodyRun
  subst returned
  have caller := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frame
  have subtract : source.clock - 1 - 9 = source.clock - 10 := by omega
  have targetEq : {calleePost with locals := source.locals} = {source with
      globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (start + 176))))
      memory := Zero.finalMemory source.memory (BitVec.ofNat 64 start) 176
      clock := source.clock - 10} := by
    simpa only [emptyLocalsHOLFinite, entry, callEntryStateHOLFinite, subtract] using caller
  have resumed : Input.CallNormal.continuationEntry source calleePost name (.val (.word (BitVec.ofNat 64 start))) = callState source name start := by
    rw [Input.CallNormal.continuationEntry, targetEq]
    rfl
  have actual := Input.CallNormal.return_execute source calleePost name .one (ofString "msg_new") [] [] body continuation callee .one (.val (.word (BitVec.ofNat 64 start)))
    rfl called positive bodyRun (by simp [shapeOfHOLExact, shapeEqHOL])
  rw [resumed] at actual
  have resultEq := congrArg Prod.fst (actual.symm.trans normal)
  have postEq := congrArg Prod.snd (actual.symm.trans normal)
  refine ⟨region, ?_, (evaluateHOLFiniteState (callState source name start) continuation).2, Prod.ext resultEq rfl, postEq.symm⟩
  change 9 ≤ source.clock - 1 at fits
  omega

theorem cleared_word (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (start slot : Nat) (inside : 8 * (slot + 1) ≤ 176) :
    (callState source name start).memory (BitVec.ofNat 64 start + BitVec.ofNat 64 (8 * slot)) = .word 0#64 :=
  ZeroWords.final_cell source.memory _ 176 slot inside

theorem memory_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (start : Nat) (region : MemoryRegion.Valid ⟨start, 176⟩)
    (query : BitVec 64) (outside : query.toNat < start ∨ start + 176 ≤ query.toNat) : (callState source name start).memory query = source.memory query := by
  apply Zero.final_memory_away
  intro offset inside same
  have number := congrArg BitVec.toNat same
  change query.toNat = (byteAddress (MemoryRegion.pointer ⟨start, 176⟩) offset).toNat at number
  rw [MemoryRegion.byte_address, MemoryRegion.address_number _ region offset (by change offset ≤ 176; omega)] at number
  change query.toNat = start + offset at number
  omega

end InitECandidate.Solver.GasBudget.MsgNew

#print axioms InitECandidate.Solver.GasBudget.MsgNew.call_normal
#print axioms InitECandidate.Solver.GasBudget.MsgNew.cleared_word
#print axioms InitECandidate.Solver.GasBudget.MsgNew.memory_away
