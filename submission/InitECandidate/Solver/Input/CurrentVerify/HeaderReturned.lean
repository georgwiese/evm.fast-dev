import InitECandidate.Solver.Input.CurrentVerify.HeaderContext
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A genuine validator return preserves main's physical SI/payload/gas and
all witness images, and supplies its actual advanced heap/hash environment
before the original after-header continuation starts. -/
theorem after_headers_data {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array heap count nextHeap : BitVec 64} {pointers lengths : Nat→BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (sourceHeap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (returned : Headers.CurrentValidate.Returned source target array heap count 2701132160#64 2701132360#64 nextHeap pointers lengths 2701134640 boundary) :
    Data input (CallNormal.continuationEntry source target "vh" (Headers.CurrentValidate.result heap (Headers.CurrentValidate.hashesPointer heap count)))
      pointer si record gasWord boundary := by
  let ready:=CallNormal.continuationEntry source target "vh" (Headers.CurrentValidate.result heap (Headers.CurrentValidate.hashesPointer heap count))
  have arena : CurrentStartup.ArenaState ready := returned.context.arena.of_frame rfl
  have environment : CurrentKeccak.Hash.Environment ready 2701132160#64 2701132360#64 := returned.context.environment.of_frame rfl
  have little : ready.be=false := returned.metadata.2.1.trans data.little
  obtain ⟨cursor,cell,lower,upper,aligned⟩:=data.heap
  have cursorEq : cursor=heap := by
    have equal:=Option.some.inj (cell.symm.trans sourceHeap)
    cases equal
    rfl
  subst cursor
  have nextHeapData : NormalHeapEffects.AtLeast (boundary+32) ready :=
    ⟨nextHeap,returned.context.heapCell,by have h:=returned.heapAfter; omega,returned.context.heapBound,returned.context.heapAligned⟩
  have siLocal : ready.locals.lookup (ofString "si")=some (.val (.word si)) :=
    (CallNormal.continuation_lookup_other source target "vh" "si" _ (by decide)).trans data.siLocal
  obtain ⟨nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,nodeImage,codeImage,headerImage⟩:=data.witnesses
  have memory (query : BitVec 64) (low : 2701134640≤query.toNat) (high : query.toNat<boundary) : ready.memory query=source.memory query :=
    returned.input.words query low high
  have siFrame : ready.memory si=source.memory si := memory si nodeImage.siLower (by have h:=nodeImage.siBefore; omega)
  have gasNumber : (record+88#64).toNat=record.toNat+88 := byteAddress_toNat record 88 (by have h:=data.recordArena.upper; omega)
  have gasFrame : ready.memory (record+88#64)=source.memory (record+88#64) := by
    apply memory
    · rw [gasNumber]; have h:=data.recordInside.1; omega
    · rw [gasNumber]; have h:=data.recordInside.2; omega
  exact ⟨arena,little,environment,nextHeapData,siLocal,data.siArena,data.siAligned,data.recordArena,data.recordAligned,data.recordInside,
    siFrame.trans data.payloadCell,gasFrame.trans data.gasCell,data.gasBound,
    nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,
    nodeImage.of_interval (by decide) memory,codeImage.of_interval (by decide) memory,headerImage.of_interval (by decide) memory⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.after_headers_data
