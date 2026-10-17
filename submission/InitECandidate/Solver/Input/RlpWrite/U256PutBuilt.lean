import InitECandidate.Solver.Input.RlpWrite.U256PutSuffix

namespace InitECandidate.Solver.Input.RlpWrite.U256Put
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole actual temporary-allocation U256 RLP writer. Its real release call
restores the original heap global; actual temporary and output writes remain. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Value.Words) (dst cursor : BitVec 64)
    (v : source.locals.lookup (ofString "v")=some (U256Value.tuple words))
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (codes : Codes source) (domain : source.memaddrs=InitE.ordinaryDomain)
    (cursorLower : 2701131776≤cursor.toNat) (fits : cursor.toNat+32≤33806089496)
    (dstArena : WitnessRadix.AllocatedBytes.Arena dst 41) (enough : 124≤source.clock) :
    ∃ target encoded paid,1≤encoded ∧ encoded≤41 ∧ paid≤124 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-paid} ∧
      (∀ query,BytesWrite.Away dst query 41→(∀ offset<32,query≠panByteAlignHOL (width:=64) (cursor+BitVec.ofNat 64 offset))→target.memory query=source.memory query) := by
  classical
  let entry:=prepared source cursor
  have vEntry : entry.locals.lookup (ofString "v")=some (U256Value.tuple words):=
    (prepared_other source cursor "v" (by decide) (by decide)).trans v
  have dEntry : entry.locals.lookup (ofString "dst")=some (.val (.word dst)):=
    (prepared_other source cursor "dst" (by decide) (by decide)).trans d
  have locals:=prepared_locals source cursor
  have heapEntry:=prepared_heap source cursor
  have entryCodes : Codes entry:=⟨codes.markCode,codes.allocCode,codes.minCode,
    ⟨codes.minCodes.byteCode,codes.minCodes.bitsCode,codes.minCodes.bitCode,codes.minCodes.limbCode⟩,
    codes.bytesCode,⟨codes.bytesCodes.header,codes.bytesCodes.beCode,codes.bytesCodes.put,codes.bytesCodes.copyCode⟩,codes.releaseCode⟩
  have temporary : WitnessRadix.AllocatedBytes.Arena cursor 32:=⟨cursorLower,fits⟩
  obtain ⟨target,encoded,suffixPaid,lower,upper,bound,suffixRun,frame,memory⟩:=suffix_execute entry words dst cursor cursor
    (WitnessRadix.PersistentAlloc.rounded cursor 32#64) vEntry dEntry locals.1 locals.2 heapEntry entryCodes domain temporary dstArena
      (by change 122≤source.clock-1-1; omega)
  let final:=restore source "mark" (restore (marked source cursor) "tmp" target)
  let paid:=suffixPaid+2
  refine ⟨final,encoded,paid,lower,upper,by dsimp [paid]; omega,?_,?_,?_,memory⟩
  · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  · rw [prepare_execute source cursor heap codes fits (by omega),suffixRun]
  · have releasedState : emptyLocalsHOLFinite (HeapScope.releasePost entry cursor)=emptyLocalsHOLFinite {source with clock:=source.clock-1-1} := by
      change emptyLocalsHOLFinite {source with
        globals:=(source.globals.update (ofString "heap_ptr",.val (.word (WitnessRadix.PersistentAlloc.rounded cursor 32#64)))).update (ofString "heap_ptr",.val (.word cursor))
        clock:=source.clock-1-1}=emptyLocalsHOLFinite {source with clock:=source.clock-1-1}
      rw [restore_global source.globals (ofString "heap_ptr") (.val (.word cursor)) _ heap]
    have transferred:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>emptyLocalsHOLFinite {state with memory:=target.memory,clock:=source.clock-1-1-suffixPaid}) releasedState
    change emptyLocalsHOLFinite {HeapScope.releasePost entry cursor with memory:=target.memory,clock:=entry.clock-suffixPaid}=
      emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-1-1-suffixPaid} at transferred
    have combined:=frame.trans transferred
    have subtract : source.clock-1-1-suffixPaid=source.clock-paid := by dsimp [paid]; omega
    change emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-paid}
    simpa only [subtract] using combined

end InitECandidate.Solver.Input.RlpWrite.U256Put

#print axioms InitECandidate.Solver.Input.RlpWrite.U256Put.execute
