import InitECandidate.Solver.Input.RlpWrite.U256PutPrepare

namespace InitECandidate.Solver.Input.RlpWrite.U256Put
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual min-writer/byte-encoder/release/return suffix. The saved heap mark
is written back by the real release call, while actual output memory remains. -/
theorem suffix_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Value.Words) (dst tmp mark old : BitVec 64)
    (v : source.locals.lookup (ofString "v")=some (U256Value.tuple words))
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (t : source.locals.lookup (ofString "tmp")=some (.val (.word tmp)))
    (m : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (codes : Codes source) (domain : source.memaddrs=InitE.ordinaryDomain)
    (tmpArena : WitnessRadix.AllocatedBytes.Arena tmp 32) (dstArena : WitnessRadix.AllocatedBytes.Arena dst 41) (enough : 122≤source.clock) :
    ∃ target encoded paid,1≤encoded ∧ encoded≤41 ∧ paid≤122 ∧
      evaluateHOLFiniteState source afterTemporary=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {HeapScope.releasePost source mark with memory:=target.memory,clock:=source.clock-paid} ∧
      (∀ query,BytesWrite.Away dst query 41→(∀ offset<32,query≠panByteAlignHOL (width:=64) (tmp+BitVec.ofNat 64 offset))→target.memory query=source.memory query) := by
  classical
  have minArgs : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "v",localVar "tmp"]=
      some [U256Value.tuple words,.val (.word tmp)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,v,t]
  have mapped : ∀ offset<32,source.memaddrs (panByteAlignHOL (width:=64) (tmp+BitVec.ofNat 64 offset)) := by
    intro offset inside
    exact WitnessRadix.AllocatedBytes.byte_mapped source tmp 32 offset domain tmpArena inside
  obtain ⟨minMemory,length,minPaid,lengthBound,minBound,minRun,minFrame⟩:=U256Min.call_execute source words tmp "n" [localVar "v",localVar "tmp"] afterMinimum
    minArgs codes.minCode codes.minCodes mapped (by omega)
  let sn:=bind {source with memory:=minMemory,clock:=source.clock-1-minPaid} "n" (BitVec.ofNat 64 length)
  have dN : sn.locals.lookup (ofString "dst")=some (.val (.word dst)):=
    (bind_lookup_other _ "n" "dst" _ (by decide)).trans d
  have tN : sn.locals.lookup (ofString "tmp")=some (.val (.word tmp)):=
    (bind_lookup_other _ "n" "tmp" _ (by decide)).trans t
  have mN : sn.locals.lookup (ofString "mark")=some (.val (.word mark)):=
    (bind_lookup_other _ "n" "mark" _ (by decide)).trans m
  have nN : sn.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))):=bind_lookup_same _ _ _
  have sourceRange:=WitnessRadix.AllocatedBytes.Arena.weaken tmp 32 length tmpArena lengthBound
  have destinationRange:=WitnessRadix.AllocatedBytes.Arena.weaken dst 41 (length+9) dstArena (by omega)
  obtain ⟨byte,access⟩:=bytes_access sn dst tmp length (by omega) domain sourceRange destinationRange
  have byteCodes : BytesWrite.Codes sn:=⟨codes.bytesCodes.header,codes.bytesCodes.beCode,codes.bytesCodes.put,codes.bytesCodes.copyCode⟩
  have byteArgs : evalListHOLFinite sn (h:=fun address=>Classical.propDecidable (sn.memaddrs address)) [localVar "dst",localVar "tmp",localVar "n"]=
      some [.val (.word dst),.val (.word tmp),.val (.word (BitVec.ofNat 64 length))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,dN,tN,nN]
  obtain ⟨byteMemory,encoded,bytePaid,lower,positive,upper,byteBound,number,byteRun,byteFrame⟩:=BytesWrite.call_execute sn dst tmp length byte "w"
    [localVar "dst",localVar "tmp",localVar "n"] afterEncoded byteArgs codes.bytesCode access byteCodes (by change length+21≤source.clock-1-minPaid; omega)
  let sw:=bind {sn with memory:=byteMemory,clock:=sn.clock-1-bytePaid} "w" (BitVec.ofNat 64 encoded)
  have wW : sw.locals.lookup (ofString "w")=some (.val (.word (BitVec.ofNat 64 encoded))):=bind_lookup_same _ _ _
  have markW : sw.locals.lookup (ofString "mark")=some (.val (.word mark)):=
    (bind_lookup_other _ "w" "mark" _ (by decide)).trans mN
  have releaseArgs : evalListHOLFinite sw (h:=fun address=>Classical.propDecidable (sw.memaddrs address)) [localVar "mark"]=some [.val (.word mark)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,markW]
  have heapW : sw.globals.lookup (ofString "heap_ptr")=some (.val (.word old)):=heap
  have releaseRun:=HeapScope.release_call_execute sw mark old [localVar "mark"] releaseArgs heapW codes.releaseCode
    (by change 1≤source.clock-1-minPaid-1-bytePaid; omega)
  let released:=HeapScope.releasePost {sw with clock:=sw.clock-1} mark
  have wReleased : released.locals.lookup (ofString "w")=some (.val (.word (BitVec.ofNat 64 encoded))):=wW
  have returnRun : evaluateHOLFiniteState released (.return (localVar "w"))=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),emptyLocalsHOLFinite released) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,toExact,localVar,wReleased,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have afterRun : evaluateHOLFiniteState sw afterEncoded=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),emptyLocalsHOLFinite released) := by
    rw [afterEncoded,WitnessRadix.StateSteps.next_sequence sw released _ _ releaseRun (by change sw.clock-1≤sw.clock; omega)]
    exact returnRun
  let tw:=restore sn "w" (emptyLocalsHOLFinite released)
  have byteScoped : evaluateHOLFiniteState sn afterMinimum=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),tw) := by
    rw [afterMinimum,byteRun,afterRun]
  let target:=restore source "n" tw
  let paid:=minPaid+bytePaid+3
  refine ⟨target,encoded,paid,positive,by omega,by dsimp [paid]; omega,?_,?_,?_⟩
  · rw [afterTemporary,minRun,byteScoped]
  · have subtract : source.clock-1-minPaid-1-bytePaid-1=source.clock-paid := by dsimp [paid]; omega
    change emptyLocalsHOLFinite {HeapScope.releasePost source mark with memory:=byteMemory,clock:=source.clock-1-minPaid-1-bytePaid-1}=
      emptyLocalsHOLFinite {HeapScope.releasePost source mark with memory:=byteMemory,clock:=source.clock-paid}
    rw [subtract]
  · intro query dstAway tmpAway
    have bytesAway : BytesWrite.Away dst query (length+9) := by
      intro offset inside
      exact dstAway offset (by omega)
    exact (byteFrame query bytesAway).trans (minFrame query tmpAway)

end InitECandidate.Solver.Input.RlpWrite.U256Put

#print axioms InitECandidate.Solver.Input.RlpWrite.U256Put.suffix_execute
