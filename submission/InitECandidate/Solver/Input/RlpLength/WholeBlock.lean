import InitECandidate.Solver.Input.RlpLength.EntryDeclarations

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete literal block_rlp_length. Header encoding is executed, its heap
is released, old input/records survive, and both actual RLP loops run. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array payload header buffer : BitVec 64) (txStart txLength wdStart wdCount : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (data : Data source input pointer array payload txStart txLength wdStart wdCount)
    (geometry : HeaderEncoding.Geometry header buffer)
    (inputBefore : pointer.toNat+input.length%2^64≤buffer.toNat)
    (arrayBefore : txLength≠0→array.toNat+16*VarList.decodedCount input txStart txLength≤buffer.toNat)
    (cellsBefore : ∀ offset∈([32,40,48,56] : List Nat),(payload+BitVec.ofNat 64 offset).toNat<buffer.toNat)
    (hdr : source.locals.lookup (ofString "hdr")=some (.val (.word header)))
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word payload)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word buffer)))
    (codes : Codes source)
    (facts : ∀ field∈HeaderEncoding.firstField::HeaderEncoding.baseRest,HeaderEncoding.FieldFacts source.memory header field)
    (optionalFacts : HeaderEncoding.wordAt source.memory (HeaderEncoding.address header 0)≠0#64→
      ∀ field∈HeaderEncoding.optionalFields,HeaderEncoding.FieldFacts source.memory header field)
    (enough : 12*VarList.decodedCount input txStart txLength+43*wdCount+1381≤source.clock) :
    ∃ target encoded paid,25*wdCount≤encoded ∧ encoded≤436208508+57*wdCount ∧
      paid≤12*VarList.decodedCount input txStart txLength+43*wdCount+1381 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-paid} ∧
      HeaderEncoding.OldMemory target.memory source.memory buffer := by
  classical
  let sm:=bind {source with clock:=source.clock-1} "mark" buffer
  have hdrM : sm.locals.lookup (ofString "hdr")=some (.val (.word header)):=
    (bind_lookup_other _ "mark" "hdr" _ (by decide)).trans hdr
  have plM : sm.locals.lookup (ofString "pl")=some (.val (.word payload)):=
    (bind_lookup_other _ "mark" "pl" _ (by decide)).trans pl
  have headerArgs : evalListHOLFinite sm (h:=fun address=>Classical.propDecidable (sm.memaddrs address)) [localVar "hdr"]=some [.val (.word header)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,hdrM]
  obtain ⟨memory,headerStart,headerLength,headerPaid,headerPositive,headerBound,headerCost,headerNumber,headerRun,oldMemory⟩:=
    HeaderEncoding.call_execute sm header buffer "he" [localVar "hdr"] afterHeader headerArgs codes.header geometry domain heap
      (HeaderEncoding.Codes.of_code source sm rfl codes.headerCodes) (HeaderEncoding.TailCodes.of_code source sm rfl codes.tailCodes)
      codes.alloc facts optionalFacts (by change 1346≤source.clock-1; omega)
  let sh:=HeaderEncoding.callerPost sm buffer memory "he" headerStart headerLength headerPaid
  have markH : sh.locals.lookup (ofString "mark")=some (.val (.word buffer)) := by
    change (sm.locals.update (ofString "he",HeaderEncoding.encodedPair headerStart headerLength)).lookup (ofString "mark")=_
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "he"≠ofString "mark" from by decide] using (bind_lookup_same {source with clock:=source.clock-1} "mark" buffer)
  have heH : sh.locals.lookup (ofString "he")=some (HeaderEncoding.encodedPair headerStart headerLength) := by
    change (sm.locals.update (ofString "he",HeaderEncoding.encodedPair headerStart headerLength)).lookup (ofString "he")=_
    simp [HolFiniteMapExact.update,FUPDATE]
  have plH : sh.locals.lookup (ofString "pl")=some (.val (.word payload)) := by
    change (sm.locals.update (ofString "he",HeaderEncoding.encodedPair headerStart headerLength)).lookup (ofString "pl")=_
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "he"≠ofString "pl" from by decide] using plM
  have heapH : sh.globals.lookup (ofString "heap_ptr")=some (.val (.word (HeaderEncoding.cursor buffer))) := by
    change (source.globals.update (ofString "heap_ptr",.val (.word (HeaderEncoding.cursor buffer)))).lookup (ofString "heap_ptr")=_
    simp [HolFiniteMapExact.update,FUPDATE]
  have releaseArgs : evalListHOLFinite sh (h:=fun address=>Classical.propDecidable (sh.memaddrs address)) [localVar "mark"]=some [.val (.word buffer)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,markH]
  have releaseRun:=HeapScope.release_call_execute sh buffer (HeaderEncoding.cursor buffer) [localVar "mark"] releaseArgs heapH codes.release
    (by change 1≤source.clock-1-headerPaid; omega)
  let released:=HeapScope.releasePost {sh with clock:=sh.clock-1} buffer
  have releasedFrame : emptyLocalsHOLFinite released=emptyLocalsHOLFinite {source with memory:=memory,clock:=source.clock-1-headerPaid-1} := by
    change emptyLocalsHOLFinite {source with
      globals:=(source.globals.update (ofString "heap_ptr",.val (.word (HeaderEncoding.cursor buffer)))).update (ofString "heap_ptr",.val (.word buffer))
      memory:=memory
      clock:=source.clock-1-headerPaid-1}=emptyLocalsHOLFinite {source with memory:=memory,clock:=source.clock-1-headerPaid-1}
    rw [RlpWrite.U256Put.restore_global source.globals (ofString "heap_ptr") (.val (.word buffer)) _ heap]
  have releasedData:=Data.of_old_memory source released input pointer array payload buffer txStart txLength wdStart wdCount oldMemory rfl rfl
    inputBefore arrayBefore cellsBefore data
  obtain ⟨target,encoded,phasePaid,lower,upper,phaseBound,number,phaseRun,phaseFrame⟩:=after_release_execute released input pointer array payload headerStart
    txStart txLength wdStart wdCount headerLength domain releasedData (Codes.of_code source released rfl codes) headerBound heH plH
      (by change 12*VarList.decodedCount input txStart txLength+43*wdCount+33≤source.clock-1-headerPaid-1; omega)
  have headerTail : evaluateHOLFiniteState sh afterHeader=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) := by
    rw [afterHeader,WitnessRadix.StateSteps.next_sequence sh released _ _ releaseRun (by change sh.clock-1≤sh.clock; omega)]
    exact phaseRun
  let final:=restore source "mark" (restore sm "he" target)
  let paid:=headerPaid+phasePaid+2
  have targetMemory:=congrArg PanSemStateFiniteExact.memory phaseFrame
  change target.memory=memory at targetMemory
  refine ⟨final,encoded,paid,lower,upper,by dsimp [paid]; omega,number,?_,?_,?_⟩
  · rw [entry_shape,HeapScope.mark_call_execute source buffer "mark" afterMark heap codes.mark (by omega)]
    change (let output:=evaluateHOLFiniteState sm afterMark;(output.1,restore source "mark" output.2))=_
    rw [afterMark,headerRun,headerTail]
  · have transfer:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>emptyLocalsHOLFinite {state with clock:=source.clock-1-headerPaid-1-phasePaid}) releasedFrame
    change emptyLocalsHOLFinite {released with clock:=released.clock-phasePaid}=
      emptyLocalsHOLFinite {source with memory:=memory,clock:=source.clock-1-headerPaid-1-phasePaid} at transfer
    have combined:=phaseFrame.trans transfer
    have subtract : source.clock-1-headerPaid-1-phasePaid=source.clock-paid := by dsimp [paid]; omega
    change emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-paid}
    simpa only [subtract,targetMemory] using combined
  · change HeaderEncoding.OldMemory target.memory source.memory buffer
    rw [targetMemory]
    exact oldMemory

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.execute
