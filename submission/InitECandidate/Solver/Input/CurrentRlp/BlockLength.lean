import InitECandidate.Solver.Input.CurrentRlp.BlockHeader
import InitECandidate.Solver.Input.HeapMarkTrace

namespace InitECandidate.Solver.Input.CurrentRlp.BlockLength
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch RlpLength

theorem after_mark_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array payload header buffer : BitVec 64) (txStart txLength wdStart wdCount : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (data : Block.Data source input pointer array payload txStart txLength wdStart wdCount)
    (geometry : HeaderEncoding.Geometry header buffer)
    (inputBefore : pointer.toNat+input.length%2^64≤buffer.toNat)
    (arrayBefore : txLength≠0→array.toNat+16*VarList.decodedCount input txStart txLength≤buffer.toNat)
    (cellsBefore : ∀ offset∈([32,40,48,56] : List Nat),(payload+BitVec.ofNat 64 offset).toNat<buffer.toNat)
    (installed : OriginalCode.Installed source.code)
    (hdr : source.locals.lookup (ofString "hdr")=some (.val (.word header)))
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word payload)))
    (mark : source.locals.lookup (ofString "mark")=some (.val (.word buffer)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word buffer))) (bounded : buffer.toNat≤2952790016)
    (facts : ∀ field∈HeaderEncoding.firstField::HeaderEncoding.baseRest,HeaderEncoding.FieldFacts source.memory header field)
    (optional : ∀ field∈HeaderEncoding.optionalFields,HeaderEncoding.FieldFacts source.memory header field) :
    source.clock-(evaluateHOLFiniteState source Block.afterMark).2.clock≤1347+tailPrice input txStart txLength wdCount := by
  obtain ⟨callee,called,h⟩:=HeaderEncoder.environment source.code.lookup header (HeaderEncoder.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "hdr"]=some [.val (.word header)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,hdr]
  have priced:=ClockCost.scoped_reached_current source "he" HeaderEncoding.returnShape (ofString "encode_header") [localVar "hdr"] _
    HeaderEncoder.body Block.afterHeader callee HeaderEncoding.returnShape 1346 (tailPrice input txStart txLength wdCount) args called
    (HeaderEncoder.body_cost (callEntryStateHOLFinite source callee) header buffer geometry domain installed h heap bounded facts optional) (by
      intro child value normal checked
      obtain ⟨start,encoded,positive,size,answer,ready⟩:=header_returned source child input pointer array payload header buffer txStart txLength wdStart wdCount
        domain data geometry inputBefore arrayBefore cellsBefore installed pl mark heap bounded facts optional callee h value normal
      exact tail_cost _ input pointer array payload buffer start txStart txLength wdStart wdCount encoded ready.domain ready.data ready.installed size
        ready.he ready.pl ready.mark ready.heap)
  change source.clock-(evaluateHOLFiniteState source Block.afterMark).2.clock≤1346+tailPrice input txStart txLength wdCount+1 at priced
  omega

theorem after_mark_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array payload header buffer : BitVec 64) (txStart txLength wdStart wdCount : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (data : Block.Data source input pointer array payload txStart txLength wdStart wdCount)
    (geometry : HeaderEncoding.Geometry header buffer)
    (inputBefore : pointer.toNat+input.length%2^64≤buffer.toNat)
    (arrayBefore : txLength≠0→array.toNat+16*VarList.decodedCount input txStart txLength≤buffer.toNat)
    (cellsBefore : ∀ offset∈([32,40,48,56] : List Nat),(payload+BitVec.ofNat 64 offset).toNat<buffer.toNat)
    (installed : OriginalCode.Installed source.code)
    (hdr : source.locals.lookup (ofString "hdr")=some (.val (.word header)))
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word payload)))
    (mark : source.locals.lookup (ofString "mark")=some (.val (.word buffer)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word buffer))) (bounded : buffer.toNat≤2952790016)
    (facts : ∀ field∈HeaderEncoding.firstField::HeaderEncoding.baseRest,HeaderEncoding.FieldFacts source.memory header field)
    (optional : ∀ field∈HeaderEncoding.optionalFields,HeaderEncoding.FieldFacts source.memory header field)
    (value : ValueHOL 64) (returned : evaluateHOLFiniteState source Block.afterMark=(some (.returned value),target)) :
    ∃ encoded,25*wdCount≤encoded ∧ encoded≤817879876+57*wdCount ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      value=.val (.word (BitVec.ofNat 64 encoded)) ∧ MemoryMetadata.erase target=MemoryMetadata.erase source ∧
      HeaderEncoding.OldMemory target.memory source.memory buffer := by
  obtain ⟨callee,called,h⟩:=HeaderEncoder.environment source.code.lookup header (HeaderEncoder.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "hdr"]=some [.val (.word header)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,hdr]
  obtain ⟨funded,child,childValue,inner,bodyRun,checked,remaining,endpoint⟩:=CallNormal.scoped_normal source target "he" HeaderEncoding.returnShape (ofString "encode_header")
    [localVar "hdr"] _ HeaderEncoder.body Block.afterHeader callee HeaderEncoding.returnShape args called value returned
  obtain ⟨start,headerLength,positive,size,answer,ready⟩:=header_returned source child input pointer array payload header buffer txStart txLength wdStart wdCount
    domain data geometry inputBefore arrayBefore cellsBefore installed pl mark heap bounded facts optional callee h childValue bodyRun
  let resumed:=CallNormal.continuationEntry source child "he" childValue
  obtain ⟨encoded,lower,upper,number,answer,frame⟩:=tail_normal resumed inner input pointer array payload buffer start txStart txLength wdStart wdCount headerLength
    ready.domain ready.data ready.installed size ready.he ready.pl ready.mark ready.heap value remaining
  have metadata:=(MemoryMetadata.of_frame frame).trans (ready.restored_metadata heap)
  have memory:=LocalEffects.memory_of_erase (HeapScope.releasePost resumed buffer) inner frame
  rw [endpoint]
  refine ⟨encoded,lower,upper,number,answer,metadata,?_⟩
  intro query before
  exact (congrFun memory query).trans (ready.memory query before)

/-- All outcomes of the actual current block_rlp_length are covered. The
header callback is invoked only after its own real normal return, and the
actual heap mark/release and both decoded loops are included. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array payload header buffer : BitVec 64) (txStart txLength wdStart wdCount : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (data : Block.Data source input pointer array payload txStart txLength wdStart wdCount)
    (geometry : HeaderEncoding.Geometry header buffer)
    (inputBefore : pointer.toNat+input.length%2^64≤buffer.toNat)
    (arrayBefore : txLength≠0→array.toNat+16*VarList.decodedCount input txStart txLength≤buffer.toNat)
    (cellsBefore : ∀ offset∈([32,40,48,56] : List Nat),(payload+BitVec.ofNat 64 offset).toNat<buffer.toNat)
    (installed : OriginalCode.Installed source.code)
    (hdr : source.locals.lookup (ofString "hdr")=some (.val (.word header)))
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word payload)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word buffer))) (bounded : buffer.toNat≤2952790016)
    (facts : ∀ field∈HeaderEncoding.firstField::HeaderEncoding.baseRest,HeaderEncoding.FieldFacts source.memory header field)
    (optional : ∀ field∈HeaderEncoding.optionalFields,HeaderEncoding.FieldFacts source.memory header field) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤price input txStart txLength wdCount := by
  by_cases zero : source.clock=0
  · omega
  let marked:=bind {source with clock:=source.clock-1} "mark" buffer
  have markedData:=Block.Data.of_fields source marked input pointer array payload txStart txLength wdStart wdCount rfl rfl rfl data
  have hdrM : marked.locals.lookup (ofString "hdr")=some (.val (.word header)):=bind_lookup_other _ "mark" "hdr" _ (by decide) |>.trans hdr
  have plM : marked.locals.lookup (ofString "pl")=some (.val (.word payload)):=bind_lookup_other _ "mark" "pl" _ (by decide) |>.trans pl
  have priced:=after_mark_cost marked input pointer array payload header buffer txStart txLength wdStart wdCount domain markedData geometry inputBefore arrayBefore cellsBefore
    installed hdrM plM (bind_lookup_same _ _ _) heap bounded facts optional
  rw [current_body,Block.entry_shape,HeapScope.mark_call_execute source buffer "mark" Block.afterMark heap (HeapScope.mark_original_code source.code installed) (by omega)]
  change source.clock-(evaluateHOLFiniteState marked Block.afterMark).2.clock≤_
  have monotone:=evaluateHOLFiniteState_clock_le marked Block.afterMark
  have clock : marked.clock=source.clock-1:=rfl
  unfold price tailPrice at *
  omega

/-- A genuine normal current block-length result derives the withdrawal
size lower bound, its actual returned word, the restored original heap and
all earlier input/header memory. There is no future-success premise. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array payload header buffer : BitVec 64) (txStart txLength wdStart wdCount : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (data : Block.Data source input pointer array payload txStart txLength wdStart wdCount)
    (geometry : HeaderEncoding.Geometry header buffer)
    (inputBefore : pointer.toNat+input.length%2^64≤buffer.toNat)
    (arrayBefore : txLength≠0→array.toNat+16*VarList.decodedCount input txStart txLength≤buffer.toNat)
    (cellsBefore : ∀ offset∈([32,40,48,56] : List Nat),(payload+BitVec.ofNat 64 offset).toNat<buffer.toNat)
    (installed : OriginalCode.Installed source.code)
    (hdr : source.locals.lookup (ofString "hdr")=some (.val (.word header)))
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word payload)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word buffer))) (bounded : buffer.toNat≤2952790016)
    (facts : ∀ field∈HeaderEncoding.firstField::HeaderEncoding.baseRest,HeaderEncoding.FieldFacts source.memory header field)
    (optional : ∀ field∈HeaderEncoding.optionalFields,HeaderEncoding.FieldFacts source.memory header field)
    (value : ValueHOL 64) (returned : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ encoded,25*wdCount≤encoded ∧ encoded≤817879876+57*wdCount ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      value=.val (.word (BitVec.ofNat 64 encoded)) ∧ MemoryMetadata.erase target=MemoryMetadata.erase source ∧
      HeaderEncoding.OldMemory target.memory source.memory buffer := by
  rw [current_body,Block.entry_shape] at returned
  obtain ⟨funded,inner,remaining,endpoint⟩:=HeapScope.mark_call_trace source target buffer "mark" Block.afterMark heap
    (HeapScope.mark_original_code source.code installed) (some (.returned value)) returned (by intro impossible; cases impossible)
  let marked:=bind {source with clock:=source.clock-1} "mark" buffer
  have markedData:=Block.Data.of_fields source marked input pointer array payload txStart txLength wdStart wdCount rfl rfl rfl data
  have hdrM : marked.locals.lookup (ofString "hdr")=some (.val (.word header)):=bind_lookup_other _ "mark" "hdr" _ (by decide) |>.trans hdr
  have plM : marked.locals.lookup (ofString "pl")=some (.val (.word payload)):=bind_lookup_other _ "mark" "pl" _ (by decide) |>.trans pl
  obtain ⟨encoded,lower,upper,number,answer,metadata,memory⟩:=after_mark_normal marked inner input pointer array payload header buffer txStart txLength wdStart wdCount
    domain markedData geometry inputBefore arrayBefore cellsBefore installed hdrM plM (bind_lookup_same _ _ _) heap bounded facts optional value remaining
  rw [endpoint]
  exact ⟨encoded,lower,upper,number,answer,metadata,memory⟩

end InitECandidate.Solver.Input.CurrentRlp.BlockLength

#print axioms InitECandidate.Solver.Input.CurrentRlp.BlockLength.after_mark_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.BlockLength.after_mark_normal
#print axioms InitECandidate.Solver.Input.CurrentRlp.BlockLength.body_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.BlockLength.body_normal
