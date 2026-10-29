import InitECandidate.Solver.Input.CurrentRlp.BlockTail

namespace InitECandidate.Solver.Input.CurrentRlp.BlockLength
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch RlpLength

/-- Physical facts at the actual resumed block caller after its genuine
header return. The input/transaction/withdrawal image comes from earlier
owned memory; the header's own normal contract supplies its current heap. -/
structure HeaderReturned (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array payload buffer headerStart : BitVec 64) (txStart txLength wdStart wdCount headerLength : Nat) : Prop where
  data : Block.Data current input pointer array payload txStart txLength wdStart wdCount
  domain : current.memaddrs=InitE.ordinaryDomain
  installed : OriginalCode.Installed current.code
  he : current.locals.lookup (ofString "he")=some (HeaderEncoding.encodedPair headerStart headerLength)
  pl : current.locals.lookup (ofString "pl")=some (.val (.word payload))
  mark : current.locals.lookup (ofString "mark")=some (.val (.word buffer))
  heap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word (HeaderEncoding.cursor buffer)))
  metadata : MemoryMetadata.erase current=MemoryMetadata.erase (HeaderEncoder.heapPost source buffer)
  memory : HeaderEncoding.OldMemory current.memory source.memory buffer

theorem header_returned (source child : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array payload header buffer : BitVec 64) (txStart txLength wdStart wdCount : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (data : Block.Data source input pointer array payload txStart txLength wdStart wdCount)
    (geometry : HeaderEncoding.Geometry header buffer)
    (inputBefore : pointer.toNat+input.length%2^64≤buffer.toNat)
    (arrayBefore : txLength≠0→array.toNat+16*VarList.decodedCount input txStart txLength≤buffer.toNat)
    (cellsBefore : ∀ offset∈([32,40,48,56] : List Nat),(payload+BitVec.ofNat 64 offset).toNat<buffer.toNat)
    (installed : OriginalCode.Installed source.code)
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word payload)))
    (mark : source.locals.lookup (ofString "mark")=some (.val (.word buffer)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word buffer))) (bounded : buffer.toNat≤2952790016)
    (facts : ∀ field∈HeaderEncoding.firstField::HeaderEncoding.baseRest,HeaderEncoding.FieldFacts source.memory header field)
    (optional : ∀ field∈HeaderEncoding.optionalFields,HeaderEncoding.FieldFacts source.memory header field)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (h : callee.lookup (ofString "h")=some (.val (.word header)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) HeaderEncoder.body=(some (.returned value),child)) :
    ∃ start encoded,1≤encoded ∧ encoded≤916 ∧ value=HeaderEncoding.encodedPair start encoded ∧
      HeaderReturned source (CallNormal.continuationEntry source child "he" value) input pointer array payload buffer start txStart txLength wdStart wdCount encoded := by
  obtain ⟨start,encoded,positive,upper,answer,arena,frame,memory⟩:=HeaderEncoder.body_normal (callEntryStateHOLFinite source callee) child header buffer geometry
    domain installed h heap bounded facts optional value normal
  let ready:=CallNormal.continuationEntry source child "he" value
  have metadata : MemoryMetadata.erase ready=MemoryMetadata.erase (HeaderEncoder.heapPost source buffer):=frame
  have readyDomain:=MemoryMetadata.domain metadata
  change ready.memaddrs=source.memaddrs at readyDomain
  have readyEndian:=MemoryMetadata.endian metadata
  change ready.be=source.be at readyEndian
  have readyCode:=MemoryMetadata.code metadata
  change ready.code=source.code at readyCode
  have readyData:=Block.Data.of_old_memory source ready input pointer array payload buffer txStart txLength wdStart wdCount memory readyDomain readyEndian
    inputBefore arrayBefore cellsBefore data
  have heapFrame:=congrArg PanSemStateFiniteExact.globals metadata
  change ready.globals=source.globals.update (ofString "heap_ptr",.val (.word (HeaderEncoding.cursor buffer))) at heapFrame
  refine ⟨start,encoded,positive,upper,answer,readyData,readyDomain.trans domain,by rw [readyCode]; exact installed,?_,?_,?_,?_,metadata,memory⟩
  · simpa only [answer] using CallNormal.continuation_lookup_same source child "he" value
  · exact (CallNormal.continuation_lookup_other source child "he" "pl" value (by decide)).trans pl
  · exact (CallNormal.continuation_lookup_other source child "he" "mark" value (by decide)).trans mark
  · rw [heapFrame]
    simp [HolFiniteMapExact.update,FUPDATE]

/-- Actual heap release undoes exactly the encoder's heap update; every
other nonlocal field was already retained by that real normal return. -/
theorem HeaderReturned.restored_metadata {source current : PanSemStateFiniteExact 64 Guest.HostMemory} {input : Guest.InputBlob}
    {pointer array payload buffer headerStart : BitVec 64} {txStart txLength wdStart wdCount headerLength : Nat}
    (ready : HeaderReturned source current input pointer array payload buffer headerStart txStart txLength wdStart wdCount headerLength)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word buffer))) :
    MemoryMetadata.erase (HeapScope.releasePost current buffer)=MemoryMetadata.erase source := by
  have projected:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>HeapScope.releasePost state buffer) ready.metadata
  change MemoryMetadata.erase (HeapScope.releasePost current buffer)=MemoryMetadata.erase (HeapScope.releasePost (HeaderEncoder.heapPost source buffer) buffer) at projected
  have restored : HeapScope.releasePost (HeaderEncoder.heapPost source buffer) buffer=source:=by
    change {source with globals:=(source.globals.update (ofString "heap_ptr",.val (.word (HeaderEncoding.cursor buffer)))).update (ofString "heap_ptr",.val (.word buffer))}=source
    rw [RlpWrite.U256Put.restore_global source.globals (ofString "heap_ptr") (.val (.word buffer)) _ heap]
  rw [restored] at projected
  exact projected

end InitECandidate.Solver.Input.CurrentRlp.BlockLength

#print axioms InitECandidate.Solver.Input.CurrentRlp.BlockLength.header_returned
#print axioms InitECandidate.Solver.Input.CurrentRlp.BlockLength.HeaderReturned.restored_metadata
