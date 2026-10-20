import InitECandidate.Solver.Input.MainWitnessTrace
import InitECandidate.Solver.Input.VarList.RecordsIntervalFrame

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Physical final witness data with the actual original ordered slices. -/
def WitnessDecoded (input : Guest.InputBlob) (current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  Witness.offsetNat input (witnessStart input) 0=12 ∧ 12≤Witness.offsetNat input (witnessStart input) 1 ∧
  Witness.offsetNat input (witnessStart input) 1≤Witness.offsetNat input (witnessStart input) 2 ∧ Witness.offsetNat input (witnessStart input) 2≤witnessLength input ∧
  Witness.Decoded current input inputPointer (witnessArray input) (RequestPrefix.cursor input) (witnessStart input)
    (Witness.offsetNat input (witnessStart input) 0) (Witness.offsetNat input (witnessStart input) 1) (Witness.offsetNat input (witnessStart input) 2) (witnessLength input) (.val (.word (RequestPrefix.cursor input)))

theorem WitnessDecoded.of_frame (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame : emptyLocalsHOLFinite target=emptyLocalsHOLFinite source) (actual : WitnessDecoded input source) : WitnessDecoded input target := by
  obtain ⟨first,lower,ordered,upper,decoded⟩ := actual
  have memory : target.memory=source.memory := by have h := congrArg PanSemStateFiniteExact.memory frame; exact h
  have globals : target.globals=source.globals := by have h := congrArg PanSemStateFiniteExact.globals frame; exact h
  have domain : target.memaddrs=source.memaddrs := by have h := congrArg PanSemStateFiniteExact.memaddrs frame; exact h
  have endian : target.be=source.be := by have h := congrArg PanSemStateFiniteExact.be frame; exact h
  exact ⟨first,lower,ordered,upper,Witness.Decoded.of_fields source target _ _ _ _ _ _ _ _ _ _ memory globals domain endian decoded⟩

/-- Actual request object and its saved SI32 pointer after decoding. -/
def RequestsDecoded (input : Guest.InputBlob) (current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  current.memory (RequestPrefix.cursor input+32#64)=.word (PayloadPrefix.finalCursor input) ∧
    ∃ counts : Nat→BitVec 64,Requests.Layout (Requests.offsetWord input (requestStart input)) (BitVec.ofNat 64 (requestLength input)) ∧
      Requests.Image current (inputPointer+BitVec.ofNat 64 (requestStart input)) (PayloadPrefix.finalCursor input) (BitVec.ofNat 64 (requestLength input)) (Requests.offsetWord input (requestStart input)) counts

theorem RequestsDecoded.of_memory (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (memory : target.memory=source.memory) (actual : RequestsDecoded input source) : RequestsDecoded input target := by
  obtain ⟨cell,counts,layout,image⟩ := actual
  refine ⟨by rw [memory]; exact cell,counts,layout,?_,image.arithmetic⟩
  intro index small
  rw [memory]
  exact image.cells index small

/-- Both complete original request/witness decoders, from the actual request
caller to the original decoder return. Rejections include all real helper
failures and the final physical records survive the request's rq scope. -/
theorem requests_witness_trace_frame (input : Guest.InputBlob) (source caller post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : Environment input source) (actual : RequestCaller input source caller) (layout : RequestLayout input)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState caller Request.requestsCall=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤(input.length%2^64)/4+witnessLength input/2+522 ∧
      ((∃ error : BitVec 64,result=some (.exception (ofString "SszErr") (.val (.word error)))) ∨
       (result=some (.returned (.val (.word (RequestPrefix.cursor input)))) ∧ WitnessDecoded input post ∧
         (∀ query,inputPointer.toNat≤query.toNat → query.toNat<(PayloadPrefix.finalCursor input).toNat →
           query≠byteAddress (RequestPrefix.cursor input) 32 → query≠byteAddress (RequestPrefix.cursor input) 40 → query≠byteAddress (RequestPrefix.cursor input) 48 → query≠byteAddress (RequestPrefix.cursor input) 56 → query≠byteAddress (RequestPrefix.cursor input) 64 → query≠byteAddress (RequestPrefix.cursor input) 72 → query≠byteAddress (RequestPrefix.cursor input) 80 → post.memory query=caller.memory query) ∧
         Payload.Image post input inputPointer (PayloadPrefix.cursor input) (PayloadPrefix.length input) (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64) ∧
         VarList.Records post input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64) (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) ∧ RequestHashImage input post ∧ RequestsDecoded input post ∧ post.ffi=source.ffi)) := by
  rcases requests_return_trace input source caller post environment actual layout bounded result run notTimeout with rejected | normal
  · obtain ⟨error,allowed,same,cost,aggregate⟩ := rejected
    exact ⟨by omega,Or.inl ⟨error,same⟩⟩
  obtain ⟨current,final,counts,returned,remaining,endpoint⟩ := normal
  obtain ⟨cost,outcome⟩ := witness_suffix_frame input source caller current final counts environment actual returned layout bounded result remaining notTimeout
  have frame : emptyLocalsHOLFinite post=emptyLocalsHOLFinite final := by rw [endpoint]; rfl
  have clock : post.clock=final.clock := by have h := congrArg PanSemStateFiniteExact.clock frame; exact h
  refine ⟨by rw [clock]; exact cost,?_⟩
  rcases outcome with rejected | normal
  · obtain ⟨error,allowed,same⟩ := rejected
    exact Or.inl ⟨error,same⟩
  · obtain ⟨same,first,lower,ordered,upper,decoded,memory,requestCell,witnessContext⟩ := normal
    have data : WitnessDecoded input final := ⟨first,lower,ordered,upper,decoded⟩
    have geometry := witness_geometry input bounded actual.transactions
    have previous := PayloadPrefix.final_cursor_geometry input bounded actual.transactions
    have arrayAfter : (PayloadPrefix.finalCursor input).toNat<(witnessArray input).toNat := by rw [previous.1,geometry.1]; omega
    have postMemory : post.memory=final.memory := by have h := congrArg PanSemStateFiniteExact.memory frame; exact h
    have earlier (query : BitVec 64) (queryLower : inputPointer.toNat≤query.toNat) (before : query.toNat<(PayloadPrefix.finalCursor input).toNat)
        (requestPtr : query≠byteAddress (RequestPrefix.cursor input) 32) (nodePtr : query≠byteAddress (RequestPrefix.cursor input) 40)
        (nodeCount : query≠byteAddress (RequestPrefix.cursor input) 48) (codePtr : query≠byteAddress (RequestPrefix.cursor input) 56)
        (codeCount : query≠byteAddress (RequestPrefix.cursor input) 64) (headerPtr : query≠byteAddress (RequestPrefix.cursor input) 72) (headerCount : query≠byteAddress (RequestPrefix.cursor input) 80) : post.memory query=caller.memory query := by
      rw [postMemory]
      exact (memory query queryLower (by omega) requestPtr nodePtr nodeCount codePtr codeCount headerPtr headerCount).trans (returned.earlier query queryLower before requestPtr)
    have bounds := input_cursor_bounds input bounded
    have inputLower : 2713731432+input.length%2^64+8≤DecoderSetup.cursor input := bounds.1
    have cursorUpper : DecoderSetup.cursor input≤2847949152 := bounds.2.1
    have aligned : DecoderSetup.cursor input%8=0 := bounds.2.2
    have plNat := (PayloadPrefix.cursor_number input bounded).1
    have siNat : (RequestPrefix.cursor input).toNat=DecoderSetup.cursor input+288 := by rw [RequestPrefix.cursor,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have rounded := PersistentAlloc.rounded_nat (PayloadPrefix.cursor input) 136#64 (by change (PayloadPrefix.cursor input).toNat+136+7<2^64; rw [plNat]; omega)
    have arrayNat : (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64).toNat=DecoderSetup.cursor input+520 := by
      change (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64).toNat=((PayloadPrefix.cursor input).toNat+136+7)/8*8 at rounded
      rw [plNat] at rounded
      omega
    have usable (query : BitVec 64) (after : (PayloadPrefix.cursor input).toNat≤query.toNat) (before : query.toNat<(PayloadPrefix.finalCursor input).toNat) : post.memory query=caller.memory query := by
      have away (offset : Nat) (small : offset≤80) : query≠byteAddress (RequestPrefix.cursor input) offset := by
        have address : (byteAddress (RequestPrefix.cursor input) offset).toNat=(RequestPrefix.cursor input).toNat+offset := byteAddress_toNat _ offset (by rw [siNat]; omega)
        intro same
        have equal := congrArg BitVec.toNat same
        rw [address,siNat] at equal
        rw [plNat] at after
        omega
      apply earlier query _ before (away 32 (by decide)) (away 40 (by decide)) (away 48 (by decide)) (away 56 (by decide)) (away 64 (by decide)) (away 72 (by decide)) (away 80 (by decide))
      change 2713731432≤query.toNat
      rw [plNat] at after
      omega
    have payloadImage : Payload.Image post input inputPointer (PayloadPrefix.cursor input) (PayloadPrefix.length input) (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64) := by
      apply Payload.Image.of_region caller post input inputPointer (PayloadPrefix.cursor input) (PayloadPrefix.length input) (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64) (by rw [plNat]; omega) actual.image
      intro query after before
      apply usable query after
      rw [plNat] at before
      have bottom := previous.2.2.1
      omega
    have transactionRecords : VarList.Records post input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64) (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) := by
      apply VarList.Records.of_interval caller post input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64) _ _ (PayloadPrefix.finalCursor input).toNat actual.records
      · change (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64).toNat+16*Payload.transactionCount input≤_
        rw [arrayNat,previous.1]
      · intro query after before
        apply usable query _ before
        rw [arrayNat] at after
        rw [plNat]
        omega
    have siRoom : (RequestPrefix.cursor input).toNat+136≤33806089496 := by rw [siNat]; omega
    have earlierCell (offset : Nat) (small : offset≤24) : post.memory (byteAddress (RequestPrefix.cursor input) offset)=caller.memory (byteAddress (RequestPrefix.cursor input) offset) := by
      have number : (byteAddress (RequestPrefix.cursor input) offset).toNat=(RequestPrefix.cursor input).toNat+offset := byteAddress_toNat _ offset (by rw [siNat]; omega)
      have away (other : Nat) (otherLower : 32≤other) (otherUpper : other≤80) : byteAddress (RequestPrefix.cursor input) offset≠byteAddress (RequestPrefix.cursor input) other := by
        intro equal
        have sameOffset := (Payload.field_address_eq _ siRoom offset other (by omega) (by omega)).mp equal
        omega
      apply earlier _ _ _ (away 32 (by decide) (by decide)) (away 40 (by decide) (by decide)) (away 48 (by decide) (by decide)) (away 56 (by decide) (by decide)) (away 64 (by decide) (by decide)) (away 72 (by decide) (by decide)) (away 80 (by decide) (by decide))
      · change 2713731432≤_; rw [number,siNat]; omega
      · rw [number,siNat]; have bottom := previous.2.2.1; omega
    have cell0 : post.memory (RequestPrefix.cursor input)=caller.memory (RequestPrefix.cursor input) := by simpa [byteAddress] using earlierCell 0 (by decide)
    have hashImage : RequestHashImage input post := ⟨cell0.trans actual.hashes.payload,(earlierCell 8 (by decide)).trans actual.hashes.hashes,
      (earlierCell 16 (by decide)).trans actual.hashes.count,(earlierCell 24 (by decide)).trans actual.hashes.parent,actual.hashes.partition⟩
    have requestMemory (query : BitVec 64) (after : (PayloadPrefix.finalCursor input).toNat≤query.toNat) (before : query.toNat<(PayloadPrefix.finalCursor input).toNat+80) : post.memory query=current.memory query := by
      have away (offset : Nat) (small : offset≤80) : query≠byteAddress (RequestPrefix.cursor input) offset := by
        have address : (byteAddress (RequestPrefix.cursor input) offset).toNat=(RequestPrefix.cursor input).toNat+offset := byteAddress_toNat _ offset (by rw [siNat]; omega)
        intro same
        have equal := congrArg BitVec.toNat same
        rw [address,siNat] at equal
        have bottom := previous.2.2.1
        omega
      rw [postMemory]
      apply memory query _ _ (away 32 (by decide)) (away 40 (by decide)) (away 48 (by decide)) (away 56 (by decide)) (away 64 (by decide)) (away 72 (by decide)) (away 80 (by decide))
      · change 2713731432≤query.toNat; have bottom := previous.2.2.1; omega
      · rw [previous.1] at before
        rw [geometry.1]
        omega
    have bytesBound : input.length%2^64≤134217712 := bounded
    have requestCellFrame (offset : Nat) (small : offset<80) : post.memory (PayloadPrefix.finalCursor input+BitVec.ofNat 64 offset)=current.memory (PayloadPrefix.finalCursor input+BitVec.ofNat 64 offset) := by
      have number : (PayloadPrefix.finalCursor input+BitVec.ofNat 64 offset).toNat=(PayloadPrefix.finalCursor input).toNat+offset := byteAddress_toNat _ offset (by have top := previous.2.2.2; omega)
      exact requestMemory _ (by rw [number]; omega) (by rw [number]; omega)
    have requestImage : Requests.Image post (inputPointer+BitVec.ofNat 64 (requestStart input)) (PayloadPrefix.finalCursor input) (BitVec.ofNat 64 (requestLength input)) (Requests.offsetWord input (requestStart input)) counts := by
      constructor
      · intro index small
        have cells := returned.image.cells index small
        exact ⟨(requestCellFrame (16*index) (by omega)).trans cells.1,(requestCellFrame (16*index+8) (by omega)).trans cells.2⟩
      · exact returned.image.arithmetic
    have requestData : RequestsDecoded input post := ⟨(congrFun postMemory _).trans requestCell,counts,returned.layout,requestImage⟩
    have currentContext : InitializerAllocations.context current=InitializerAllocations.context caller := by have h := congrArg InitializerAllocations.context returned.control; exact h
    have finalContext := witnessContext.trans currentContext
    have finalFfi : final.ffi=caller.ffi := by have h := congrArg PanSemStateFiniteExact.ffi finalContext; exact h
    have postFfi : post.ffi=source.ffi := by
      have sameFfi : post.ffi=final.ffi := by rw [endpoint]; rfl
      exact sameFfi.trans (finalFfi.trans actual.ffi)
    exact Or.inr ⟨same,WitnessDecoded.of_frame input final post frame data,earlier,payloadImage,transactionRecords,hashImage,requestData,postFfi⟩



/-- Bound and actual witness-data projection retaining the original API. -/
theorem requests_witness_trace (input : Guest.InputBlob) (source caller post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : Environment input source) (actual : RequestCaller input source caller) (layout : RequestLayout input)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState caller Request.requestsCall=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤(input.length%2^64)/4+witnessLength input/2+522 ∧
      ((∃ error : BitVec 64,result=some (.exception (ofString "SszErr") (.val (.word error)))) ∨
       (result=some (.returned (.val (.word (RequestPrefix.cursor input)))) ∧ WitnessDecoded input post)) := by
  obtain ⟨cost,outcome⟩ := requests_witness_trace_frame input source caller post environment actual layout bounded result run notTimeout
  refine ⟨cost,?_⟩
  rcases outcome with rejected | normal
  · exact Or.inl rejected
  · exact Or.inr ⟨normal.1,normal.2.1⟩

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.WitnessDecoded.of_frame
#print axioms InitECandidate.Solver.Input.Main.DecoderCall.requests_witness_trace

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.requests_witness_trace_frame

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.RequestsDecoded.of_memory
