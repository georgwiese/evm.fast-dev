import InitECandidate.Solver.Input.HashFields
import InitECandidate.Solver.Input.HashFieldCells

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Four actual SI words used by the original request hashing routine. -/
structure RequestHashImage (input : Guest.InputBlob) (current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  payload : current.memory (RequestPrefix.cursor input)=.word (PayloadPrefix.cursor input)
  hashes : current.memory (RequestPrefix.cursor input+8#64)=.word (inputPointer+18#64+Request.requestWords input 1)
  count : current.memory (RequestPrefix.cursor input+16#64)=.word (BitVec.ofNat 64 ((Guest.GasLimit.le32 input 58-Guest.GasLimit.le32 input 22)/32))
  parent : current.memory (RequestPrefix.cursor input+24#64)=.word (inputPointer+26#64)
  partition : (Guest.GasLimit.le32 input 58-Guest.GasLimit.le32 input 22)%32=0

structure RequestCaller (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  bytes : Blob.HeapInput current input inputPointer
  code : current.code = source.code
  exceptions : current.eshapes = source.eshapes
  domain : current.memaddrs = source.memaddrs
  heap : current.globals.lookup (ofString "heap_ptr") = some (.val (.word (PayloadPrefix.finalCursor input)))
  offsets : current.globals.lookup (ofString "ssz_offs") = some (.val (.word 2713715344#64))
  np : current.locals.lookup (ofString "np") = some (.val (.word (inputPointer + 18#64)))
  length : current.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6 - 16))))
  si : current.locals.lookup (ofString "si") = some (.val (.word (RequestPrefix.cursor input)))
  requestsOffset : current.locals.lookup (ofString "o_rq") = some (.val (.word (Request.requestWords input 2)))
  gasCell : current.memory (PayloadPrefix.cursor input + 88#64) = .word (BitVec.ofNat 64 (Guest.GasLimit.le64 input 474))
  countCell : current.memory (PayloadPrefix.cursor input + 56#64) = .word (BitVec.ofNat 64 (Payload.withdrawalCount input))
  transactions : Payload.transactionCount input ≤ (input.length % 2^64) / 4
  forward : current.clock ≤ source.clock
  cost : source.clock - current.clock ≤ (input.length % 2^64) / 4 + 153
  roots : current.locals.lookup (ofString "p") = some (.val (.word (inputPointer + 2#64))) ∧
    current.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64 - 2)))) ∧
    current.locals.lookup (ofString "o_wit") = some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6))))
  globals : ∀ key,key ≠ ofString "heap_ptr" → current.globals.lookup key = source.globals.lookup key
  image : Payload.Image current input inputPointer (PayloadPrefix.cursor input) (PayloadPrefix.length input) (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64)
  records : VarList.Records current input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64) (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input)
  ffi : current.ffi=source.ffi
  hashes : RequestHashImage input current
  payloadLayout : Payload.Layout input (PayloadPrefix.length input)

end InitECandidate.Solver.Input.Main.DecoderCall

namespace InitECandidate.Solver.Input.Main.PayloadPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

private theorem payload_field_away (input : Guest.InputBlob) (bounded : input.length % 2^64 ≤ Guest.maxInputBytes)
    (offset : BitVec 64) (small : offset.toNat ≤ 128) (field : Nat) (fieldSmall : field ≤ 88) :
    cursor input + offset ≠ byteAddress (RequestPrefix.cursor input) field := by
  have upper : DecoderSetup.cursor input ≤ 2847949152 := (input_cursor_bounds input bounded).2.1
  have payloadNat := (cursor_number input bounded).1
  have siNat : (RequestPrefix.cursor input).toNat = DecoderSetup.cursor input + 288 := by
    rw [RequestPrefix.cursor,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have destinationNat := byteAddress_toNat (RequestPrefix.cursor input) field (by rw [siNat]; omega)
  intro same
  have numbers := congrArg BitVec.toNat same
  rw [BitVec.toNat_add_of_lt (by rw [payloadNat]; omega),payloadNat,destinationNat,siNat] at numbers
  omega

/-- Real blob-hash count plus all three actual SI stores, reaching the
original request decoder caller. Passing count arithmetic, heap, input bytes
and real gas/count cells all belong to this same execution. -/
theorem hash_fields_trace (input : Guest.InputBlob) (source caller current post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : DecoderCall.Environment input source) (actualCaller : DecoderCall.PayloadCaller input source caller)
    (returned : Returned input caller current) (layout : DecoderCall.RequestLayout input) (bounded : input.length % 2^64 ≤ Guest.maxInputBytes)
    (siPayload : current.memory (RequestPrefix.cursor input)=.word (cursor input))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState current Request.hashesCall = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (∃ error : BitVec 64,(error = 30#64 ∨ error = 31#64) ∧ result = some (.exception (ofString "SszErr") (.val (.word error))) ∧ current.clock - post.clock ≤ 67) ∨
    (∃ next innerPost,DecoderCall.RequestCaller input source next ∧ evaluateHOLFiniteState next Request.requestsCall = (result,innerPost) ∧ post = restore current "nvh" innerPost) := by
  rcases hashes_trace input source caller current post environment actualCaller returned layout result run notTimeout with rejected | normal
  · exact Or.inl rejected
  · obtain ⟨next,innerPost,count,locals,countNat,remainder,forward,cost,aggregate,frame,bytes,gasCell,countCell,remaining,restored⟩ := normal
    have other (key : String) (nvh : ofString "nvh" ≠ ofString key) (pl : ofString "pl" ≠ ofString key) : next.locals.lookup (ofString key) = caller.locals.lookup (ofString key) := by
      rw [locals,returned.locals]
      simp [HolFiniteMapExact.lookup_update,FUPDATE,nvh,pl]
    have si := (other "si" (by decide) (by decide)).trans actualCaller.si
    have np := (other "np" (by decide) (by decide)).trans actualCaller.np
    have vh := (other "o_vh" (by decide) (by decide)).trans actualCaller.hashesOffset
    have nvh : next.locals.lookup (ofString "nvh") = some (.val (.word count)) := by
      rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
    have domain : next.memaddrs = source.memaddrs := by
      have projected := congrArg PanSemStateFiniteExact.memaddrs frame
      exact projected.trans (returned.domain.trans actualCaller.frame.domain)
    have code : next.code = source.code := by
      have projected := congrArg PanSemStateFiniteExact.code frame
      exact projected.trans (returned.code.trans actualCaller.frame.code)
    have exceptions : next.eshapes = source.eshapes := by
      have projected := congrArg PanSemStateFiniteExact.eshapes frame
      exact projected.trans (returned.exceptions.trans actualCaller.frame.exceptions)
    have globals : next.globals = current.globals := by
      have projected := congrArg PanSemStateFiniteExact.globals frame
      exact projected
    have geometry := input_cursor_bounds input bounded
    have upper : DecoderSetup.cursor input ≤ 2847949152 := geometry.2.1
    have lower : 2713731432 + input.length % 2^64 + 8 ≤ DecoderSetup.cursor input := geometry.1
    have aligned : DecoderSetup.cursor input % 8 = 0 := geometry.2.2
    have siNat : (RequestPrefix.cursor input).toNat = DecoderSetup.cursor input + 288 := by
      rw [RequestPrefix.cursor,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have stores := Request.hash_fields_execute next input inputPointer (RequestPrefix.cursor input) (inputPointer + 18#64) (Request.requestWords input 1) count bytes si np vh nvh
      (domain.trans environment.domain) ⟨by rw [siNat]; omega,by rw [siNat]; omega⟩ (by decide) (by rw [siNat]; omega)
      (by change 2713731432 + input.length % 2^64 + 8 ≤ _; rw [siNat]; omega)
    let target := Request.hashFieldsStored next (RequestPrefix.cursor input) (inputPointer + 18#64) (Request.requestWords input 1) count
    have targetRun := stores.1.symm.trans remaining
    have targetGas : target.memory (cursor input + 88#64) = .word (BitVec.ofNat 64 (Guest.GasLimit.le64 input 474)) :=
      (stores.2.2 _ (payload_field_away input bounded 88#64 (by decide) 8 (by decide))
        (payload_field_away input bounded 88#64 (by decide) 16 (by decide)) (payload_field_away input bounded 88#64 (by decide) 24 (by decide))).trans gasCell
    have targetCount : target.memory (cursor input + 56#64) = .word (BitVec.ofNat 64 (Payload.withdrawalCount input)) :=
      (stores.2.2 _ (payload_field_away input bounded 56#64 (by decide) 8 (by decide))
        (payload_field_away input bounded 56#64 (by decide) 16 (by decide)) (payload_field_away input bounded 56#64 (by decide) 24 (by decide))).trans countCell
    have heap : target.globals.lookup (ofString "heap_ptr") = some (.val (.word (finalCursor input))) := by
      change next.globals.lookup _ = _
      rw [globals]; exact returned.heap
    have offsets : target.globals.lookup (ofString "ssz_offs") = some (.val (.word 2713715344#64)) := by
      change next.globals.lookup _ = _
      rw [globals,returned.globals (ofString "ssz_offs") (by decide),actualCaller.frame.globals]
      simpa [HolFiniteMapExact.lookup_update,FUPDATE,show (ofString "heap_ptr" == ofString "ssz_offs") = false from by decide] using environment.offsets
    have nextForward := actualCaller.frame.forward
    have clockLower := actualCaller.frame.clockLower
    have returnedForward := returned.forward
    have otherGlobals (key : MlS) (different : key ≠ ofString "heap_ptr") : target.globals.lookup key = source.globals.lookup key := by
      change next.globals.lookup key = _
      rw [globals,returned.globals key different,actualCaller.frame.globals]
      simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    have nextMemory : next.memory=current.memory := by have h := congrArg PanSemStateFiniteExact.memory frame; exact h
    have image := Payload.Image.of_memory current next input inputPointer (cursor input) (length input) (PersistentAlloc.rounded (cursor input) 136#64) nextMemory returned.image
    have records := VarList.Records.of_memory current next input inputPointer (PersistentAlloc.rounded (cursor input) 136#64) _ _ nextMemory returned.records
    have targetImage : Payload.Image target input inputPointer (cursor input) (length input) (PersistentAlloc.rounded (cursor input) 136#64) := by
      apply Payload.Image.of_cells next target input inputPointer (cursor input) (length input) (PersistentAlloc.rounded (cursor input) 136#64) image
      intro field member
      have bound := (Payload.image_fields_valid input inputPointer (length input) (PersistentAlloc.rounded (cursor input) 136#64) field member).1
      have encoded : (BitVec.ofNat 64 field.1).toNat=field.1 := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      exact stores.2.2 _ (payload_field_away input bounded _ (by rw [encoded]; omega) 8 (by decide))
        (payload_field_away input bounded _ (by rw [encoded]; omega) 16 (by decide)) (payload_field_away input bounded _ (by rw [encoded]; omega) 24 (by decide))
    have plNat := (cursor_number input bounded).1
    have rounded := PersistentAlloc.rounded_nat (cursor input) 136#64 (by change (cursor input).toNat+136+7<2^64; rw [plNat]; omega)
    have arrayNat : (PersistentAlloc.rounded (cursor input) 136#64).toNat=DecoderSetup.cursor input+520 := by
      change (PersistentAlloc.rounded (cursor input) 136#64).toNat=((cursor input).toNat+136+7)/8*8 at rounded
      rw [plNat] at rounded
      omega
    have targetRecords : VarList.Records target input inputPointer (PersistentAlloc.rounded (cursor input) 136#64) (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) := by
      apply VarList.Records.of_after next target input inputPointer (PersistentAlloc.rounded (cursor input) 136#64) _ _ ((RequestPrefix.cursor input).toNat+32) records (by rw [siNat,arrayNat]; omega)
      intro query after
      have different (offset : Nat) (small : offset<32) : query≠byteAddress (RequestPrefix.cursor input) offset := by
        have address : (byteAddress (RequestPrefix.cursor input) offset).toNat=(RequestPrefix.cursor input).toNat+offset := byteAddress_toNat _ offset (by rw [siNat]; omega)
        intro same
        have equal := congrArg BitVec.toNat same
        rw [address] at equal
        omega
      exact stores.2.2 query (different 8 (by decide)) (different 16 (by decide)) (different 24 (by decide))
    have nextContext : InitializerAllocations.context next=InitializerAllocations.context current := by have h := congrArg InitializerAllocations.context frame; exact h
    have nextFfi : next.ffi=current.ffi := by have h := congrArg PanSemStateFiniteExact.ffi nextContext; exact h
    have returnedFfi : current.ffi=caller.ffi := by have h := congrArg PanSemStateFiniteExact.ffi returned.context; exact h
    have targetFfi : target.ffi=source.ffi := nextFfi.trans (returnedFfi.trans actualCaller.frame.ffi)
    have countWord : count=BitVec.ofNat 64 ((Guest.GasLimit.le32 input 58-Guest.GasLimit.le32 input 22)/32) := by rw [←countNat]; simp
    have exactCells := Request.hash_fields_cells next (RequestPrefix.cursor input) (inputPointer+18#64) (Request.requestWords input 1) count (by rw [siNat]; omega)
    have zeroAway (offset : Nat) (positive : 0<offset) (small : offset≤24) : RequestPrefix.cursor input≠byteAddress (RequestPrefix.cursor input) offset := by
      have address : (byteAddress (RequestPrefix.cursor input) offset).toNat=(RequestPrefix.cursor input).toNat+offset := byteAddress_toNat _ offset (by rw [siNat]; omega)
      intro same
      have equal := congrArg BitVec.toNat same
      rw [address] at equal
      omega
    have parentAdd : (18#64:BitVec 64)+8#64=26#64 := by decide
    have hashImage : DecoderCall.RequestHashImage input target := ⟨
      (stores.2.2 _ (zeroAway 8 (by decide) (by decide)) (zeroAway 16 (by decide) (by decide)) (zeroAway 24 (by decide) (by decide))).trans (by rw [nextMemory]; exact siPayload),
      exactCells.1,by rw [←countWord]; exact exactCells.2.1,by simpa only [BitVec.add_assoc,parentAdd] using exactCells.2.2,remainder⟩
    have metadata : DecoderCall.RequestCaller input source target := ⟨stores.2.1,code,exceptions,domain,heap,offsets,np,
      (other "nlen" (by decide) (by decide)).trans actualCaller.length,si,(other "o_rq" (by decide) (by decide)).trans actualCaller.requestsOffset,
      targetGas,targetCount,returned.transactions,by change next.clock ≤ source.clock; omega,by change source.clock - next.clock ≤ _; omega,
      ⟨(other "p" (by decide) (by decide)).trans actualCaller.roots.1,
        (other "len" (by decide) (by decide)).trans actualCaller.roots.2.1,
        (other "o_wit" (by decide) (by decide)).trans actualCaller.roots.2.2⟩,otherGlobals,targetImage,targetRecords,targetFfi,hashImage,returned.layout⟩
    exact Or.inr ⟨target,innerPost,metadata,targetRun,restored⟩

end InitECandidate.Solver.Input.Main.PayloadPrefix

#print axioms InitECandidate.Solver.Input.Main.PayloadPrefix.hash_fields_trace
