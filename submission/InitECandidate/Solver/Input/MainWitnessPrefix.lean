import InitECandidate.Solver.Input.MainRequestStore
import InitECandidate.Solver.Input.Witness.PrefixTrace

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def witnessStart (input : Guest.InputBlob) := 2 + Guest.GasLimit.le32 input 6
def witnessLength (input : Guest.InputBlob) := input.length % 2^64 - 2 - Guest.GasLimit.le32 input 6
def witnessArray (input : Guest.InputBlob) := PersistentAlloc.rounded (PayloadPrefix.finalCursor input) 80#64

/-- Actual entry to the unchanged witness offset body after request decoding.
All bytes, saved SI/request cells and payload fields belong to this execution. -/
structure WitnessEntry (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (counts : Nat → BitVec 64) (allowance : Nat := 502) : Prop where
  bytes : Blob.HeapInput current input inputPointer
  pointer : current.locals.lookup (ofString "wp") = some (.val (.word (inputPointer + BitVec.ofNat 64 (witnessStart input))))
  length : current.locals.lookup (ofString "wlen") = some (.val (.word (BitVec.ofNat 64 (witnessLength input))))
  si : current.locals.lookup (ofString "si") = some (.val (.word (RequestPrefix.cursor input)))
  code : current.code = source.code
  domain : current.memaddrs = source.memaddrs
  exceptions : current.eshapes = source.eshapes
  heap : current.globals.lookup (ofString "heap_ptr") = some (.val (.word (witnessArray input)))
  globals : ∀ key,key ≠ ofString "heap_ptr" → current.globals.lookup key = source.globals.lookup key
  gasCell : current.memory (PayloadPrefix.cursor input + 88#64) = .word (BitVec.ofNat 64 (Guest.GasLimit.le64 input 474))
  countCell : current.memory (PayloadPrefix.cursor input + 56#64) = .word (BitVec.ofNat 64 (Payload.withdrawalCount input))
  requestCell : current.memory (RequestPrefix.cursor input + 32#64) = .word (PayloadPrefix.finalCursor input)
  requestLayout : Requests.Layout (Requests.offsetWord input (requestStart input)) (BitVec.ofNat 64 (requestLength input))
  requests : Requests.Image current (inputPointer + BitVec.ofNat 64 (requestStart input)) (PayloadPrefix.finalCursor input) (BitVec.ofNat 64 (requestLength input)) (Requests.offsetWord input (requestStart input)) counts
  transactions : Payload.transactionCount input ≤ (input.length % 2^64) / 4
  forward : current.clock ≤ source.clock
  cost : source.clock - current.clock ≤ (input.length % 2^64) / 4 + allowance

/-- The real witness length guard either raises SszErr82 or reaches its
literal offset body. Neither branch assumes a future helper return or clock. -/
theorem witness_prefix_trace_frame (input : Guest.InputBlob) (source caller current post : PanSemStateFiniteExact 64 Guest.HostMemory) (counts : Nat → BitVec 64)
    (environment : Environment input source) (actual : RequestCaller input source caller)
    (returned : RequestsReturned input source caller current counts) (layout : RequestLayout input)
    (bounded : input.length % 2^64 ≤ Guest.maxInputBytes)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState current Request.afterRequests = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (result = some (.exception (ofString "SszErr") (.val (.word 82#64))) ∧ source.clock - post.clock ≤ (input.length % 2^64) / 4 + 503) ∨
    (12 ≤ witnessLength input ∧ witnessStart input + witnessLength input = input.length % 2^64 ∧
      ∃ (next innerPost : PanSemStateFiniteExact 64 Guest.HostMemory) (restoreStack : PanSemStateFiniteExact 64 Guest.HostMemory → PanSemStateFiniteExact 64 Guest.HostMemory),
        WitnessEntry input source next counts ∧ evaluateHOLFiniteState next Witness.offsetBody = (result,innerPost) ∧ post = restoreStack innerPost ∧
        (∀ target,emptyLocalsHOLFinite (restoreStack target) = emptyLocalsHOLFinite target) ∧
        (∀ query,query≠byteAddress (RequestPrefix.cursor input) 32 → next.memory query=current.memory query) ∧ InitializerAllocations.context next=InitializerAllocations.context current) := by
  obtain ⟨storedRun,metadata,requestCell⟩ := store_request_pointer input source caller current counts environment actual returned bounded
  let stored := StructureStore.stored current (RequestPrefix.cursor input) 32 (PayloadPrefix.finalCursor input)
  have storedClock : stored.clock=current.clock := rfl
  have witnessRun : evaluateHOLFiniteState stored Witness.prefixBody=(result,post) := by
    rw [Request.after_requests_shape,StateSteps.next_sequence current stored _ _ storedRun (Nat.le_refl _)] at run
    exact run
  have upper : Guest.GasLimit.le32 input 6 ≤ input.length % 2^64 - 2 := by
    have := layout.requestLower
    have := layout.requestUpper
    have := layout.extent
    omega
  have code : stored.code = source.code := metadata.code.trans actual.code
  have installed : OriginalCode.Installed stored.code := code.symm ▸ environment.code
  have shape : stored.eshapes.lookup (ofString "SszErr") = some .one := by rw [metadata.exceptions,actual.exceptions]; exact environment.shapes .SszErr
  rcases Witness.prefix_trace stored post input inputPointer (Guest.GasLimit.le32 input 6) metadata.bytes (by have := layout.extent; omega) upper
    metadata.roots.1 metadata.roots.2.1 metadata.roots.2.2 (original_fail_code stored.code installed) shape result witnessRun notTimeout with rejected | normal
  · obtain ⟨short,same,cost⟩ := rejected
    have prefixCost := metadata.aggregate
    have forward := metadata.forward.trans actual.forward
    rw [storedClock] at cost
    change source.clock-current.clock≤(input.length%2^64)/4+502 at prefixCost
    change current.clock≤source.clock at forward
    exact Or.inl ⟨same,by omega⟩
  · obtain ⟨minimum,bytes,wp,wlen,innerPost,remaining,endpoint⟩ := normal
    let ready := Witness.prefixPrepared stored input inputPointer (Guest.GasLimit.le32 input 6)
    have si : ready.locals.lookup (ofString "si") = some (.val (.word (RequestPrefix.cursor input))) :=
      (bind_lookup_other _ "wlen" "si" _ (by decide)).trans ((bind_lookup_other _ "wp" "si" _ (by decide)).trans metadata.si)
    have image : Requests.Image ready (inputPointer + BitVec.ofNat 64 (requestStart input)) (PayloadPrefix.finalCursor input) (BitVec.ofNat 64 (requestLength input)) (Requests.offsetWord input (requestStart input)) counts := ⟨metadata.image.cells,metadata.image.arithmetic⟩
    have entry : WitnessEntry input source ready counts := ⟨bytes,wp,wlen,si,code,metadata.domain.trans actual.domain,metadata.exceptions.trans actual.exceptions,
      metadata.heap,metadata.globals,metadata.gasCell,metadata.countCell,requestCell,metadata.layout,image,metadata.transactions,metadata.forward.trans actual.forward,metadata.aggregate⟩
    exact Or.inr ⟨minimum,by dsimp only [witnessStart,witnessLength]; have := layout.extent; omega,ready,innerPost,Witness.restorePrefix stored inputPointer (Guest.GasLimit.le32 input 6),entry,remaining,endpoint,(by intro target; exact Witness.restore_prefix_frame _ target _ _),(by
      intro query different
      change StoreWord.put current.memory (byteAddress (RequestPrefix.cursor input) 32) (PayloadPrefix.finalCursor input) query=current.memory query
      simp only [StoreWord.put,if_neg different]),rfl⟩


/-- Entry/outcome projection of the stronger actual prefix memory frame. -/
theorem witness_prefix_trace (input : Guest.InputBlob) (source caller current post : PanSemStateFiniteExact 64 Guest.HostMemory) (counts : Nat → BitVec 64)
    (environment : Environment input source) (actual : RequestCaller input source caller)
    (returned : RequestsReturned input source caller current counts) (layout : RequestLayout input)
    (bounded : input.length % 2^64 ≤ Guest.maxInputBytes)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState current Request.afterRequests = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (result = some (.exception (ofString "SszErr") (.val (.word 82#64))) ∧ source.clock - post.clock ≤ (input.length % 2^64) / 4 + 503) ∨
    (12 ≤ witnessLength input ∧ witnessStart input + witnessLength input = input.length % 2^64 ∧
      ∃ (next innerPost : PanSemStateFiniteExact 64 Guest.HostMemory) (restoreStack : PanSemStateFiniteExact 64 Guest.HostMemory → PanSemStateFiniteExact 64 Guest.HostMemory),
        WitnessEntry input source next counts ∧ evaluateHOLFiniteState next Witness.offsetBody = (result,innerPost) ∧ post = restoreStack innerPost ∧
        (∀ target,emptyLocalsHOLFinite (restoreStack target) = emptyLocalsHOLFinite target)) := by
  rcases witness_prefix_trace_frame input source caller current post counts environment actual returned layout bounded result run notTimeout with rejected | normal
  · exact Or.inl rejected
  · obtain ⟨minimum,inside,next,innerPost,restoreStack,entry,remaining,endpoint,preserved,memory⟩ := normal
    exact Or.inr ⟨minimum,inside,next,innerPost,restoreStack,entry,remaining,endpoint,preserved⟩

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.witness_prefix_trace

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.witness_prefix_trace_frame
