import InitECandidate.Solver.Input.MainRequestsReturn
import InitECandidate.Solver.Input.StructureStore
import InitECandidate.Solver.Input.Witness.OffsetProgram

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang
open WitnessRadix.QueryBranch

def requestPointerStore : ProgHOL 64 := .store (Scalar.plus (localVar "si") 32) (localVar "rq")

theorem after_requests_shape : afterRequests = .seq requestPointerStore Witness.prefixBody := by
  simp only [afterRequests,requestsCall,afterHashes,hashesCall,afterPayload,continuation,requestBody,prefixBody,Header.continuation,Header.afterHeader,Header.body,
    Guest.guestFn_decode_stateless_input,Witness.prefixBody,Payload.dropLeading,progToHOL,shapeToHOL,Option.map_none,
    requestPointerStore,Scalar.plus,localVar,expToHOL,List.map_cons,List.map_nil]

end InitECandidate.Solver.Input.Request

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The original SI32 request-pointer store at any actual clock. Its real
arena/mapping are derived, and copied input, payload gas/count and all ten
returned request cells survive the exact write. -/
theorem store_request_pointer (input : Guest.InputBlob) (source caller current : PanSemStateFiniteExact 64 Guest.HostMemory) (counts : Nat → BitVec 64)
    (environment : Environment input source) (actual : RequestCaller input source caller)
    (returned : RequestsReturned input source caller current counts) (bounded : input.length % 2^64 ≤ Guest.maxInputBytes) :
    let next := StructureStore.stored current (RequestPrefix.cursor input) 32 (PayloadPrefix.finalCursor input)
    evaluateHOLFiniteState current Request.requestPointerStore = (none,next) ∧ RequestsReturned input source caller next counts ∧
      next.memory (RequestPrefix.cursor input + 32#64) = .word (PayloadPrefix.finalCursor input) := by
  have geometry := input_cursor_bounds input bounded
  have lower : 2713731432 + input.length % 2^64 + 8 ≤ DecoderSetup.cursor input := geometry.1
  have upper : DecoderSetup.cursor input ≤ 2847949152 := geometry.2.1
  have aligned : DecoderSetup.cursor input % 8 = 0 := geometry.2.2
  have smallBytes : input.length % 2^64 ≤ 134217712 := bounded
  have siNat : (RequestPrefix.cursor input).toNat = DecoderSetup.cursor input + 288 := by
    rw [RequestPrefix.cursor,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have addressNat : (RequestPrefix.cursor input + 32#64).toNat = DecoderSetup.cursor input + 320 := by
    rw [BitVec.toNat_add_of_lt (by change (RequestPrefix.cursor input).toNat + 32 < 2^64; rw [siNat]; omega),siNat]
    rfl
  have plNat := (PayloadPrefix.cursor_number input bounded).1
  have rqNat := PayloadPrefix.final_cursor_geometry input bounded returned.transactions
  have rq : current.locals.lookup (ofString "rq") = some (.val (.word (PayloadPrefix.finalCursor input))) := by rw [returned.locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have read := Request.local_word current "rq" (PayloadPrefix.finalCursor input) rq
  have domain := returned.domain.trans (actual.domain.trans environment.domain)
  obtain ⟨run,bytes,cell,frame⟩ := StructureStore.execute current input inputPointer (RequestPrefix.cursor input) 96 32 "si" (localVar "rq") (PayloadPrefix.finalCursor input)
    returned.bytes returned.si read domain ⟨by rw [siNat]; omega,by rw [siNat]; omega⟩ (by decide) (by rw [siNat]; omega) (by decide) (by decide)
    (by change 2713731432 + input.length % 2^64 + 8 ≤ _; rw [siNat]; omega)
  have payloadAway (offset : Nat) (small : offset < 136) : PayloadPrefix.cursor input + BitVec.ofNat 64 offset ≠ byteAddress (RequestPrefix.cursor input) 32 := by
    have encoded : (BitVec.ofNat 64 offset).toNat = offset := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have number : (PayloadPrefix.cursor input + BitVec.ofNat 64 offset).toNat = DecoderSetup.cursor input + 384 + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [encoded,plNat]; omega),encoded,plNat]
    intro same
    have equal := congrArg BitVec.toNat same
    change (PayloadPrefix.cursor input + BitVec.ofNat 64 offset).toNat = (RequestPrefix.cursor input + 32#64).toNat at equal
    rw [number,addressNat] at equal
    omega
  have requestAway (offset : Nat) (small : offset < 80) : PayloadPrefix.finalCursor input + BitVec.ofNat 64 offset ≠ byteAddress (RequestPrefix.cursor input) 32 := by
    have top := rqNat.2.2.2
    have bottom := rqNat.2.2.1
    have number : (PayloadPrefix.finalCursor input + BitVec.ofNat 64 offset).toNat = (PayloadPrefix.finalCursor input).toNat + offset := byteAddress_toNat _ offset (by omega)
    intro same
    have equal := congrArg BitVec.toNat same
    change (PayloadPrefix.finalCursor input + BitVec.ofNat 64 offset).toNat = (RequestPrefix.cursor input + 32#64).toNat at equal
    rw [number,addressNat] at equal
    omega
  let next := StructureStore.stored current (RequestPrefix.cursor input) 32 (PayloadPrefix.finalCursor input)
  have image : Requests.Image next (inputPointer + BitVec.ofNat 64 (requestStart input)) (PayloadPrefix.finalCursor input) (BitVec.ofNat 64 (requestLength input)) (Requests.offsetWord input (requestStart input)) counts := by
    constructor
    · intro index small
      have original := returned.image.cells index small
      exact ⟨(frame _ (requestAway (16*index) (by omega))).trans original.1,(frame _ (requestAway (16*index+8) (by omega))).trans original.2⟩
    · exact returned.image.arithmetic
  have metadata : RequestsReturned input source caller next counts := ⟨returned.locals,bytes,returned.control,returned.code,returned.domain,returned.exceptions,returned.heap,
    (frame _ (payloadAway 88 (by decide))).trans returned.gasCell,(frame _ (payloadAway 56 (by decide))).trans returned.countCell,
    returned.roots,returned.si,returned.globals,returned.layout,image,returned.transactions,returned.forward,returned.cost,returned.aggregate⟩
  exact ⟨run,metadata,cell⟩

/-- The same actual request continuation reaches the literal original witness
prefix after that one zero-clock SI store, retaining any later outcome. -/
theorem witness_after_request (input : Guest.InputBlob) (source caller current post : PanSemStateFiniteExact 64 Guest.HostMemory) (counts : Nat → BitVec 64)
    (environment : Environment input source) (actual : RequestCaller input source caller)
    (returned : RequestsReturned input source caller current counts) (bounded : input.length % 2^64 ≤ Guest.maxInputBytes)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState current Request.afterRequests = (result,post)) :
    ∃ next,RequestsReturned input source caller next counts ∧ next.clock = current.clock ∧
      next.memory (RequestPrefix.cursor input + 32#64) = .word (PayloadPrefix.finalCursor input) ∧ evaluateHOLFiniteState next Witness.prefixBody = (result,post) := by
  obtain ⟨stored,metadata,cell⟩ := store_request_pointer input source caller current counts environment actual returned bounded
  rw [Request.after_requests_shape,StateSteps.next_sequence current _ _ _ stored (Nat.le_refl _)] at run
  exact ⟨_,metadata,rfl,cell,run⟩

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Request.after_requests_shape
#print axioms InitECandidate.Solver.Input.Main.DecoderCall.store_request_pointer
#print axioms InitECandidate.Solver.Input.Main.DecoderCall.witness_after_request
