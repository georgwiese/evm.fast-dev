import InitECandidate.Solver.Input.MainPayloadReturn
import InitECandidate.Solver.Input.PayloadImageFrame
import InitECandidate.Solver.Input.VarList.RecordsAfterFrame
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang
open WitnessRadix.QueryBranch

def payloadPointerStore : ProgHOL 64 := .store (Scalar.plus (localVar "si") 0) (localVar "pl")
def hashesCall : ProgHOL 64 := match afterPayload with | .seq _ rest => rest | _ => .skip

theorem after_payload_shape : afterPayload = .seq payloadPointerStore hashesCall := by
  simp only [hashesCall,afterPayload,continuation,requestBody,prefixBody,Header.continuation,Header.afterHeader,Header.body,
    Guest.guestFn_decode_stateless_input,progToHOL,shapeToHOL,Option.map_none,payloadPointerStore,Scalar.plus,localVar,expToHOL,List.map_cons,List.map_nil]

end InitECandidate.Solver.Input.Request

namespace InitECandidate.Solver.Input.Main.PayloadPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The first real SI store after a normal payload return executes at any
clock. Its destination is derived from the saved caller, and separation
preserves the copied input, real gas/count cells and all parser globals. -/
theorem store_pointer (input : Guest.InputBlob) (source caller current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : DecoderCall.Environment input source) (actualCaller : DecoderCall.PayloadCaller input source caller)
    (returned : Returned input caller current) (bounded : input.length % 2^64 ≤ Guest.maxInputBytes) :
    let next := {current with memory := StoreWord.put current.memory (RequestPrefix.cursor input) (cursor input)}
    evaluateHOLFiniteState current Request.payloadPointerStore = (none,next) ∧ Returned input caller next ∧
      next.memory (RequestPrefix.cursor input) = .word (cursor input) ∧
      (∀ key,next.globals.lookup key = current.globals.lookup key) := by
  have geometry := input_cursor_bounds input bounded
  have upper : DecoderSetup.cursor input ≤ 2847949152 := geometry.2.1
  have lower : 2713731432 + input.length % 2^64 + 8 ≤ DecoderSetup.cursor input := geometry.1
  have siNat : (RequestPrefix.cursor input).toNat = DecoderSetup.cursor input + 288 := by
    rw [RequestPrefix.cursor,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have payloadNat := (cursor_number input bounded).1
  have si : current.locals.lookup (ofString "si") = some (.val (.word (RequestPrefix.cursor input))) := by
    rw [returned.locals]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show (ofString "pl" == ofString "si") = false from by decide] using actualCaller.si
  have pl : current.locals.lookup (ofString "pl") = some (.val (.word (cursor input))) := by
    rw [returned.locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have domain : current.memaddrs = InitE.ordinaryDomain := returned.domain.trans (actualCaller.frame.domain.trans environment.domain)
  have mapped : current.memaddrs (RequestPrefix.cursor input) := by
    rw [domain]
    apply BackingLayout.ordinary_mapped
    · rw [siNat]; omega
    · rw [siNat]; omega
    · rw [siNat]; have aligned : DecoderSetup.cursor input % 8 = 0 := geometry.2.2; omega
  have address : eval current (Scalar.plus (localVar "si") 0) = some (.val (.word (RequestPrefix.cursor input))) := by
    simp [eval,Scalar.plus,localVar,evalHOLExact,toExact,evalListHOLExact,si,valueIsWord,valueWord,wordOpHOL,wordOp]
  have value : eval current (localVar "pl") = some (.val (.word (cursor input))) := by
    simpa [eval,localVar,evalHOLExact,toExact] using pl
  have run := StoreWord.execute current _ _ (RequestPrefix.cursor input) (cursor input) address value mapped
  have bytes := Blob.HeapInput.store_separate current input inputPointer (RequestPrefix.cursor input) (cursor input) returned.bytes (by decide)
    (by change 2713731432 + input.length % 2^64 < 2^64; omega) (Or.inr (by change 2713731432 + input.length % 2^64 ≤ _; rw [siNat]; omega))
  have away (offset : BitVec 64) (small : offset.toNat ≤ 128) : cursor input + offset ≠ RequestPrefix.cursor input := by
    intro same
    have number := congrArg BitVec.toNat same
    rw [BitVec.toNat_add_of_lt (by rw [payloadNat]; omega),payloadNat,siNat] at number
    omega
  let next := {current with memory:=StoreWord.put current.memory (RequestPrefix.cursor input) (cursor input)}
  have image : Payload.Image next input inputPointer (cursor input) (length input) (PersistentAlloc.rounded (cursor input) 136#64) := by
    apply Payload.Image.of_cells current next input inputPointer (cursor input) (length input) (PersistentAlloc.rounded (cursor input) 136#64) returned.image
    intro field member
    have bound := (Payload.image_fields_valid input inputPointer (length input) (PersistentAlloc.rounded (cursor input) 136#64) field member).1
    have encoded : (BitVec.ofNat 64 field.1).toNat=field.1 := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    simp only [next,StoreWord.put,if_neg (away _ (by rw [encoded]; omega))]
  have rounded := PersistentAlloc.rounded_nat (cursor input) 136#64 (by change (cursor input).toNat+136+7<2^64; rw [payloadNat]; omega)
  have arrayNat : (PersistentAlloc.rounded (cursor input) 136#64).toNat=DecoderSetup.cursor input+520 := by
    change (PersistentAlloc.rounded (cursor input) 136#64).toNat=((cursor input).toNat+136+7)/8*8 at rounded
    rw [payloadNat] at rounded
    have aligned : DecoderSetup.cursor input%8=0 := geometry.2.2
    omega
  have records : VarList.Records next input inputPointer (PersistentAlloc.rounded (cursor input) 136#64) (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) := by
    apply VarList.Records.of_after current next input inputPointer (PersistentAlloc.rounded (cursor input) 136#64) _ _ ((RequestPrefix.cursor input).toNat+1) returned.records (by rw [siNat,arrayNat]; omega)
    intro query after
    have different : query≠RequestPrefix.cursor input := by intro same; rw [same] at after; omega
    simp only [next,StoreWord.put,if_neg different]
  have nextReturned : Returned input caller {current with memory := StoreWord.put current.memory (RequestPrefix.cursor input) (cursor input)} :=
    ⟨returned.locals,bytes,by simpa [StoreWord.put,away 88#64 (by decide)] using returned.gasCell,returned.gasBound,
      by simpa [StoreWord.put,away 56#64 (by decide)] using returned.countCell,
      returned.code,returned.domain,returned.endian,returned.exceptions,returned.heap,returned.transactions,returned.globals,returned.forward,returned.cost,image,records,returned.context,returned.layout⟩
  exact ⟨run,nextReturned,by simp [StoreWord.put],fun _ => rfl⟩

/-- Resume the literal next decoding call after that exact store; the later
decoder result can be any outcome. -/
theorem after_pointer (input : Guest.InputBlob) (source caller current post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : DecoderCall.Environment input source) (actualCaller : DecoderCall.PayloadCaller input source caller)
    (returned : Returned input caller current) (bounded : input.length % 2^64 ≤ Guest.maxInputBytes)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState current Request.afterPayload = (result,post)) :
    ∃ next,Returned input caller next ∧ next.memory (RequestPrefix.cursor input) = .word (cursor input) ∧
      next.clock = current.clock ∧ evaluateHOLFiniteState next Request.hashesCall = (result,post) := by
  obtain ⟨stored,metadata,cell,globals⟩ := store_pointer input source caller current environment actualCaller returned bounded
  rw [Request.after_payload_shape,StateSteps.next_sequence current _ _ _ stored (Nat.le_refl _)] at run
  exact ⟨_,metadata,cell,rfl,run⟩

end InitECandidate.Solver.Input.Main.PayloadPrefix

#print axioms InitECandidate.Solver.Input.Request.after_payload_shape
#print axioms InitECandidate.Solver.Input.Main.PayloadPrefix.store_pointer
#print axioms InitECandidate.Solver.Input.Main.PayloadPrefix.after_pointer
