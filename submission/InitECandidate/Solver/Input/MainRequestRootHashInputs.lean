import InitECandidate.Solver.Input.MainRequestRootHashData

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.Main.RequestRootHashData
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix

/-- The actual original request bytes lie inside the copied input. -/
theorem request_slice (input : Guest.InputBlob) (caller current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (actual : DecoderCall.DecoderReady input caller current) :
    DecoderCall.requestStart input+DecoderCall.requestLength input≤input.length%2^64 := by
  have a:=actual.layout.extent
  have b:=actual.layout.hashesUpper
  have c:=actual.layout.requestUpper
  unfold DecoderCall.requestStart DecoderCall.requestLength
  omega

/-- Every actual request count and mapped record slice follows from its
original decoded offset span, exact encoded record size and shared input. -/
theorem request_inputs (input : Guest.InputBlob) (caller current : PanSemStateFiniteExact 64 Guest.HostMemory) (counts : Nat→BitVec 64)
    (actual : DecoderCall.DecoderReady input caller current) (bounded : input.length%2^64≤Guest.maxInputBytes)
    (layout : Requests.Layout (Requests.offsetWord input (DecoderCall.requestStart input)) (BitVec.ofNat 64 (DecoderCall.requestLength input)))
    (image : Requests.Image current (inputPointer+BitVec.ofNat 64 (DecoderCall.requestStart input)) (PayloadPrefix.finalCursor input)
      (BitVec.ofNat 64 (DecoderCall.requestLength input)) (Requests.offsetWord input (DecoderCall.requestStart input)) counts) :
    ∀ kind : RequestsHash.Kind,(description input counts).requestCount kind≤input.length%2^64 ∧
      AllocatedBytes.Arena ((description input counts).requestPointer kind) ((description input counts).requestCount kind*kind.record.length) := by
  have inside := request_slice input caller current actual
  have inputBound : input.length%2^64≤134217712 := bounded
  have total : (BitVec.ofNat 64 (DecoderCall.requestLength input)).toNat=DecoderCall.requestLength input := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have inputArena : AllocatedBytes.Arena inputPointer (input.length%2^64) := ⟨by decide,by change 2713731432+input.length%2^64≤33806089496; omega⟩
  intro kind
  have tag := RequestsHash.tag_bound kind
  have offsetUpper := (layout.valid kind.tag tag).2.1
  rw [total] at offsetUpper
  have nextUpper : Requests.boundary (Requests.offsetWord input (DecoderCall.requestStart input)) (BitVec.ofNat 64 (DecoderCall.requestLength input)) (kind.tag+1)≤DecoderCall.requestLength input := by
    by_cases more : kind.tag+1<5
    · simpa only [Requests.boundary,if_pos more,total] using (layout.valid (kind.tag+1) more).2.1
    · simp only [Requests.boundary,if_neg more,total]
      exact Nat.le_refl _
  have size : (Requests.elementSize kind.tag).toNat=kind.record.length := by cases kind <;> rfl
  have bytes := Requests.Image.element_bytes current (inputPointer+BitVec.ofNat 64 (DecoderCall.requestStart input)) (PayloadPrefix.finalCursor input)
    (BitVec.ofNat 64 (DecoderCall.requestLength input)) (Requests.offsetWord input (DecoderCall.requestStart input)) counts image kind.tag tag
  rw [size,Requests.Layout.span_number _ _ layout kind.tag tag] at bytes
  have currentBoundary : Requests.boundary (Requests.offsetWord input (DecoderCall.requestStart input)) (BitVec.ofNat 64 (DecoderCall.requestLength input)) kind.tag=
      (Requests.offsetWord input (DecoderCall.requestStart input) kind.tag).toNat := by rw [Requests.boundary,if_pos tag]
  rw [currentBoundary] at bytes
  have byteExtent : (Requests.offsetWord input (DecoderCall.requestStart input) kind.tag).toNat+(counts kind.tag).toNat*kind.record.length≤DecoderCall.requestLength input := by
    rw [Nat.mul_comm] at bytes
    omega
  have positive : 1≤kind.record.length := by cases kind <;> decide
  have countBound : (counts kind.tag).toNat≤input.length%2^64 := by
    have scaled := Nat.mul_le_mul_left (counts kind.tag).toNat positive
    simp only [Nat.mul_one] at scaled
    exact Nat.le_trans scaled (by omega)
  have pointer : (description input counts).requestPointer kind=inputPointer+BitVec.ofNat 64 (DecoderCall.requestStart input+(Requests.offsetWord input (DecoderCall.requestStart input) kind.tag).toNat) := by
    change (inputPointer+BitVec.ofNat 64 (DecoderCall.requestStart input))+Requests.offsetWord input (DecoderCall.requestStart input) kind.tag=_
    rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,←BitVec.add_assoc]
  refine ⟨countBound,?_⟩
  rw [pointer]
  exact AllocatedBytes.Arena.subrange inputPointer (input.length%2^64)
    (DecoderCall.requestStart input+(Requests.offsetWord input (DecoderCall.requestStart input) kind.tag).toNat) ((counts kind.tag).toNat*kind.record.length) inputArena (by omega)

end InitECandidate.Solver.Input.Main.RequestRootHashData
#print axioms InitECandidate.Solver.Input.Main.RequestRootHashData.request_slice
#print axioms InitECandidate.Solver.Input.Main.RequestRootHashData.request_inputs
