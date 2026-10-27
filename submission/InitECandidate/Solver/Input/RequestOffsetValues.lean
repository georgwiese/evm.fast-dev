import InitECandidate.Solver.Input.RequestOffsetsNormal

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem le32_number (input : Guest.InputBlob) (start : Nat) (visible : start+3<Guest.maxInputBytes) :
    (BitVec.ofNat 64 (Guest.GasLimit.le32 input start)).toNat=Guest.GasLimit.le32 input start := by
  have bound:=Framing.le32_lt input start
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]

theorem request_values (input : Guest.InputBlob) (total : BitVec 64)
    (first : requestWords input 0=44#64)
    (valid : ∀ position<3,Offsets.ValidAt 44#64 total (requestWords input) position) :
    Guest.GasLimit.le32 input 18=44 ∧ 44≤Guest.GasLimit.le32 input 22 ∧
      Guest.GasLimit.le32 input 22≤Guest.GasLimit.le32 input 58 ∧ Guest.GasLimit.le32 input 58≤total.toNat := by
  have firstNat:=congrArg BitVec.toNat first
  change (BitVec.ofNat 64 (Guest.GasLimit.le32 input 18)).toNat=44 at firstNat
  rw [le32_number input 18 (by decide)] at firstNat
  have v1:=valid 1 (by decide)
  have v2:=valid 2 (by decide)
  change 44≤(BitVec.ofNat 64 (Guest.GasLimit.le32 input 22)).toNat ∧ _ at v1
  change _ ∧ (BitVec.ofNat 64 (Guest.GasLimit.le32 input 58)).toNat≤total.toNat ∧
    (0<2→(BitVec.ofNat 64 (Guest.GasLimit.le32 input 22)).toNat≤(BitVec.ofNat 64 (Guest.GasLimit.le32 input 58)).toNat) at v2
  simp only [le32_number input 22 (by decide),le32_number input 58 (by decide)] at v1 v2
  exact ⟨firstNat,v1.1,v2.2.2 (by decide),v2.2.1⟩

def payloadArguments : List (ExpHOL 64) := [
  .op .add [localVar "np",localVar "o_pl"],.op .sub [localVar "o_vh",localVar "o_pl"]]
def afterPayload : ProgHOL 64 := match continuation with | .decCall _ _ _ _ rest=>rest | _=>.skip

theorem payload_call_shape : continuation=.decCall (ofString "pl") .one (ofString "decode_payload") payloadArguments afterPayload := by
  simp only [continuation,requestBody,prefixBody,Header.continuation,Header.afterHeader,Header.body,Guest.Software.guestFn_decode_stateless_input,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,afterPayload,payloadArguments,localVar]

/-- Actual payload call arguments derived from the validator's fixed offset.
The payload slice is contained in the copied encoded extent. -/
theorem payload_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64)
    (np : source.locals.lookup (ofString "np")=some (.val (.word (pointer+18#64))))
    (pl : source.locals.lookup (ofString "o_pl")=some (.val (.word (requestWords input 0))))
    (vh : source.locals.lookup (ofString "o_vh")=some (.val (.word (requestWords input 1))))
    (first : Guest.GasLimit.le32 input 18=44) (lower : 44≤Guest.GasLimit.le32 input 22)
    (upper : Guest.GasLimit.le32 input 22≤input.length%2^64-18) (extent : 62≤input.length%2^64) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) payloadArguments=
      some [.val (.word (pointer+62#64)),.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 22-44)))] ∧
      Guest.GasLimit.le32 input 22-44≤input.length%2^64-62 := by
  classical
  have subtraction : BitVec.ofNat 64 (Guest.GasLimit.le32 input 22)-44#64=BitVec.ofNat 64 (Guest.GasLimit.le32 input 22-44) :=
    BitVec.ofNat_sub_ofNat_of_le _ 44 (by decide) lower
  refine ⟨?_,by omega⟩
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,payloadArguments,localVar,np,pl,vh,requestWords,first,
    valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.add_assoc,subtraction]

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.le32_number
#print axioms InitECandidate.Solver.Input.Request.request_values
#print axioms InitECandidate.Solver.Input.Request.payload_call_shape
#print axioms InitECandidate.Solver.Input.Request.payload_arguments
