import InitECandidate.Solver.Input.MainErrorBound
import InitECandidate.Solver.Input.MainDecoderReject

namespace InitECandidate.Solver.Input.Main.ErrorHandler
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def entry (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (error : BitVec 64) :=
  setVarHOLFinite (ofString "err_code") (.val (.word error)) {target with locals := (DecoderSetup.entered source input).locals}

/-- The original caller's actual output buffers and saved locals supply the
handler contract after any decoder exception, even if decoding changed their
contents, allocated memory or emitted FFI events. -/
theorem entry_cost (input : Guest.InputBlob) (before source target : PanSemStateFiniteExact 64 Guest.HostMemory) (error : BitVec 64)
    (copied : InputCopied input before source) (bounded : input.length % 2 ^ 64 ≤ Guest.maxInputBytes)
    (code : target.code = source.code) (domain : target.memaddrs = source.memaddrs) :
    (entry source target input error).clock - (evaluateHOLFiniteState (entry source target input error) DecoderCall.handler).2.clock ≤ 51 := by
  let current := entry source target input error
  let out := BitVec.ofNat 64 (DecoderSetup.cursor input)
  let root := DecoderSetup.zeroPointer input
  have geometry := input_cursor_bounds input bounded
  have lower : 2713731432 ≤ DecoderSetup.cursor input := by change 2713731432 ≤ (inputCursor input).toNat; omega
  have upper : DecoderSetup.cursor input ≤ 2847949152 := geometry.2.1
  have aligned : DecoderSetup.cursor input % 8 = 0 := geometry.2.2
  have outNumber : out.toNat = DecoderSetup.cursor input := by
    change (BitVec.ofNat 64 (DecoderSetup.cursor input)).toNat = _
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have rootNumber : root.toNat = DecoderSetup.cursor input + 256 := by
    change (BitVec.ofNat 64 (DecoderSetup.cursor input + 256)).toNat = _
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have locals := DecoderSetup.entered_bindings source input
  have outBinding : current.locals.lookup (ofString "out") = some (.val (.word out)) := by
    simpa [current,entry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "err_code" ≠ ofString "out" from by decide] using locals.2.1
  have rootBinding : current.locals.lookup (ofString "z32") = some (.val (.word root)) := by
    simpa [current,entry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "err_code" ≠ ofString "z32" from by decide] using locals.2.2.1
  have errorBinding : current.locals.lookup (ofString "err_code") = some (.val (.word error)) := by
    simp [current,entry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have installed : OriginalCode.Installed current.code := code.symm ▸ copied.code
  have mapped : current.memaddrs = InitE.ordinaryDomain := domain.trans copied.domain
  exact handler_cost current out root error installed outBinding rootBinding errorBinding mapped
    ⟨by rw [outNumber]; omega,by rw [outNumber]; omega⟩ ⟨by rw [rootNumber]; omega,by rw [rootNumber]; omega⟩
    (by rw [outNumber]; exact aligned) (by rw [rootNumber]; omega)

theorem early_cost (input : Guest.InputBlob) (before source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (copied : InputCopied input before source) (bounded : input.length % 2 ^ 64 ≤ Guest.maxInputBytes) :
    (DecoderCall.handlerState source input).clock - (evaluateHOLFiniteState (DecoderCall.handlerState source input) DecoderCall.handler).2.clock ≤ 51 := by
  let caller := DecoderSetup.entered source input
  have context := DecoderSetup.entered_context source input
  have code : caller.code = source.code := by have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code) context; exact h
  have domain : caller.memaddrs = source.memaddrs := by have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) context; exact h
  exact entry_cost input before source {caller with clock := caller.clock - 2} (DecoderCall.rejectionCode input) copied bounded code domain

end InitECandidate.Solver.Input.Main.ErrorHandler

#print axioms InitECandidate.Solver.Input.Main.ErrorHandler.entry_cost
#print axioms InitECandidate.Solver.Input.Main.ErrorHandler.early_cost
