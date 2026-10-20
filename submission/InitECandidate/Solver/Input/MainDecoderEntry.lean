import InitECandidate.Solver.Input.MainDecoderCall
import InitECandidate.Solver.Input.MainDecoderPrefix
import InitECandidate.Solver.Input.MainSszWorkspace

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

structure Environment (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  pointer : source.locals.lookup (ofString "p") = some (.val (.word inputPointer))
  length : source.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (input.length % 2 ^ 64))))
  bytes : Blob.HeapInput source input inputPointer
  offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word 2713715344#64))
  heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (DecoderSetup.cursor input + 288))))
  scalars : OriginalScalarGlobals.Scalars source.globals
  code : OriginalCode.Installed source.code
  shapes : OriginalExceptions.Installed source.eshapes
  domain : source.memaddrs = InitE.ordinaryDomain
  shared : source.shMemaddrs = InitE.sharedDomain
  little : source.be = false
  oracle : source.ffi.oracle = InitE.sourceOracle
  host : source.ffi.ffiState = Guest.guestHostMemory input

/-- Main's real inp tuple and initialized global workspace derive both
callee parameters and all decoder entry facts. No decoded schema, gas or
normal-return premise is supplied. -/
theorem entry_data (input : Guest.InputBlob) (before source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (copied : InputCopied input before source) (bounded : input.length % 2 ^ 64 ≤ Guest.maxInputBytes) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      evalListHOLFinite (DecoderSetup.entered source input) (h := fun address => Classical.propDecidable ((DecoderSetup.entered source input).memaddrs address)) arguments =
        some (values inputPointer (input.length % 2 ^ 64)) ∧
      lookupCodeHOLFinite (DecoderSetup.entered source input).code.lookup (ofString "decode_stateless_input") (values inputPointer (input.length % 2 ^ 64)) = some (Header.body,callee,.one) ∧
      Environment input (callEntryStateHOLFinite (DecoderSetup.entered source input) callee) := by
  let caller := DecoderSetup.entered source input
  have context := DecoderSetup.entered_context source input
  have installed := InitializerAllocations.installed_of_context source caller context copied.code
  have currentDomain := (InitializerAllocations.domain_of_context source caller context).trans copied.domain
  have shapes : caller.eshapes = source.eshapes := by have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.eshapes) context; exact h
  have shared : caller.shMemaddrs = source.shMemaddrs := by have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.shMemaddrs) context; exact h
  have endian : caller.be = source.be := by have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) context; exact h
  have oracle : caller.ffi.oracle = source.ffi.oracle := InitializerAllocations.oracle_of_context source caller context
  have host : caller.ffi.ffiState = source.ffi.ffiState := by have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.ffi.ffiState) context; exact h
  have tuple : caller.locals.lookup (ofString "inp") = some (Blob.pair inputPointer (input.length % 2 ^ 64)) := (DecoderSetup.entered_bindings source input).1.trans copied.binding
  have args := arguments_read caller inputPointer (input.length % 2 ^ 64) tuple
  obtain ⟨callee,called,pointer,length⟩ := environment caller.code.lookup inputPointer (input.length % 2 ^ 64) (original_code caller.code installed)
  let entry := callEntryStateHOLFinite caller callee
  have bytes := Blob.HeapInput.of_fields caller entry input inputPointer rfl rfl rfl (DecoderSetup.entered_bytes input before source copied bounded)
  have offsets : entry.globals.lookup (ofString "ssz_offs") = some (.val (.word 2713715344#64)) :=
    (DecoderSetup.entered_other_global source input (ofString "ssz_offs") (by decide)).trans (copied.ssz_offsets input before source)
  have ready : Environment input entry := ⟨pointer,length,bytes,offsets,DecoderSetup.entered_heap source input,
    DecoderSetup.entered_scalars source input copied.scalars,installed,shapes.symm ▸ copied.shapes,currentDomain,
    shared.trans copied.shared,endian.trans copied.little,oracle.trans copied.oracle,host.trans copied.host⟩
  exact ⟨callee,args,called,ready⟩

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.entry_data
