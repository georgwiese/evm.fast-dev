import InitECandidate.Solver.Input.MainForkPrefix

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Immutable startup fields, retaining the real host state but erasing
accumulated events as well as local work, globals, memory and clock. -/
def startupContext (source : PanSemStateFiniteExact 64 Guest.HostMemory) := KeccakAbsorb.hashControl (InitializerAllocations.context source)

private theorem startup_of_hash (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : KeccakAbsorb.hashControl target = KeccakAbsorb.hashControl source) : startupContext target = startupContext source := by
  have h := congrArg InitializerAllocations.context same
  exact h

private theorem startup_of_context (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : InitializerAllocations.context target = InitializerAllocations.context source) : startupContext target = startupContext source :=
  congrArg KeccakAbsorb.hashControl same

theorem startup_context (source mptMiddle bnMiddle evmMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (mpt : MptReached source mptMiddle) (bn : BnReached source mptMiddle bnMiddle)
    (evm : EvmReached source bnMiddle evmMiddle) (fork : ForkReached source evmMiddle middle) : startupContext middle = startupContext source := by
  have mptContext := (startup_of_hash _ mptMiddle mpt.control).trans
    ((startup_of_context (sszState source) (MptInitialization.allocated (sszState source) 2713717456)
      (InitializerAllocations.template_context (sszState source) 2713717456 MptInitialization.actions)).trans (startup_of_context source (sszState source) (ssz_context source)))
  have secpContext := (startup_of_context mptMiddle (secpState mptMiddle) (secp_context mptMiddle)).trans mptContext
  have bnContext := (startup_of_hash _ bnMiddle bn.control).trans
    ((startup_of_context (secpState mptMiddle) (BnInitialization.template (secpState mptMiddle) 2713718728)
      (BnInitialization.template_context (secpState mptMiddle) 2713718728)).trans secpContext)
  have headerContext := (startup_of_context bnMiddle (headerState bnMiddle) (header_context bnMiddle)).trans bnContext
  have evmContext := (startup_of_hash _ evmMiddle evm.control).trans
    ((startup_of_context (headerState bnMiddle) (EvmInitialization.template (headerState bnMiddle) 2713730624)
      (EvmInitialization.template_context (headerState bnMiddle) 2713730624)).trans headerContext)
  exact (startup_of_hash _ middle fork.control).trans
    ((startup_of_context evmMiddle (ForkInitialization.template evmMiddle 2713730840) (ForkInitialization.template_context evmMiddle 2713730840)).trans evmContext)

private theorem globals_of_hash (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : KeccakAbsorb.hashControl target = KeccakAbsorb.hashControl source) : target.globals = source.globals := congrArg (fun state => state.globals) same

/-- Global initialization provenance retained for downstream buffer facts. -/
def StartupHistory (input : Guest.InputBlob) (current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ source mptMiddle bnMiddle evmMiddle,Entry input source ∧ MptReached source mptMiddle ∧ BnReached source mptMiddle bnMiddle ∧
    EvmReached source bnMiddle evmMiddle ∧ ForkReached source evmMiddle current

structure InputReady (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  code : OriginalCode.Installed source.code
  shapes : OriginalExceptions.Installed source.eshapes
  scalars : OriginalScalarGlobals.Scalars source.globals
  heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713731432#64))
  domain : source.memaddrs = InitE.ordinaryDomain
  shared : source.shMemaddrs = InitE.sharedDomain
  little : source.be = false
  oracle : source.ffi.oracle = InitE.sourceOracle
  host : source.ffi.ffiState = Guest.guestHostMemory input
  history : StartupHistory input source

theorem input_ready (input : Guest.InputBlob) (source mptMiddle bnMiddle evmMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (bn : BnReached source mptMiddle bnMiddle)
    (evm : EvmReached source bnMiddle evmMiddle) (fork : ForkReached source evmMiddle middle) : InputReady input middle := by
  have context := startup_context source mptMiddle bnMiddle evmMiddle middle mpt bn evm fork
  have code : middle.code = source.code := by have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code) context; exact h
  have shapes : middle.eshapes = source.eshapes := by have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.eshapes) context; exact h
  have domain : middle.memaddrs = source.memaddrs := by have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) context; exact h
  have shared : middle.shMemaddrs = source.shMemaddrs := by have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.shMemaddrs) context; exact h
  have endian : middle.be = source.be := by have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) context; exact h
  have oracle : middle.ffi.oracle = source.ffi.oracle := by have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.ffi.oracle) context; exact h
  have host : middle.ffi.ffiState = source.ffi.ffiState := by have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.ffi.ffiState) context; exact h
  have globals := globals_of_hash _ middle fork.control
  have scalars : OriginalScalarGlobals.Scalars middle.globals := by
    rw [globals]
    exact ForkInitialization.template_scalars evmMiddle 2713730840 (evm.scalars input source mptMiddle bnMiddle evmMiddle entry mpt bn)
  have heap : middle.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713731432#64)) := by
    rw [globals]
    exact ForkInitialization.template_heap evmMiddle 2713730840 (evm.heap source mptMiddle bnMiddle evmMiddle bn)
  exact ⟨code.symm ▸ entry.code,shapes.symm ▸ entry.shapes,scalars,heap,domain.trans entry.domain,shared.trans entry.shared,endian.trans entry.little,oracle.trans entry.oracle,host.trans entry.host,⟨source,mptMiddle,bnMiddle,evmMiddle,entry,mpt,bn,evm,fork⟩⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.startup_context
#print axioms InitECandidate.Solver.Input.Main.input_ready
