import InitECandidate.Solver.Input.MainInputProgram
import InitECandidate.Solver.Input.TerminatingPaddedScope

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def inputPointer : BitVec 64 := 2713731432#64
def inputAmount (input : Guest.InputBlob) := BitVec.ofNat 64 (input.length % 2 ^ 64 + 8)
def inputPrice (input : Guest.InputBlob) := Blob.copyRounds (input.length % 2 ^ 64) + 2

structure InputCopied (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  clock : current.clock = source.clock - inputPrice input
  bytes : Blob.HeapInput current input inputPointer
  binding : current.locals.lookup (ofString "inp") = some (Blob.pair inputPointer (input.length % 2 ^ 64))
  globals : current.globals = (PersistentAlloc.post source inputPointer (inputAmount input)).globals
  scalars : OriginalScalarGlobals.Scalars current.globals
  heap : current.globals.lookup (ofString "heap_ptr") = some (.val (.word (PersistentAlloc.rounded inputPointer (inputAmount input))))
  code : OriginalCode.Installed current.code
  shapes : OriginalExceptions.Installed current.eshapes
  domain : current.memaddrs = InitE.ordinaryDomain
  shared : current.shMemaddrs = InitE.sharedDomain
  little : current.be = false
  oracle : current.ffi.oracle = InitE.sourceOracle
  host : current.ffi.ffiState = Guest.guestHostMemory input
  history : StartupHistory input source

private theorem shared_after (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (program : ProgHOL 64)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source program = (result,target)) : target.shMemaddrs = source.shMemaddrs := by
  have encoded : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair (PanPropsEvalStateFiniteExact.ofPanSemFinite source) program =
      (result,PanPropsEvalStateFiniteExact.ofPanSemFinite target) := by
    simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite,run]
  exact (evaluateInvariantsHOLFinite program (PanPropsEvalStateFiniteExact.ofPanSemFinite source) result (PanPropsEvalStateFiniteExact.ofPanSemFinite target) encoded).2.1

/-- The actual accepted-length input call reaches its literal continuation
with the real copied bytes and returned inp tuple. Funding is derived from
the enclosing non-timeout run; the mathematical input length is unrestricted. -/
theorem input_copy_prefix (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (ready : InputReady input source) (bounded : input.length % 2 ^ 64 ≤ Guest.maxInputBytes)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterFork = (result,target)) (notTimeout : result ≠ some .timeOut) :
    inputPrice input ≤ source.clock ∧ ∃ current final,InputCopied input source current ∧
      evaluateHOLFiniteState current afterInput = (result,final) ∧ target = QueryBranch.restore source "inp" final := by
  obtain ⟨callee,called⟩ := Blob.environment source.code.lookup (Blob.original_code source.code ready.code)
  let padding := inputPrice input
  let padded := {source with clock := source.clock + padding}
  let entry := callEntryStateHOLFinite padded callee
  have lower : 2701131776 ≤ inputPointer.toNat := by decide
  have room : inputPointer.toNat + input.length % 2 ^ 64 + 8 ≤ 33806089496 := by
    change 2713731432 + input.length % 2 ^ 64 + 8 ≤ _
    change input.length % 2 ^ 64 ≤ 134217712 at bounded
    omega
  have aligned : inputPointer.toNat % 8 = 0 := by decide
  have enough : Blob.copyRounds (input.length % 2 ^ 64) + 1 ≤ entry.clock := by
    change Blob.copyRounds (input.length % 2 ^ 64) + 1 ≤ source.clock + (Blob.copyRounds (input.length % 2 ^ 64) + 2) - 1
    omega
  obtain ⟨bodyPost,bodyRun,bodyClock,bodyGlobals,bodyHost,bodyOracle,_,bodyDomain,bodyEndian⟩ :=
    Blob.execute entry input inputPointer bounded lower room aligned ready.heap (PersistentAlloc.original_code entry.code ready.code)
      ready.oracle ready.host ready.domain ready.shared enough
  obtain ⟨bytePost,byteRun,_,_,byteImage⟩ := Blob.execute_bytes entry input inputPointer bounded lower room aligned ready.little ready.heap
    (PersistentAlloc.original_code entry.code ready.code) ready.oracle ready.host ready.domain ready.shared enough
  have same : bodyPost = bytePost := congrArg Prod.snd (bodyRun.symm.trans byteRun)
  have image : Blob.HeapInput bodyPost input inputPointer := same.symm ▸ byteImage
  have copiedClock : bodyPost.clock = source.clock := by
    change bodyPost.clock = source.clock + (Blob.copyRounds (input.length % 2 ^ 64) + 2) - 1 - (Blob.copyRounds (input.length % 2 ^ 64) + 1) at bodyClock
    omega
  have fields := evaluation_fields entry bodyPost Blob.body (some (.returned (Blob.pair inputPointer (input.length % 2 ^ 64)))) bodyRun
  have bodyShared := shared_after entry bodyPost Blob.body (some (.returned (Blob.pair inputPointer (input.length % 2 ^ 64)))) bodyRun
  rw [after_fork_shape] at run
  obtain ⟨funded,_,_,final,remaining,restore⟩ := terminating_padded_scope source target bodyPost "inp" Blob.returnShape (ofString "input_blob") Blob.body afterInput
    callee Blob.returnShape (Blob.pair inputPointer (input.length % 2 ^ 64)) padding called (by change 1 ≤ Blob.copyRounds (input.length % 2 ^ 64) + 2; omega)
    bodyRun (by simp [Blob.pair,Blob.returnShape,shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]) result run notTimeout
  let current := CallNormal.continuationEntry source {bodyPost with clock := bodyPost.clock - padding} "inp" (Blob.pair inputPointer (input.length % 2 ^ 64))
  have currentGlobals : current.globals = (PersistentAlloc.post source inputPointer (inputAmount input)).globals := bodyGlobals
  have currentScalars : OriginalScalarGlobals.Scalars current.globals := by
    rw [currentGlobals]
    exact ready.scalars.update (ofString "heap_ptr") (PersistentAlloc.rounded inputPointer (inputAmount input))
  have currentHeap : current.globals.lookup (ofString "heap_ptr") = some (.val (.word (PersistentAlloc.rounded inputPointer (inputAmount input)))) := by
    rw [currentGlobals]
    simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
  have currentBinding : current.locals.lookup (ofString "inp") = some (Blob.pair inputPointer (input.length % 2 ^ 64)) := by
    simp [current,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have currentBytes : Blob.HeapInput current input inputPointer := Blob.HeapInput.of_fields bodyPost current input inputPointer rfl rfl rfl image
  have currentClock : current.clock = source.clock - inputPrice input := by change bodyPost.clock - padding = source.clock - inputPrice input; rw [copiedClock]
  have code : current.code = source.code := fields.2.2.2
  have shapes : current.eshapes = source.eshapes := fields.2.2.1
  have currentReady : InputCopied input source current := ⟨currentClock,currentBytes,currentBinding,currentGlobals,currentScalars,currentHeap,
    code.symm ▸ ready.code,shapes.symm ▸ ready.shapes,bodyDomain.trans ready.domain,bodyShared.trans ready.shared,
    bodyEndian.trans ready.little,bodyOracle.trans ready.oracle,bodyHost.trans ready.host,ready.history⟩
  exact ⟨by rw [copiedClock] at funded; exact funded,current,final,currentReady,remaining,restore⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.input_copy_prefix
