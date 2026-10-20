import InitECandidate.Solver.Input.MainPayloadSetup
import InitECandidate.Solver.Input.PayloadPrefixNormal

namespace InitECandidate.Solver.Input.Main.PayloadPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem ready_clock (entry : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) : (ready entry input).clock = entry.clock - 1 := rfl

theorem ready_context (entry : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :
    InitializerAllocations.context (ready entry input) = InitializerAllocations.context entry := rfl

theorem ready_globals (entry : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :
    (ready entry input).globals = entry.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded (cursor input) 136#64))) := rfl

private theorem update_shadow (globals : HolFiniteMapExact MlS (ValueHOL 64)) (old next : BitVec 64) :
    (globals.update (ofString "heap_ptr",.val (.word old))).update (ofString "heap_ptr",.val (.word next)) = globals.update (ofString "heap_ptr",.val (.word next)) := by
  apply HolFiniteMapExact.ext
  funext key
  simp only [HolFiniteMapExact.lookup_update_pointwise]
  by_cases same : key = ofString "heap_ptr" <;> simp [same]

/-- Current payload allocation composes with main's actual11tick callee
entry, retaining the new heap word and complete FFI/immutable metadata. -/
theorem ready_frame (input : Guest.InputBlob) (source entry : PanSemStateFiniteExact 64 Guest.HostMemory)
    (actual : DecoderCall.PayloadEntry input source entry) :
    ParserFrame source (ready entry input) (PersistentAlloc.rounded (cursor input) 136#64) 12 := by
  have globals : (ready entry input).globals = source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded (cursor input) 136#64))) := by
    rw [ready_globals,actual.frame.globals]
    exact update_shadow source.globals _ _
  exact ParserFrame.advance source entry (ready entry input) _ _ 11 1 actual.frame (ready_context entry input) globals (by rw [ready_clock]; omega) (by rw [ready_clock])

theorem ready_offsets (entry : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :
    (ready entry input).locals.lookup (ofString "o_extra") = some (.val (.word (Payload.offsetWords input 0))) ∧
    (ready entry input).locals.lookup (ofString "o_txs") = some (.val (.word (Payload.offsetWords input 1))) ∧
    (ready entry input).locals.lookup (ofString "o_wd") = some (.val (.word (Payload.offsetWords input 2))) ∧
    (ready entry input).locals.lookup (ofString "o_bal") = some (.val (.word (Payload.offsetWords input 3))) :=
  Payload.declared_offsets (Payload.headerStored entry inputPointer (cursor input) (length input)) input

theorem ready_length (entry : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (binding : entry.locals.lookup (ofString "len") = some (.val (.word (length input)))) :
    (ready entry input).locals.lookup (ofString "len") = some (.val (.word (length input))) := by
  exact (Payload.declared_other (Payload.headerStored entry inputPointer (cursor input) (length input)) input "len" (by decide) (by decide) (by decide) (by decide)).trans
    ((bind_lookup_other (PersistentAlloc.post {entry with clock := entry.clock - 1} (cursor input) 136#64) "pl" "len" _ (by decide)).trans binding)

theorem ready_pointer (entry : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (binding : entry.locals.lookup (ofString "p") = some (.val (.word (inputPointer + 62#64)))) :
    (ready entry input).locals.lookup (ofString "p") = some (.val (.word (inputPointer + 62#64))) := by
  exact (Payload.declared_other (Payload.headerStored entry inputPointer (cursor input) (length input)) input "p" (by decide) (by decide) (by decide) (by decide)).trans
    ((bind_lookup_other (PersistentAlloc.post {entry with clock := entry.clock - 1} (cursor input) 136#64) "pl" "p" _ (by decide)).trans binding)

theorem ready_pl (entry : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :
    (ready entry input).locals.lookup (ofString "pl") = some (.val (.word (cursor input))) := by
  exact (Payload.declared_other (Payload.headerStored entry inputPointer (cursor input) (length input)) input "pl" (by decide) (by decide) (by decide) (by decide)).trans (bind_lookup_same _ _ _)

theorem restore_frame (entry target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :
    emptyLocalsHOLFinite (Payload.restorePrefix entry input inputPointer (cursor input) (length input) target) = emptyLocalsHOLFinite target := rfl

end InitECandidate.Solver.Input.Main.PayloadPrefix

#print axioms InitECandidate.Solver.Input.Main.PayloadPrefix.ready_clock
#print axioms InitECandidate.Solver.Input.Main.PayloadPrefix.ready_context
#print axioms InitECandidate.Solver.Input.Main.PayloadPrefix.ready_globals
#print axioms InitECandidate.Solver.Input.Main.PayloadPrefix.ready_frame
#print axioms InitECandidate.Solver.Input.Main.PayloadPrefix.ready_offsets
#print axioms InitECandidate.Solver.Input.Main.PayloadPrefix.ready_length
#print axioms InitECandidate.Solver.Input.Main.PayloadPrefix.ready_pl

#print axioms InitECandidate.Solver.Input.Main.PayloadPrefix.ready_pointer

#print axioms InitECandidate.Solver.Input.Main.PayloadPrefix.restore_frame
