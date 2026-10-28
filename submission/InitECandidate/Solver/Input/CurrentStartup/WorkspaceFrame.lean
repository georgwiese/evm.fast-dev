import InitECandidate.Solver.Input.CurrentStartup.WorkspacePointer
import InitECandidate.Solver.Input.CurrentHash.RootEntry

namespace InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrame
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
abbrev WorkspaceKey := OffsetsFrame.WorkspaceKey
abbrev key := OffsetsFrame.workspaceKey

/-- The actual caught-decoder handler also retains all three SSZ globals,
including serialization, byte output and its terminal FFI outcome. -/
theorem handler_preserves (workspace : WorkspaceKey) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key workspace) code DecoderPrefix.handler := by
  simp only [DecoderPrefix.handler, DecoderPrefix.decoderCall, afterStartup, Main.afterMemory, Main.body,
    CallPrefix.cutAt, seqTail, Guest.Software.guestFn_main, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  refine GlobalEffects.scoped_body (key workspace) code _ _ (Code.name .serialize_result) _ _
    (Code.formals .serialize_result) (Code.body .serialize_result) (Code.shape .serialize_result)
    (Code.installed code installed .serialize_result) (OffsetsFrame.serialize_result code installed workspace) ?_
  refine GlobalEffects.sequence (key workspace) code _ _ (GlobalEffects.byte_store (key workspace) code _ _) ?_
  refine GlobalEffects.sequence (key workspace) code _ _
    (GlobalEffects.call_body (key workspace) code (some none) (Code.name .output_write) _
      (Code.formals .output_write) (Code.body .output_write) (Code.shape .output_write)
      (Code.installed code installed .output_write) (OffsetsFrame.output_write code installed workspace)) ?_
  exact GlobalEffects.sequence (key workspace) code _ _
    (GlobalEffects.external (key workspace) code _ _ _ _ _) (GlobalEffects.returned (key workspace) code _)

theorem decoder_preserves (workspace : WorkspaceKey) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key workspace) code DecoderPrefix.decoderCall := by
  rw [DecoderPrefix.decoder_shape]
  exact GlobalEffects.caught_destination (key workspace) code (some (ofString "si"))
    (Code.name .decode_host_input) [] (Code.formals .decode_host_input) (Code.body .decode_host_input)
    (Code.shape .decode_host_input) (ofString "SszErr") (ofString "err_code") DecoderPrefix.handler
    (Code.installed code installed .decode_host_input)
    (OffsetsFrame.decode_host_input code installed workspace) (handler_preserves workspace code installed)

theorem decoder_prefix (workspace : WorkspaceKey) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key workspace) code (CallPrefix.program DecoderPrefix.actions .skip) := by
  rw [DecoderPrefix.actions_shape]
  simp only [CallPrefix.program]
  refine GlobalEffects.scoped_body (key workspace) code _ _ (Code.name .alloc) _ _
    (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
    (Code.installed code installed .alloc) (OffsetsFrame.alloc code installed workspace) ?_
  refine GlobalEffects.scoped_body (key workspace) code _ _ (Code.name .alloc) _ _
    (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
    (Code.installed code installed .alloc) (OffsetsFrame.alloc code installed workspace) ?_
  refine GlobalEffects.sequence (key workspace) code _ _
    (GlobalEffects.call_body (key workspace) code (some none) (Code.name .memzero) _
      (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
      (Code.installed code installed .memzero) (OffsetsFrame.memzero code installed workspace)) ?_
  refine GlobalEffects.declared (key workspace) code _ _ _ _ ?_
  refine GlobalEffects.declared (key workspace) code _ _ _ _ ?_
  exact GlobalEffects.sequence (key workspace) code _ _
    (decoder_preserves workspace code installed) (GlobalEffects.skip (key workspace) code)

theorem root_prefix (workspace : WorkspaceKey) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key workspace) code (CallPrefix.program CurrentHash.RootEntry.actions .skip) := by
  rw [CurrentHash.RootEntry.actions_shape]
  simp only [CallPrefix.program]
  exact GlobalEffects.scoped_body (key workspace) code _ _ (Code.name .alloc) _ _
    (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
    (Code.installed code installed .alloc) (OffsetsFrame.alloc code installed workspace)
    (GlobalEffects.skip (key workspace) code)

/-- The three actual initialized pointers survive main's decoder and real
root allocation. All prerequisites come from those original execution traces. -/
theorem main_cells {input : Guest.InputBlob}
    {origin source decoded current : PanSemStateFiniteExact 64 Guest.HostMemory}
    (entry : Main.Entry input origin)
    (startup : evaluateHOLFiniteState (Main.memoryState origin) (withTail routines .skip) = (none, source))
    (decoder : CallPrefix.Execution source DecoderPrefix.actions decoded)
    (root : CallPrefix.Execution decoded CurrentHash.RootEntry.actions current) :
    current.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)) ∧
    current.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word 2701132496#64)) ∧
    current.globals.lookup (ofString "zero_hashes") = some (.val (.word 2701132592#64)) := by
  have sourceCode : OriginalCode.Installed source.code := by
    rw [(evaluation_fields (Main.memoryState origin) source _ none startup).2.2.2]
    exact entry.code
  have decodedCode : OriginalCode.Installed decoded.code := by rw [decoder.runtime.2.2.2.1]; exact sourceCode
  have cells := EarlyWorkspace.main_workspaces input origin source entry startup
  have kept (workspace : WorkspaceKey) : current.globals.lookup (key workspace) = source.globals.lookup (key workspace) :=
    (root.globals (key workspace) (root_prefix workspace decoded.code decodedCode)).trans
      (decoder.globals (key workspace) (decoder_prefix workspace source.code sourceCode))
  exact ⟨(kept .offsets).trans cells.1, (kept .lengthChunk).trans cells.2.1, (kept .zeroHashes).trans cells.2.2⟩

end InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrame

#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrame.handler_preserves
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrame.decoder_preserves
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrame.decoder_prefix
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrame.root_prefix
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrame.main_cells
