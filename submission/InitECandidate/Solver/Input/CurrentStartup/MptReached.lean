import InitECandidate.Solver.Input.CurrentStartup.MptInitialized
import InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrame

namespace InitECandidate.Solver.Input.CurrentStartup.MptWorkspace
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem main_decoder_cells {input : Guest.InputBlob}
    {origin source decoded current : PanSemStateFiniteExact 64 Guest.HostMemory}
    (entry : Main.Entry input origin)
    (startup : evaluateHOLFiniteState (Main.memoryState origin) (withTail routines .skip) = (none,source))
    (decoder : CallPrefix.Execution source DecoderPrefix.actions decoded)
    (root : CallPrefix.Execution decoded CurrentHash.RootEntry.actions current) :
    current.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word 2701134768#64)) := by
  have sourceCode : OriginalCode.Installed source.code := by
    rw [(evaluation_fields (Main.memoryState origin) source _ none startup).2.2.2]
    exact entry.code
  have decodedCode : OriginalCode.Installed decoded.code := by rw [decoder.runtime.2.2.2.1]; exact sourceCode
  have cells := (main_cells input origin source entry startup).1
  exact ((root.globals (ofString "mpt_hash_scratch") (WorkspaceFrame.root_prefix .mptHash decoded.code decodedCode)).trans
    (decoder.globals (ofString "mpt_hash_scratch") (WorkspaceFrame.decoder_prefix .mptHash source.code sourceCode))).trans cells

theorem main_decoder_key_cell {input : Guest.InputBlob}
    {origin source decoded current : PanSemStateFiniteExact 64 Guest.HostMemory}
    (entry : Main.Entry input origin)
    (startup : evaluateHOLFiniteState (Main.memoryState origin) (withTail routines .skip) = (none,source))
    (decoder : CallPrefix.Execution source DecoderPrefix.actions decoded)
    (root : CallPrefix.Execution decoded CurrentHash.RootEntry.actions current) :
    current.globals.lookup (ofString "mpt_key_scratch") = some (.val (.word 2701134808#64)) := by
  have sourceCode : OriginalCode.Installed source.code := by
    rw [(evaluation_fields (Main.memoryState origin) source _ none startup).2.2.2]
    exact entry.code
  have decodedCode : OriginalCode.Installed decoded.code := by rw [decoder.runtime.2.2.2.1]; exact sourceCode
  have cells := main_key_cell input origin source entry startup
  exact ((root.globals (ofString "mpt_key_scratch") (WorkspaceFrame.root_prefix .mptKey decoded.code decodedCode)).trans
    (decoder.globals (ofString "mpt_key_scratch") (WorkspaceFrame.decoder_prefix .mptKey source.code sourceCode))).trans cells

end InitECandidate.Solver.Input.CurrentStartup.MptWorkspace

#print axioms InitECandidate.Solver.Input.CurrentStartup.MptWorkspace.main_decoder_cells

#print axioms InitECandidate.Solver.Input.CurrentStartup.MptWorkspace.main_decoder_key_cell
