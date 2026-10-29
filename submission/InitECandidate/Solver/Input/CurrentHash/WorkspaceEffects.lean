import InitECandidate.Solver.Input.CurrentHash.WorkspaceEntry

namespace InitECandidate.Solver.Input.CurrentHash.WorkspaceEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- All outcomes of the actual31-helper hash graph retain the initialized
workspace pointers. Digest memory values and returned results are unrestricted. -/
theorem Workspace.after_body {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    (data : Workspace source) (routine : Code.Routine) (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source (Code.body routine) = (result, post)) : Workspace post := by
  have kept (cursor : Cursor) : post.globals.lookup (key cursor) = source.globals.lookup (key cursor) := by
    have same := Effects.body_preserves cursor source.code data.code routine source rfl
    rw [actual] at same
    exact congrArg Prod.snd same
  have fields := evaluation_fields source post _ result actual
  refine ⟨?_, fields.1.trans data.domain, fields.2.1.trans data.little,
    (kept .offsets).trans data.offsets, (kept .lengthChunk).trans data.chunk, (kept .zeroHashes).trans data.zeros,
    (kept .keccakState).trans data.keccakState,(kept .keccakPad).trans data.keccakPad,(kept .mptHash).trans data.mptHash,(kept .mptKey).trans data.mptKey,(kept .mptEmpty).trans data.mptEmpty,(kept .shaState).trans data.shaState,(kept .shaPad).trans data.shaPad,(kept .u256Ws).trans data.u256,
    data.chunkArena, data.zeroArena, data.chunkAligned, data.zeroAligned⟩
  rw [fields.2.2.2]
  exact data.code

/-- The real tail, ignored and local-result callers preserve the same values,
including malformed arguments, mapping errors and clock exhaustion. -/
theorem Workspace.after_call {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    (data : Workspace source) (routine : Code.Routine) (destination : Option (Option MlS))
    (arguments : List (ExpHOL 64)) (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source
      (.call (GlobalEffects.callInfo destination) (Code.name routine) arguments) = (result, post)) : Workspace post := by
  have kept (cursor : Cursor) : post.globals.lookup (key cursor) = source.globals.lookup (key cursor) := by
    have same := Effects.call_preserves cursor source.code data.code routine destination arguments source rfl
    rw [actual] at same
    exact congrArg Prod.snd same
  have fields := evaluation_fields source post _ result actual
  refine ⟨?_, fields.1.trans data.domain, fields.2.1.trans data.little,
    (kept .offsets).trans data.offsets, (kept .lengthChunk).trans data.chunk, (kept .zeroHashes).trans data.zeros,
    (kept .keccakState).trans data.keccakState,(kept .keccakPad).trans data.keccakPad,(kept .mptHash).trans data.mptHash,(kept .mptKey).trans data.mptKey,(kept .mptEmpty).trans data.mptEmpty,(kept .shaState).trans data.shaState,(kept .shaPad).trans data.shaPad,(kept .u256Ws).trans data.u256,
    data.chunkArena, data.zeroArena, data.chunkAligned, data.zeroAligned⟩
  rw [fields.2.2.2]
  exact data.code

end InitECandidate.Solver.Input.CurrentHash.WorkspaceEntry

#print axioms InitECandidate.Solver.Input.CurrentHash.WorkspaceEntry.Workspace.after_body
#print axioms InitECandidate.Solver.Input.CurrentHash.WorkspaceEntry.Workspace.after_call
