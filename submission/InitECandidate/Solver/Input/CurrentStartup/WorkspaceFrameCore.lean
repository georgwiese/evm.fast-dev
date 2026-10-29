import InitECandidate.Solver.Input.CurrentStartup.OffsetsKeys
import InitECandidate.Solver.Input.GlobalEffectsCaught

namespace InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

inductive WorkspaceKey where | offsets | lengthChunk | zeroHashes | keccakState | keccakPad | shaState | shaPad | mptHash | mptKey | mptEmpty

def workspaceKey : WorkspaceKey → MlS
  | .offsets => ofString "ssz_offs"
  | .lengthChunk => ofString "ssz_len_chunk"
  | .zeroHashes => ofString "zero_hashes"
  | .keccakState => ofString "keccak_st"
  | .keccakPad => ofString "keccak_pad"
  | .mptHash => ofString "mpt_hash_scratch"
  | .mptKey => ofString "mpt_key_scratch"
  | .mptEmpty => ofString "empty_trie_root"
  | .shaState => ofString "sha_st"
  | .shaPad => ofString "sha_pad"

/-- Shared current-syntax frames, including the MPT buffer after its initializer. -/
def fromLegacy : OffsetsFrame.WorkspaceKey → WorkspaceKey
  | .offsets => .offsets
  | .lengthChunk => .lengthChunk
  | .zeroHashes => .zeroHashes
  | .keccakState => .keccakState
  | .keccakPad => .keccakPad
  | .shaState => .shaState
  | .shaPad => .shaPad

@[simp] theorem workspaceKey_fromLegacy (key : OffsetsFrame.WorkspaceKey) :
    workspaceKey (fromLegacy key) = OffsetsFrame.workspaceKey key := by
  cases key <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem trap_with (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .trap_with) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_trap_with, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.shared_store (workspaceKey workspace) code _ _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.shared_store (workspaceKey workspace) code _ _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.shared_store (workspaceKey workspace) code _ _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.external (workspaceKey workspace) code _ _ _ _ _)
  (GlobalEffects.raised (workspaceKey workspace) code _ _)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem alloc (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .alloc) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_alloc, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .trap_with) _ (Code.formals .trap_with) (Code.body .trap_with) (Code.shape .trap_with)
  (Code.installed code installed .trap_with) (trap_with code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .trap_with) _ (Code.formals .trap_with) (Code.body .trap_with) (Code.shape .trap_with)
  (Code.installed code installed .trap_with) (trap_with code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_other (workspaceKey workspace) code _ _ (by cases workspace <;> decide))
  (GlobalEffects.returned (workspaceKey workspace) code _))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem keccak_f1600 (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .keccak_f1600) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_keccak_f1600, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.loop (workspaceKey workspace) code _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.assign (workspaceKey workspace) code _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.returned (workspaceKey workspace) code _)))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem keccak_absorb_block (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .keccak_absorb_block) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_keccak_absorb_block, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.loop (workspaceKey workspace) code _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.assign (workspaceKey workspace) code _ _)))
  (GlobalEffects.loop (workspaceKey workspace) code _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.assign (workspaceKey workspace) code _ _))))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .keccak_f1600) _ (Code.formals .keccak_f1600) (Code.body .keccak_f1600) (Code.shape .keccak_f1600)
  (Code.installed code installed .keccak_f1600) (keccak_f1600 code installed workspace))
  (GlobalEffects.returned (workspaceKey workspace) code _))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem memcpy (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .memcpy) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_memcpy, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.loop (workspaceKey workspace) code _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.assign (workspaceKey workspace) code _ _))))))
  (GlobalEffects.loop (workspaceKey workspace) code _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.assign (workspaceKey workspace) code _ _))))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.loop (workspaceKey workspace) code _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.assign (workspaceKey workspace) code _ _))))))))))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.loop (workspaceKey workspace) code _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.assign (workspaceKey workspace) code _ _)))
  (GlobalEffects.returned (workspaceKey workspace) code _)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem memzero (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .memzero) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_memzero, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.loop (workspaceKey workspace) code _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.assign (workspaceKey workspace) code _ _))))))
  (GlobalEffects.loop (workspaceKey workspace) code _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.assign (workspaceKey workspace) code _ _))))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.loop (workspaceKey workspace) code _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.assign (workspaceKey workspace) code _ _))))))))))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.loop (workspaceKey workspace) code _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.assign (workspaceKey workspace) code _ _)))
  (GlobalEffects.returned (workspaceKey workspace) code _)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem keccak256 (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .keccak256) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_keccak256, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (memzero code installed workspace))
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.loop (workspaceKey workspace) code _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .keccak_absorb_block) _ (Code.formals .keccak_absorb_block) (Code.body .keccak_absorb_block) (Code.shape .keccak_absorb_block)
  (Code.installed code installed .keccak_absorb_block) (keccak_absorb_block code installed workspace))
  (GlobalEffects.assign (workspaceKey workspace) code _ _)))
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (memzero code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .memcpy) _ (Code.formals .memcpy) (Code.body .memcpy) (Code.shape .memcpy)
  (Code.installed code installed .memcpy) (memcpy code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .keccak_absorb_block) _ (Code.formals .keccak_absorb_block) (Code.body .keccak_absorb_block) (Code.shape .keccak_absorb_block)
  (Code.installed code installed .keccak_absorb_block) (keccak_absorb_block code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.store (workspaceKey workspace) code _ _))))
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .memcpy) _ (Code.formals .memcpy) (Code.body .memcpy) (Code.shape .memcpy)
  (Code.installed code installed .memcpy) (memcpy code installed workspace)))
  (GlobalEffects.returned (workspaceKey workspace) code _))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem u256_ws_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .u256_ws_init) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_u256_ws_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.returned (workspaceKey workspace) code _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem secp256k1_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .secp256k1_init) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_secp256k1_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.returned (workspaceKey workspace) code _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bn254_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .bn254_init) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_bn254_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.returned (workspaceKey workspace) code _)
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.returned (workspaceKey workspace) code _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bls_consts_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .bls_consts_init) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_bls_consts_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.returned (workspaceKey workspace) code _)
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.returned (workspaceKey workspace) code _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bls_lib_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .bls_lib_init) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_bls_lib_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .bls_consts_init) _ (Code.formals .bls_consts_init) (Code.body .bls_consts_init) (Code.shape .bls_consts_init)
  (Code.installed code installed .bls_consts_init) (bls_consts_init code installed workspace))
  (GlobalEffects.returned (workspaceKey workspace) code _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bls_precompiles_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .bls_precompiles_init) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_bls_precompiles_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.returned (workspaceKey workspace) code _)
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .bls_lib_init) _ (Code.formals .bls_lib_init) (Code.body .bls_lib_init) (Code.shape .bls_lib_init)
  (Code.installed code installed .bls_lib_init) (bls_lib_init code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.returned (workspaceKey workspace) code _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ripemd160_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .ripemd160_init) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_ripemd160_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.returned (workspaceKey workspace) code _)
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.returned (workspaceKey workspace) code _))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem blake2_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .blake2_init) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_blake2_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.returned (workspaceKey workspace) code _)
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.returned (workspaceKey workspace) code _)))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem header_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .header_init) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_header_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.returned (workspaceKey workspace) code _)
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (memzero code installed workspace))
  (GlobalEffects.returned (workspaceKey workspace) code _))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem heap_mark (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .heap_mark) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_heap_mark, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.returned (workspaceKey workspace) code _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem heap_release (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .heap_release) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_heap_release, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_other (workspaceKey workspace) code _ _ (by cases workspace <;> decide))
  (GlobalEffects.returned (workspaceKey workspace) code _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem evm_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .evm_init) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_evm_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .heap_mark) _ _ (Code.formals .heap_mark) (Code.body .heap_mark) (Code.shape .heap_mark)
  (Code.installed code installed .heap_mark) (heap_mark code installed workspace)
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed workspace)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .heap_release) _ (Code.formals .heap_release) (Code.body .heap_release) (Code.shape .heap_release)
  (Code.installed code installed .heap_release) (heap_release code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .keccak256) _ (Code.formals .keccak256) (Code.body .keccak256) (Code.shape .keccak256)
  (Code.installed code installed .keccak256) (keccak256 code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.loop (workspaceKey workspace) code _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.assign (workspaceKey workspace) code _ _)))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (memzero code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (memzero code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.returned (workspaceKey workspace) code _)))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem st_be32 (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .st_be32) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_st_be32, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.returned (workspaceKey workspace) code _)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bswap64 (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .bswap64) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_bswap64, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.returned (workspaceKey workspace) code _)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem st_be64 (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .st_be64) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_st_be64, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .bswap64) _ _ (Code.formals .bswap64) (Code.body .bswap64) (Code.shape .bswap64)
  (Code.installed code installed .bswap64) (bswap64 code installed workspace)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.returned (workspaceKey workspace) code _)))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .st_be32) _ (Code.formals .st_be32) (Code.body .st_be32) (Code.shape .st_be32)
  (Code.installed code installed .st_be32) (st_be32 code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .st_be32) _ (Code.formals .st_be32) (Code.body .st_be32) (Code.shape .st_be32)
  (Code.installed code installed .st_be32) (st_be32 code installed workspace))
  (GlobalEffects.returned (workspaceKey workspace) code _))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem addr_from_words (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .addr_from_words) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_addr_from_words, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .st_be32) _ (Code.formals .st_be32) (Code.body .st_be32) (Code.shape .st_be32)
  (Code.installed code installed .st_be32) (st_be32 code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (st_be64 code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (st_be64 code installed workspace))
  (GlobalEffects.returned (workspaceKey workspace) code _))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem fork_init (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .fork_init) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_fork_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (memzero code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (memzero code installed workspace))
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.loop (workspaceKey workspace) code _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.assign (workspaceKey workspace) code _ _)))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (addr_from_words code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (addr_from_words code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (addr_from_words code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (addr_from_words code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (addr_from_words code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (addr_from_words code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (addr_from_words code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.global_call_body (workspaceKey workspace) code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (by cases workspace <;> decide) (Code.installed code installed .alloc) (alloc code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (st_be64 code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (st_be64 code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (st_be64 code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (st_be64 code installed workspace))
  (GlobalEffects.returned (workspaceKey workspace) code _)))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ssz_fail (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .ssz_fail) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_ssz_fail, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.raised (workspaceKey workspace) code _ _)
  (GlobalEffects.returned (workspaceKey workspace) code _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ssz_split_var_list (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .ssz_split_var_list) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_ssz_split_var_list, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.returned (workspaceKey workspace) code _)
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed workspace)
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.loop (workspaceKey workspace) code _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.assign (workspaceKey workspace) code _ _)))))))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.returned (workspaceKey workspace) code _))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem decode_bytes_list (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .decode_bytes_list) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_decode_bytes_list, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .ssz_split_var_list) _ _ (Code.formals .ssz_split_var_list) (Code.body .ssz_split_var_list) (Code.shape .ssz_split_var_list)
  (Code.installed code installed .ssz_split_var_list) (ssz_split_var_list code installed workspace)
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.loop (workspaceKey workspace) code _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.assign (workspaceKey workspace) code _ _)))
  (GlobalEffects.returned (workspaceKey workspace) code _))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ssz_check_offsets (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .ssz_check_offsets) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_ssz_check_offsets, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.returned (workspaceKey workspace) code _)
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.loop (workspaceKey workspace) code _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.assign (workspaceKey workspace) code _ _)))))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.returned (workspaceKey workspace) code _)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem udivmod (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .udivmod) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_udivmod, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .trap_with) _ (Code.formals .trap_with) (Code.body .trap_with) (Code.shape .trap_with)
  (Code.installed code installed .trap_with) (trap_with code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.returned (workspaceKey workspace) code _)
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.loop (workspaceKey workspace) code _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.assign (workspaceKey workspace) code _ _))
  (GlobalEffects.skip (workspaceKey workspace) code)))))
  (GlobalEffects.returned (workspaceKey workspace) code _)))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ssz_fixed_list_count (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .ssz_fixed_list_count) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_ssz_fixed_list_count, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .udivmod) _ _ (Code.formals .udivmod) (Code.body .udivmod) (Code.shape .udivmod)
  (Code.installed code installed .udivmod) (udivmod code installed workspace)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.returned (workspaceKey workspace) code _))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem decode_payload (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .decode_payload) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_decode_payload, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed workspace)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_check_offsets) _ (Code.formals .ssz_check_offsets) (Code.body .ssz_check_offsets) (Code.shape .ssz_check_offsets)
  (Code.installed code installed .ssz_check_offsets) (ssz_check_offsets code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .ssz_split_var_list) _ _ (Code.formals .ssz_split_var_list) (Code.body .ssz_split_var_list) (Code.shape .ssz_split_var_list)
  (Code.installed code installed .ssz_split_var_list) (ssz_split_var_list code installed workspace)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .ssz_fixed_list_count) _ _ (Code.formals .ssz_fixed_list_count) (Code.body .ssz_fixed_list_count) (Code.shape .ssz_fixed_list_count)
  (Code.installed code installed .ssz_fixed_list_count) (ssz_fixed_list_count code installed workspace)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.returned (workspaceKey workspace) code _))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem decode_requests (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .decode_requests) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_decode_requests, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.loop (workspaceKey workspace) code _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.assign (workspaceKey workspace) code _ _)))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_check_offsets) _ (Code.formals .ssz_check_offsets) (Code.body .ssz_check_offsets) (Code.shape .ssz_check_offsets)
  (Code.installed code installed .ssz_check_offsets) (ssz_check_offsets code installed workspace))
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed workspace)
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .ssz_fixed_list_count) _ _ (Code.formals .ssz_fixed_list_count) (Code.body .ssz_fixed_list_count) (Code.shape .ssz_fixed_list_count)
  (Code.installed code installed .ssz_fixed_list_count) (ssz_fixed_list_count code installed workspace)
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .ssz_fixed_list_count) _ _ (Code.formals .ssz_fixed_list_count) (Code.body .ssz_fixed_list_count) (Code.shape .ssz_fixed_list_count)
  (Code.installed code installed .ssz_fixed_list_count) (ssz_fixed_list_count code installed workspace)
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .ssz_fixed_list_count) _ _ (Code.formals .ssz_fixed_list_count) (Code.body .ssz_fixed_list_count) (Code.shape .ssz_fixed_list_count)
  (Code.installed code installed .ssz_fixed_list_count) (ssz_fixed_list_count code installed workspace)
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .ssz_fixed_list_count) _ _ (Code.formals .ssz_fixed_list_count) (Code.body .ssz_fixed_list_count) (Code.shape .ssz_fixed_list_count)
  (Code.installed code installed .ssz_fixed_list_count) (ssz_fixed_list_count code installed workspace)
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .ssz_fixed_list_count) _ _ (Code.formals .ssz_fixed_list_count) (Code.body .ssz_fixed_list_count) (Code.shape .ssz_fixed_list_count)
  (Code.installed code installed .ssz_fixed_list_count) (ssz_fixed_list_count code installed workspace)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.returned (workspaceKey workspace) code _))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem decode_stateless_input (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .decode_stateless_input) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_decode_stateless_input, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.assign (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_check_offsets) _ (Code.formals .ssz_check_offsets) (Code.body .ssz_check_offsets) (Code.shape .ssz_check_offsets)
  (Code.installed code installed .ssz_check_offsets) (ssz_check_offsets code installed workspace))
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed workspace)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_check_offsets) _ (Code.formals .ssz_check_offsets) (Code.body .ssz_check_offsets) (Code.shape .ssz_check_offsets)
  (Code.installed code installed .ssz_check_offsets) (ssz_check_offsets code installed workspace))
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .decode_payload) _ _ (Code.formals .decode_payload) (Code.body .decode_payload) (Code.shape .decode_payload)
  (Code.installed code installed .decode_payload) (decode_payload code installed workspace)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .ssz_fixed_list_count) _ _ (Code.formals .ssz_fixed_list_count) (Code.body .ssz_fixed_list_count) (Code.shape .ssz_fixed_list_count)
  (Code.installed code installed .ssz_fixed_list_count) (ssz_fixed_list_count code installed workspace)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .decode_requests) _ _ (Code.formals .decode_requests) (Code.body .decode_requests) (Code.shape .decode_requests)
  (Code.installed code installed .decode_requests) (decode_requests code installed workspace)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.loop (workspaceKey workspace) code _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.assign (workspaceKey workspace) code _ _)))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_check_offsets) _ (Code.formals .ssz_check_offsets) (Code.body .ssz_check_offsets) (Code.shape .ssz_check_offsets)
  (Code.installed code installed .ssz_check_offsets) (ssz_check_offsets code installed workspace))
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .decode_bytes_list) _ _ (Code.formals .decode_bytes_list) (Code.body .decode_bytes_list) (Code.shape .decode_bytes_list)
  (Code.installed code installed .decode_bytes_list) (decode_bytes_list code installed workspace)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .decode_bytes_list) _ _ (Code.formals .decode_bytes_list) (Code.body .decode_bytes_list) (Code.shape .decode_bytes_list)
  (Code.installed code installed .decode_bytes_list) (decode_bytes_list code installed workspace)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .decode_bytes_list) _ _ (Code.formals .decode_bytes_list) (Code.body .decode_bytes_list) (Code.shape .decode_bytes_list)
  (Code.installed code installed .decode_bytes_list) (decode_bytes_list code installed workspace)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.returned (workspaceKey workspace) code _)))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem input_blob (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .input_blob) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_input_blob, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.shared_load (workspaceKey workspace) code _ _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .trap_with) _ (Code.formals .trap_with) (Code.body .trap_with) (Code.shape .trap_with)
  (Code.installed code installed .trap_with) (trap_with code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed workspace)
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.loop (workspaceKey workspace) code _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.shared_load (workspaceKey workspace) code _ _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.assign (workspaceKey workspace) code _ _))))
  (GlobalEffects.returned (workspaceKey workspace) code _))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem host_input_byte (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .host_input_byte) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_host_input_byte, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.shared_load (workspaceKey workspace) code _ _ _)
  (GlobalEffects.returned (workspaceKey workspace) code _)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem host_input_le32 (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .host_input_le32) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_host_input_le32, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .host_input_byte) _ _ (Code.formals .host_input_byte) (Code.body .host_input_byte) (Code.shape .host_input_byte)
  (Code.installed code installed .host_input_byte) (host_input_byte code installed workspace)
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .host_input_byte) _ _ (Code.formals .host_input_byte) (Code.body .host_input_byte) (Code.shape .host_input_byte)
  (Code.installed code installed .host_input_byte) (host_input_byte code installed workspace)
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .host_input_byte) _ _ (Code.formals .host_input_byte) (Code.body .host_input_byte) (Code.shape .host_input_byte)
  (Code.installed code installed .host_input_byte) (host_input_byte code installed workspace)
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .host_input_byte) _ _ (Code.formals .host_input_byte) (Code.body .host_input_byte) (Code.shape .host_input_byte)
  (Code.installed code installed .host_input_byte) (host_input_byte code installed workspace)
  (GlobalEffects.returned (workspaceKey workspace) code _)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem precheck_host_ssz_header (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .precheck_host_ssz_header) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_precheck_host_ssz_header, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.shared_load (workspaceKey workspace) code _ _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.returned (workspaceKey workspace) code _)
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .host_input_byte) _ _ (Code.formals .host_input_byte) (Code.body .host_input_byte) (Code.shape .host_input_byte)
  (Code.installed code installed .host_input_byte) (host_input_byte code installed workspace)
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .host_input_byte) _ _ (Code.formals .host_input_byte) (Code.body .host_input_byte) (Code.shape .host_input_byte)
  (Code.installed code installed .host_input_byte) (host_input_byte code installed workspace)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (host_input_le32 code installed workspace)
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (host_input_le32 code installed workspace)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_check_offsets) _ (Code.formals .ssz_check_offsets) (Code.body .ssz_check_offsets) (Code.shape .ssz_check_offsets)
  (Code.installed code installed .ssz_check_offsets) (ssz_check_offsets code installed workspace))
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (host_input_le32 code installed workspace)
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (host_input_le32 code installed workspace)
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (host_input_le32 code installed workspace)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_check_offsets) _ (Code.formals .ssz_check_offsets) (Code.body .ssz_check_offsets) (Code.shape .ssz_check_offsets)
  (Code.installed code installed .ssz_check_offsets) (ssz_check_offsets code installed workspace))
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.conditional (workspaceKey workspace) code _ _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_fail) _ (Code.formals .ssz_fail) (Code.body .ssz_fail) (Code.shape .ssz_fail)
  (Code.installed code installed .ssz_fail) (ssz_fail code installed workspace))
  (GlobalEffects.skip (workspaceKey workspace) code))
  (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (host_input_le32 code installed workspace)
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (host_input_le32 code installed workspace)
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (host_input_le32 code installed workspace)
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .host_input_le32) _ _ (Code.formals .host_input_le32) (Code.body .host_input_le32) (Code.shape .host_input_le32)
  (Code.installed code installed .host_input_le32) (host_input_le32 code installed workspace)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .ssz_check_offsets) _ (Code.formals .ssz_check_offsets) (Code.body .ssz_check_offsets) (Code.shape .ssz_check_offsets)
  (Code.installed code installed .ssz_check_offsets) (ssz_check_offsets code installed workspace))
  (GlobalEffects.returned (workspaceKey workspace) code _)))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem decode_host_input (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .decode_host_input) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_decode_host_input, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .precheck_host_ssz_header) _ (Code.formals .precheck_host_ssz_header) (Code.body .precheck_host_ssz_header) (Code.shape .precheck_host_ssz_header)
  (Code.installed code installed .precheck_host_ssz_header) (precheck_host_ssz_header code installed workspace))
  (GlobalEffects.scoped_body (workspaceKey workspace) code _ _ (Code.name .input_blob) _ _ (Code.formals .input_blob) (Code.body .input_blob) (Code.shape .input_blob)
  (Code.installed code installed .input_blob) (input_blob code installed workspace)
  (GlobalEffects.call_body (workspaceKey workspace) code none (Code.name .decode_stateless_input) _ (Code.formals .decode_stateless_input) (Code.body .decode_stateless_input) (Code.shape .decode_stateless_input)
  (Code.installed code installed .decode_stateless_input) (decode_stateless_input code installed workspace))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem st_le32 (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .st_le32) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_st_le32, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.returned (workspaceKey workspace) code _)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem st_le64 (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .st_le64) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_st_le64, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .st_le32) _ (Code.formals .st_le32) (Code.body .st_le32) (Code.shape .st_le32)
  (Code.installed code installed .st_le32) (st_le32 code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .st_le32) _ (Code.formals .st_le32) (Code.body .st_le32) (Code.shape .st_le32)
  (Code.installed code installed .st_le32) (st_le32 code installed workspace))
  (GlobalEffects.returned (workspaceKey workspace) code _)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem serialize_result (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .serialize_result) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_serialize_result, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .memcpy) _ (Code.formals .memcpy) (Code.body .memcpy) (Code.shape .memcpy)
  (Code.installed code installed .memcpy) (memcpy code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.call_body (workspaceKey workspace) code (some none) (Code.name .st_le64) _ (Code.formals .st_le64) (Code.body .st_le64) (Code.shape .st_le64)
  (Code.installed code installed .st_le64) (st_le64 code installed workspace))
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.byte_store (workspaceKey workspace) code _ _)
  (GlobalEffects.returned (workspaceKey workspace) code _))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem output_write (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .output_write) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_output_write, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (GlobalEffects.declared (workspaceKey workspace) code _ _ _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.loop (workspaceKey workspace) code _ _
  (GlobalEffects.sequence (workspaceKey workspace) code _ _
  (GlobalEffects.shared_store (workspaceKey workspace) code _ _ _)
  (GlobalEffects.assign (workspaceKey workspace) code _ _)))
  (GlobalEffects.returned (workspaceKey workspace) code _)))

end InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore

#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.trap_with
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.alloc
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.keccak_f1600
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.keccak_absorb_block
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.memcpy
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.memzero
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.keccak256
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.u256_ws_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.secp256k1_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.bn254_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.bls_consts_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.bls_lib_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.bls_precompiles_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.ripemd160_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.blake2_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.header_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.heap_mark
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.heap_release
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.evm_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.st_be32
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.bswap64
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.st_be64
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.addr_from_words
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.fork_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.ssz_fail
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.ssz_split_var_list
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.decode_bytes_list
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.ssz_check_offsets
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.udivmod
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.ssz_fixed_list_count
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.decode_payload
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.decode_requests
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.decode_stateless_input
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.input_blob
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.host_input_byte
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.host_input_le32
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.precheck_host_ssz_header
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.decode_host_input
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.st_le32
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.st_le64
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.serialize_result
#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.output_write
