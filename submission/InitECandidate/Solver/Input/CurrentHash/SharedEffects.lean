import InitECandidate.Solver.Input.CurrentHash.Base
import InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame
import InitECandidate.Solver.Input.CurrentStartup.TrapWith
import InitECandidate.Solver.Input.CurrentStartup.Alloc
import InitECandidate.Solver.Input.CurrentStartup.HeapMark
import InitECandidate.Solver.Input.CurrentStartup.HeapRelease
import InitECandidate.Solver.Input.CurrentStartup.Memcpy
import InitECandidate.Solver.Input.CurrentStartup.Memzero
import InitECandidate.Solver.Input.CurrentStartup.StLe32
import InitECandidate.Solver.Input.CurrentStartup.StLe64

namespace InitECandidate.Solver.Input.CurrentHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace SharedEffects

namespace TrapWith
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .trap_with) := by
  cases cursor with
  | scratch => exact CurrentStartup.TrapWith.preserves .scratch code installed
  | frame => exact CurrentStartup.TrapWith.preserves .frame code installed
  | offsets => exact CurrentStartup.OffsetsFrame.trap_with code installed .offsets
  | lengthChunk => exact CurrentStartup.OffsetsFrame.trap_with code installed .lengthChunk
  | zeroHashes => exact CurrentStartup.OffsetsFrame.trap_with code installed .zeroHashes
  | keccakState => exact CurrentStartup.OffsetsFrame.trap_with code installed .keccakState
  | keccakPad => exact CurrentStartup.OffsetsFrame.trap_with code installed .keccakPad
  | mptHash => exact CurrentStartup.WorkspaceFrameCore.trap_with code installed .mptHash
  | mptKey => exact CurrentStartup.WorkspaceFrameCore.trap_with code installed .mptKey
  | mptEmpty => exact CurrentStartup.WorkspaceFrameCore.trap_with code installed .mptEmpty
  | shaState => exact CurrentStartup.WorkspaceFrameCore.trap_with code installed .shaState
  | shaPad => exact CurrentStartup.WorkspaceFrameCore.trap_with code installed .shaPad
  | u256Ws => exact CurrentStartup.WorkspaceFrameCore.trap_with code installed .u256Ws
end TrapWith

namespace Alloc
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .alloc) := by
  cases cursor with
  | scratch => exact CurrentStartup.Alloc.preserves .scratch code installed
  | frame => exact CurrentStartup.Alloc.preserves .frame code installed
  | offsets => exact CurrentStartup.OffsetsFrame.alloc code installed .offsets
  | lengthChunk => exact CurrentStartup.OffsetsFrame.alloc code installed .lengthChunk
  | zeroHashes => exact CurrentStartup.OffsetsFrame.alloc code installed .zeroHashes
  | keccakState => exact CurrentStartup.OffsetsFrame.alloc code installed .keccakState
  | keccakPad => exact CurrentStartup.OffsetsFrame.alloc code installed .keccakPad
  | mptHash => exact CurrentStartup.WorkspaceFrameCore.alloc code installed .mptHash
  | mptKey => exact CurrentStartup.WorkspaceFrameCore.alloc code installed .mptKey
  | mptEmpty => exact CurrentStartup.WorkspaceFrameCore.alloc code installed .mptEmpty
  | shaState => exact CurrentStartup.WorkspaceFrameCore.alloc code installed .shaState
  | shaPad => exact CurrentStartup.WorkspaceFrameCore.alloc code installed .shaPad
  | u256Ws => exact CurrentStartup.WorkspaceFrameCore.alloc code installed .u256Ws
end Alloc

namespace HeapMark
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .heap_mark) := by
  cases cursor with
  | scratch => exact CurrentStartup.HeapMark.preserves .scratch code installed
  | frame => exact CurrentStartup.HeapMark.preserves .frame code installed
  | offsets => exact CurrentStartup.OffsetsFrame.heap_mark code installed .offsets
  | lengthChunk => exact CurrentStartup.OffsetsFrame.heap_mark code installed .lengthChunk
  | zeroHashes => exact CurrentStartup.OffsetsFrame.heap_mark code installed .zeroHashes
  | keccakState => exact CurrentStartup.OffsetsFrame.heap_mark code installed .keccakState
  | keccakPad => exact CurrentStartup.OffsetsFrame.heap_mark code installed .keccakPad
  | mptHash => exact CurrentStartup.WorkspaceFrameCore.heap_mark code installed .mptHash
  | mptKey => exact CurrentStartup.WorkspaceFrameCore.heap_mark code installed .mptKey
  | mptEmpty => exact CurrentStartup.WorkspaceFrameCore.heap_mark code installed .mptEmpty
  | shaState => exact CurrentStartup.WorkspaceFrameCore.heap_mark code installed .shaState
  | shaPad => exact CurrentStartup.WorkspaceFrameCore.heap_mark code installed .shaPad
  | u256Ws => exact CurrentStartup.WorkspaceFrameCore.heap_mark code installed .u256Ws
end HeapMark

namespace HeapRelease
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .heap_release) := by
  cases cursor with
  | scratch => exact CurrentStartup.HeapRelease.preserves .scratch code installed
  | frame => exact CurrentStartup.HeapRelease.preserves .frame code installed
  | offsets => exact CurrentStartup.OffsetsFrame.heap_release code installed .offsets
  | lengthChunk => exact CurrentStartup.OffsetsFrame.heap_release code installed .lengthChunk
  | zeroHashes => exact CurrentStartup.OffsetsFrame.heap_release code installed .zeroHashes
  | keccakState => exact CurrentStartup.OffsetsFrame.heap_release code installed .keccakState
  | keccakPad => exact CurrentStartup.OffsetsFrame.heap_release code installed .keccakPad
  | mptHash => exact CurrentStartup.WorkspaceFrameCore.heap_release code installed .mptHash
  | mptKey => exact CurrentStartup.WorkspaceFrameCore.heap_release code installed .mptKey
  | mptEmpty => exact CurrentStartup.WorkspaceFrameCore.heap_release code installed .mptEmpty
  | shaState => exact CurrentStartup.WorkspaceFrameCore.heap_release code installed .shaState
  | shaPad => exact CurrentStartup.WorkspaceFrameCore.heap_release code installed .shaPad
  | u256Ws => exact CurrentStartup.WorkspaceFrameCore.heap_release code installed .u256Ws
end HeapRelease

namespace Memcpy
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .memcpy) := by
  cases cursor with
  | scratch => exact CurrentStartup.Memcpy.preserves .scratch code installed
  | frame => exact CurrentStartup.Memcpy.preserves .frame code installed
  | offsets => exact CurrentStartup.OffsetsFrame.memcpy code installed .offsets
  | lengthChunk => exact CurrentStartup.OffsetsFrame.memcpy code installed .lengthChunk
  | zeroHashes => exact CurrentStartup.OffsetsFrame.memcpy code installed .zeroHashes
  | keccakState => exact CurrentStartup.OffsetsFrame.memcpy code installed .keccakState
  | keccakPad => exact CurrentStartup.OffsetsFrame.memcpy code installed .keccakPad
  | mptHash => exact CurrentStartup.WorkspaceFrameCore.memcpy code installed .mptHash
  | mptKey => exact CurrentStartup.WorkspaceFrameCore.memcpy code installed .mptKey
  | mptEmpty => exact CurrentStartup.WorkspaceFrameCore.memcpy code installed .mptEmpty
  | shaState => exact CurrentStartup.WorkspaceFrameCore.memcpy code installed .shaState
  | shaPad => exact CurrentStartup.WorkspaceFrameCore.memcpy code installed .shaPad
  | u256Ws => exact CurrentStartup.WorkspaceFrameCore.memcpy code installed .u256Ws
end Memcpy

namespace Memzero
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .memzero) := by
  cases cursor with
  | scratch => exact CurrentStartup.Memzero.preserves .scratch code installed
  | frame => exact CurrentStartup.Memzero.preserves .frame code installed
  | offsets => exact CurrentStartup.OffsetsFrame.memzero code installed .offsets
  | lengthChunk => exact CurrentStartup.OffsetsFrame.memzero code installed .lengthChunk
  | zeroHashes => exact CurrentStartup.OffsetsFrame.memzero code installed .zeroHashes
  | keccakState => exact CurrentStartup.OffsetsFrame.memzero code installed .keccakState
  | keccakPad => exact CurrentStartup.OffsetsFrame.memzero code installed .keccakPad
  | mptHash => exact CurrentStartup.WorkspaceFrameCore.memzero code installed .mptHash
  | mptKey => exact CurrentStartup.WorkspaceFrameCore.memzero code installed .mptKey
  | mptEmpty => exact CurrentStartup.WorkspaceFrameCore.memzero code installed .mptEmpty
  | shaState => exact CurrentStartup.WorkspaceFrameCore.memzero code installed .shaState
  | shaPad => exact CurrentStartup.WorkspaceFrameCore.memzero code installed .shaPad
  | u256Ws => exact CurrentStartup.WorkspaceFrameCore.memzero code installed .u256Ws
end Memzero

namespace StLe32
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .st_le32) := by
  cases cursor with
  | scratch => exact CurrentStartup.StLe32.preserves .scratch code installed
  | frame => exact CurrentStartup.StLe32.preserves .frame code installed
  | offsets => exact CurrentStartup.OffsetsFrame.st_le32 code installed .offsets
  | lengthChunk => exact CurrentStartup.OffsetsFrame.st_le32 code installed .lengthChunk
  | zeroHashes => exact CurrentStartup.OffsetsFrame.st_le32 code installed .zeroHashes
  | keccakState => exact CurrentStartup.OffsetsFrame.st_le32 code installed .keccakState
  | keccakPad => exact CurrentStartup.OffsetsFrame.st_le32 code installed .keccakPad
  | mptHash => exact CurrentStartup.WorkspaceFrameCore.st_le32 code installed .mptHash
  | mptKey => exact CurrentStartup.WorkspaceFrameCore.st_le32 code installed .mptKey
  | mptEmpty => exact CurrentStartup.WorkspaceFrameCore.st_le32 code installed .mptEmpty
  | shaState => exact CurrentStartup.WorkspaceFrameCore.st_le32 code installed .shaState
  | shaPad => exact CurrentStartup.WorkspaceFrameCore.st_le32 code installed .shaPad
  | u256Ws => exact CurrentStartup.WorkspaceFrameCore.st_le32 code installed .u256Ws
end StLe32

namespace StLe64
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .st_le64) := by
  cases cursor with
  | scratch => exact CurrentStartup.StLe64.preserves .scratch code installed
  | frame => exact CurrentStartup.StLe64.preserves .frame code installed
  | offsets => exact CurrentStartup.OffsetsFrame.st_le64 code installed .offsets
  | lengthChunk => exact CurrentStartup.OffsetsFrame.st_le64 code installed .lengthChunk
  | zeroHashes => exact CurrentStartup.OffsetsFrame.st_le64 code installed .zeroHashes
  | keccakState => exact CurrentStartup.OffsetsFrame.st_le64 code installed .keccakState
  | keccakPad => exact CurrentStartup.OffsetsFrame.st_le64 code installed .keccakPad
  | mptHash => exact CurrentStartup.WorkspaceFrameCore.st_le64 code installed .mptHash
  | mptKey => exact CurrentStartup.WorkspaceFrameCore.st_le64 code installed .mptKey
  | mptEmpty => exact CurrentStartup.WorkspaceFrameCore.st_le64 code installed .mptEmpty
  | shaState => exact CurrentStartup.WorkspaceFrameCore.st_le64 code installed .shaState
  | shaPad => exact CurrentStartup.WorkspaceFrameCore.st_le64 code installed .shaPad
  | u256Ws => exact CurrentStartup.WorkspaceFrameCore.st_le64 code installed .u256Ws
end StLe64

end SharedEffects
end InitECandidate.Solver.Input.CurrentHash

#print axioms InitECandidate.Solver.Input.CurrentHash.SharedEffects.TrapWith.preserves

#print axioms InitECandidate.Solver.Input.CurrentHash.SharedEffects.Alloc.preserves

#print axioms InitECandidate.Solver.Input.CurrentHash.SharedEffects.HeapMark.preserves

#print axioms InitECandidate.Solver.Input.CurrentHash.SharedEffects.HeapRelease.preserves

#print axioms InitECandidate.Solver.Input.CurrentHash.SharedEffects.Memcpy.preserves

#print axioms InitECandidate.Solver.Input.CurrentHash.SharedEffects.Memzero.preserves

#print axioms InitECandidate.Solver.Input.CurrentHash.SharedEffects.StLe32.preserves

#print axioms InitECandidate.Solver.Input.CurrentHash.SharedEffects.StLe64.preserves
