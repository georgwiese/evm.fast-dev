import InitECandidate.Solver.Input.CurrentStartup.Base

namespace InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

inductive WorkspaceKey where | offsets | lengthChunk | zeroHashes | keccakState | keccakPad

def workspaceKey : WorkspaceKey → MlS
  | .offsets => ofString "ssz_offs"
  | .lengthChunk => ofString "ssz_len_chunk"
  | .zeroHashes => ofString "zero_hashes"
  | .keccakState => ofString "keccak_st"
  | .keccakPad => ofString "keccak_pad"

end InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame
