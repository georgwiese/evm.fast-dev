import InitECandidate.Solver.Input.CurrentHash.Code
import InitECandidate.Solver.Input.CurrentStartup.Base

namespace InitECandidate.Solver.Input.CurrentHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Fixed globals retained by the actual request-hash closure on every outcome. -/
inductive Cursor where | scratch | frame | offsets | lengthChunk | zeroHashes | keccakState | keccakPad

def key : Cursor → MlS
  | .scratch => ofString "scratch_ptr"
  | .frame => ofString "frame_mem_ptr"
  | .offsets => ofString "ssz_offs"
  | .lengthChunk => ofString "ssz_len_chunk"
  | .zeroHashes => ofString "zero_hashes"
  | .keccakState => ofString "keccak_st"
  | .keccakPad => ofString "keccak_pad"

end InitECandidate.Solver.Input.CurrentHash
