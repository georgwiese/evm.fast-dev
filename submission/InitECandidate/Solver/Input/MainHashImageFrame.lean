import InitECandidate.Solver.Input.MainHashFields

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem RequestHashImage.of_memory (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (memory : target.memory=source.memory) (actual : RequestHashImage input source) : RequestHashImage input target := by
  constructor
  · rw [memory]; exact actual.payload
  · rw [memory]; exact actual.hashes
  · rw [memory]; exact actual.count
  · rw [memory]; exact actual.parent
  · exact actual.partition

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.RequestHashImage.of_memory
