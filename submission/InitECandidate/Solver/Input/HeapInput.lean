import InitECandidate.Solver.Input.Framing
import InitECandidate.Solver.Input.PureReturn

namespace InitECandidate.Solver.Input.Blob
open Flapjack PanSemStateFiniteExact

/-- Exact byte correspondence over the encoded input extent. This does not
replace the encoded extent with the arbitrary mathematical list's length. -/
def HeapInput (state : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64) : Prop :=
  ∀ offset<input.length%2^64,
    @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address=>Classical.propDecidable (state.memaddrs address)) state.be
      (pointer+BitVec.ofNat 64 offset)=some (Framing.convert ((input[offset]?).getD 0))

end InitECandidate.Solver.Input.Blob
