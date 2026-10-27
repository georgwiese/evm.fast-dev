import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A particular normally returned stateless decoder execution, selected by
its caller rather than replaced by an unrelated existential execution. -/
structure DecoderOrigin where
  entry : PanSemStateFiniteExact 64 Guest.HostMemory
  post : PanSemStateFiniteExact 64 Guest.HostMemory
  pointer : BitVec 64
  word : BitVec 64

/-- A suffix ends with the same original physical observation and value. -/
structure DecoderOrigin.Frame (origin : DecoderOrigin) (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer : BitVec 64) (value : ValueHOL 64) : Prop where
  pointer : pointer = origin.pointer
  value : value = .val (.word origin.word)
  state : LocalEffects.erase post = LocalEffects.erase origin.post
  clock : post.clock = origin.post.clock

theorem DecoderOrigin.Frame.of_frame {origin : DecoderOrigin} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer : BitVec 64} {value : ValueHOL 64} (actual : origin.Frame source pointer value)
    (state : LocalEffects.erase target = LocalEffects.erase source) (clock : target.clock = source.clock) :
    origin.Frame target pointer value :=
  ⟨actual.pointer, actual.value, state.trans actual.state, clock.trans actual.clock⟩

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderOrigin.Frame.of_frame
