import InitECandidate.Solver.Headers.ValidateRound

namespace InitECandidate.Solver.Headers.Validate
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Transport current loop data through actual nonlocal metadata equality
and agreement on its fixed input region. Memory outside that region and
the evaluator clock may change. -/
theorem RoundState.transport (data : Data) (origin source target : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index)
    (code : target.code=source.code) (exceptions : target.eshapes=source.eshapes)
    (domain : target.memaddrs=source.memaddrs) (oracle : target.ffi.oracle=source.ffi.oracle)
    (globals : target.globals=source.globals) (locals : target.locals=source.locals)
    (frame : Input.HashInput.Frame source target data.lower data.upper) : RoundState data origin target index := by
  refine ⟨by rw [code]; exact state.installed,by rw [exceptions]; exact state.shape,
    Rlp.Validation.Arena.of_fields source target data.cursor data.limit state.arena domain globals,
    Keccak256.Environment.of_fields source target data.stp data.pad state.environment domain code oracle (by intro key other; rw [globals]),
    state.input.trans origin source target data.lower data.upper frame,
    state.rows.of_frame source target data.array data.pointers data.lengths data.count data.lower data.upper frame,?_,?_,?_,?_,?_,?_,?_⟩
  · obtain ⟨pointer,cell,bounded,aligned,before⟩ := state.heap
    exact ⟨pointer,by rw [globals]; exact cell,bounded,aligned,before⟩
  · rw [locals]; exact state.arrayCell
  · rw [locals]; exact state.countCell
  · rw [locals]; exact state.hsCell
  · rw [locals]; exact state.hashesCell
  · rw [locals]; exact state.indexCell
  · intro key other
    rw [globals]
    exact state.globals key other

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.RoundState.transport
