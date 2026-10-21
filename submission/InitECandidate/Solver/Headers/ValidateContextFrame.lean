import InitECandidate.Solver.Headers.ValidateCallTrace

namespace InitECandidate.Solver.Headers.Validate
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Reachable wrapper declarations/calls may replace locals and spend clock.
The validator context depends on physical memory and runtime metadata only. -/
theorem Context.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count cursor limit stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper budget : Nat)
    (context : Context source array heap count cursor limit stp pad pointers lengths lower upper budget)
    (code : target.code=source.code) (exceptions : target.eshapes=source.eshapes)
    (domain : target.memaddrs=source.memaddrs) (oracle : target.ffi.oracle=source.ffi.oracle)
    (globals : target.globals=source.globals) (frame : Input.HashInput.Frame source target lower upper) :
    Context target array heap count cursor limit stp pad pointers lengths lower upper budget := by
  refine ⟨by rw [code]; exact context.installed,by rw [exceptions]; exact context.shape,
    Rlp.Validation.Arena.of_fields source target cursor limit context.arena domain globals,
    Keccak256.Environment.of_fields source target stp pad context.environment domain code oracle (by intro key other; rw [globals]),
    context.rows.of_frame source target array pointers lengths count.toNat lower upper frame,?_,context.heapLower,context.heapBound,context.heapAligned,context.before,
    context.stateArena,context.stateAligned,context.padArena,context.padAligned,context.stateBefore,context.padBefore,context.aligned,context.inputLower,context.scratchBefore,context.byteBudget⟩
  rw [globals]
  exact context.heapCell

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.Context.of_fields
