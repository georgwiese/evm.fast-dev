import InitECandidate.Solver.Headers.ValidateRoundTransport

namespace InitECandidate.Solver.Headers.Validate
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- A read-only actual phase may change locals/clock; supplying the real
five current loop bindings completes its transported invariant. -/
theorem RoundState.nonlocal (data : Data) (origin source target : PanSemStateFiniteExact 64 Guest.HostMemory) (index nextIndex : Nat)
    (state : RoundState data origin source index) (same : Input.LocalEffects.erase target=Input.LocalEffects.erase source)
    (arrayCell : target.locals.lookup (ofString "arr")=some (.val (.word data.array)))
    (countCell : target.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 data.count))))
    (hsCell : target.locals.lookup (ofString "hs")=some (.val (.word data.hs)))
    (hashesCell : target.locals.lookup (ofString "hashes")=some (.val (.word data.hashes)))
    (indexCell : target.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 nextIndex)))) : RoundState data origin target nextIndex := by
  have code:=congrArg PanSemStateFiniteExact.code same
  have exceptions:=congrArg PanSemStateFiniteExact.eshapes same
  have domain:=congrArg PanSemStateFiniteExact.memaddrs same
  have globals:=congrArg PanSemStateFiniteExact.globals same
  have oracle:=congrArg (fun state=>state.ffi.oracle) same
  change target.code=source.code at code
  change target.eshapes=source.eshapes at exceptions
  change target.memaddrs=source.memaddrs at domain
  change target.globals=source.globals at globals
  change target.ffi.oracle=source.ffi.oracle at oracle
  have memory:=Input.LocalEffects.memory_of_erase source target same
  have frame : Input.HashInput.Frame source target data.lower data.upper := ⟨by intro query lower upper; rw [memory]⟩
  refine ⟨by rw [code]; exact state.installed,by rw [exceptions]; exact state.shape,
    Rlp.Validation.Arena.of_fields source target data.cursor data.limit state.arena domain globals,
    Keccak256.Environment.of_fields source target data.stp data.pad state.environment domain code oracle (by intro key other; rw [globals]),
    state.input.trans origin source target _ _ frame,state.rows.of_frame source target _ _ _ _ _ _ frame,?_,arrayCell,countCell,hsCell,hashesCell,indexCell⟩
  obtain ⟨heap,cell,bounded,aligned,before⟩ := state.heap
  exact ⟨heap,by rw [globals]; exact cell,bounded,aligned,before⟩

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.RoundState.nonlocal
