import InitECandidate.Solver.Headers.CurrentValidate.Round

namespace InitECandidate.Solver.Headers.CurrentValidate
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix

/-- A real nonlocal frame retains all physical current data. Only the
listed actual next caller bindings must be established separately. -/
theorem RoundState.nonlocal (data : Data) (origin source target : PanSemStateFiniteExact 64 Guest.HostMemory) (index next : Nat)
    (state : RoundState data origin source index) (same : LocalEffects.erase target=LocalEffects.erase source)
    (arrayCell : target.locals.lookup (ofString "arr")=some (.val (.word data.array)))
    (countCell : target.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 data.count))))
    (hsCell : target.locals.lookup (ofString "hs")=some (.val (.word data.hs)))
    (hashesCell : target.locals.lookup (ofString "hashes")=some (.val (.word data.hashes)))
    (indexCell : target.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 next)))) : RoundState data origin target next := by
  have globals:=congrArg PanSemStateFiniteExact.globals same
  change target.globals=source.globals at globals
  have frame : HashInput.Frame source target data.lower data.upper := ⟨fun query _ _=>congrFun (LocalEffects.memory_of_erase source target same) query⟩
  refine ⟨state.arena.of_frame same,state.environment.of_frame same,state.input.trans origin source target _ _ frame,
    state.rows.of_frame source target _ _ _ _ _ _ frame,?_,arrayCell,countCell,hsCell,hashesCell,indexCell,?_⟩
  · rw [globals]
    exact state.heap
  · intro key different
    rw [globals]
    exact state.globals key different

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.RoundState.nonlocal
