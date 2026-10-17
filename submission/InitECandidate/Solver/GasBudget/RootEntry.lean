import InitECandidate.Solver.GasBudget.RootValidationCall

namespace InitECandidate.Solver.GasBudget.RootBudget
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual normal validator call supplies the intrinsic premise. At the
later real min split, derive the liquid cap and exact execution/scoping from
that caller predicate and actual gas/code/local entries. -/
theorem initialize_validated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (gas intrinsic : BitVec 64)
    (capped : RootValidation.CappedIntrinsic source)
    (gasLocal : source.locals.lookup (ofString "gas") = some (.val (.word gas)))
    (totalLocal : source.locals.lookup (ofString "intrinsic_gas") = some (.val (.word intrinsic)))
    (code : source.code.lookup (ofString "min") = some (Minimum.formals, Minimum.body, .one))
    (enough : 1 ≤ source.clock) :
    ∃ regular state floor : BitVec 64,
      floor.toNat ≤ 16777216 ∧
      (liquidWord gas intrinsic regular).toNat + regular.toNat ≤ 16777216 ∧
      (entered source gas intrinsic regular).locals.lookup (ofString "mgas") =
        some (.val (.word (liquidWord gas intrinsic regular))) ∧
      (entered source gas intrinsic regular).locals.lookup (ofString "reservoir") =
        some (.val (.word (reservoirWord gas intrinsic regular))) ∧
      (entered source gas intrinsic regular).clock = source.clock - 1 ∧
      (entered source gas intrinsic regular).memory = source.memory ∧
      (entered source gas intrinsic regular).globals = source.globals ∧
      (∀ continuation, evaluateHOLFiniteState source (program continuation) =
        (let output := evaluateHOLFiniteState (entered source gas intrinsic regular) continuation
         (output.1, closeScope source gas intrinsic regular output.2))) ∧
      source.locals.lookup (ofString "intrinsic") = some (intrinsicValue regular state floor) := by
  obtain ⟨regular, state, floor, stored, regularCap, floorCap⟩ := capped
  have fields := entered_fields source gas intrinsic regular
  exact ⟨regular, state, floor, floorCap, liquid_bound gas intrinsic regular regularCap,
    fields.2.2.2.2.1, fields.2.2.2.2.2, fields.2.2.2.1, fields.1, fields.2.1,
    fun continuation => execute source gas intrinsic regular state floor gasLocal totalLocal stored code enough continuation, stored⟩

end InitECandidate.Solver.GasBudget.RootBudget

#print axioms InitECandidate.Solver.GasBudget.RootBudget.initialize_validated
