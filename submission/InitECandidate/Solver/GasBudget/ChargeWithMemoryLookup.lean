import InitECandidate.Solver.GasBudget.ChargeWithMemoryProgram

namespace InitECandidate.Solver.GasBudget.ChargeWithMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual literal base argument and successful original lookup derive
the real callee's base binding, even when start/size originate in real pops. -/
theorem lookup_base (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (start size : ExpHOL 64) (installed : Input.OriginalCode.Installed source.code)
    (values : List (ValueHOL 64))
    (arguments : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [.const base, start, size] = some values)
    (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "charge_with_memory") values = some (actual, callee, returnShape)) :
    callee.lookup (ofString "base") = some (.val (.word base)) := by
  have code := original_code source.code installed
  have raw := lookupCodeHOLFinite_eq_some source.code.lookup (ofString "charge_with_memory") values actual callee returnShape called
  simp only [lookupCodeHOLExact, code] at raw
  split at raw
  · rename_i valid
    have length := valid.2.1
    cases values with
    | nil => simp at length
    | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest =>
        cases rest with
        | nil => simp at length
        | cons third rest =>
          cases rest with
          | cons head tail => simp at length
          | nil =>
            have firstEq : first = .val (.word base) :=
              Input.ArgumentValues.head_of_list source (.const base) [start, size] (.val (.word base)) first [second, third] rfl arguments
            have same := Option.some.inj raw
            have baseEq := congrArg (fun triple : ProgHOL 64 × (MlS → Option (ValueHOL 64)) × ShapeHOL => triple.2.1 (ofString "base")) same
            have cell : callee.lookup (ofString "base") = some first := by
              simpa [show ofString "base" ≠ ofString "start" from by decide,
                show ofString "base" ≠ ofString "size" from by decide] using baseEq.symm
            exact cell.trans (congrArg some firstEq)
  · cases raw

end InitECandidate.Solver.GasBudget.ChargeWithMemory

#print axioms InitECandidate.Solver.GasBudget.ChargeWithMemory.lookup_base
