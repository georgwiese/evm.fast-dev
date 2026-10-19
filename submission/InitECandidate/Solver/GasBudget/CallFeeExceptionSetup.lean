import InitECandidate.Solver.GasBudget.CallAccessFee
import InitECandidate.Solver.Input.ExceptionWordDeclaration

namespace InitECandidate.Solver.GasBudget.CallAccessFee
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem setup_exception (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (warm : BitVec 64)
    (continuation : ProgHOL 64) (identifier : MlS) (payload : ValueHOL 64)
    (warmLocal : source.locals.lookup (ofString "warm") = some (.val (.word warm)))
    (run : evaluateHOLFiniteState source (program continuation) = (some (.exception identifier payload), post)) :
    ∃ ready inner, emptyLocalsHOLFinite ready = emptyLocalsHOLFinite source ∧
      ready.locals.lookup (ofString "access_cost") = some (.val (.word (resultWord warm))) ∧
      (∀ key : String, ofString "access_cost" ≠ ofString key → ready.locals.lookup (ofString key) = source.locals.lookup (ofString key)) ∧
      evaluateHOLFiniteState ready continuation = (some (.exception identifier payload), inner) ∧ post = restore source "access_cost" inner := by
  obtain ⟨inner, declaredRun, scope⟩ := Input.declaration_exception_word source post "access_cost" (.const 100#64) 100#64 (.seq update continuation) identifier payload rfl run
  let initial := bind source "access_cost" 100#64
  have warmI : initial.locals.lookup (ofString "warm") = some (.val (.word warm)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans warmLocal
  obtain ⟨ready, updateRun, canonical, accessCell, other⟩ := update_execute initial warm warmI (bind_lookup_same _ _ _)
  have fields := congrArg emptyLocalsHOLFinite canonical
  change emptyLocalsHOLFinite ready = emptyLocalsHOLFinite source at fields
  have clock := congrArg PanSemStateFiniteExact.clock canonical
  change ready.clock = initial.clock at clock
  rw [WitnessRadix.StateSteps.next_sequence initial ready update continuation updateRun (by omega)] at declaredRun
  refine ⟨ready, inner, fields, accessCell, ?_, declaredRun, scope⟩
  intro key different
  exact (other key different).trans (bind_lookup_other _ _ _ _ different)

end InitECandidate.Solver.GasBudget.CallAccessFee

namespace InitECandidate.Solver.GasBudget.CallValueFee
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem setup_exception (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (access memoryCost expand : BitVec 64) (words : U256Zero.Quad) (continuation : ProgHOL 64) (identifier : MlS) (payload : ValueHOL 64)
    (vz : source.locals.lookup (ofString "vz") = some (.val (.word (U256Zero.resultWord words))))
    (accessCell : source.locals.lookup (ofString "access_cost") = some (.val (.word access)))
    (xCell : source.locals.lookup (ofString "x") = some (.rStruct [.val (.word memoryCost), .val (.word expand)]))
    (run : evaluateHOLFiniteState source (withTransfer continuation) = (some (.exception identifier payload), post)) :
    ∃ ready inner, emptyLocalsHOLFinite ready = emptyLocalsHOLFinite source ∧
      ready.locals.lookup (ofString "access_cost") = some (.val (.word access)) ∧
      ready.locals.lookup (ofString "transfer_cost") = some (.val (.word (ForwardCredit.valueFee words))) ∧
      ready.locals.lookup (ofString "x") = some (.rStruct [.val (.word memoryCost), .val (.word expand)]) ∧
      evaluateHOLFiniteState ready (program continuation) = (some (.exception identifier payload), inner) ∧
      post = restore source "transfer_cost" inner := by
  obtain ⟨inner, declaredRun, scope⟩ := Input.declaration_exception_word source post "transfer_cost" (.const 0#64) 0#64
    (.seq transferUpdate (program continuation)) identifier payload rfl run
  let initial := bind source "transfer_cost" 0#64
  have initialVZ : initial.locals.lookup (ofString "vz") = some (.val (.word (U256Zero.resultWord words))) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans vz
  obtain ⟨ready, updateRun, canonical, transferCell, other⟩ := transfer_execute initial words initialVZ (bind_lookup_same _ _ _)
  have fields := congrArg emptyLocalsHOLFinite canonical
  change emptyLocalsHOLFinite ready = emptyLocalsHOLFinite source at fields
  have clock := congrArg PanSemStateFiniteExact.clock canonical
  change ready.clock = initial.clock at clock
  rw [WitnessRadix.StateSteps.next_sequence initial ready transferUpdate (program continuation) updateRun (by omega)] at declaredRun
  exact ⟨ready, inner, fields,
    (other "access_cost" (by decide)).trans ((bind_lookup_other _ _ _ _ (by decide)).trans accessCell), transferCell,
    (other "x" (by decide)).trans ((bind_lookup_other _ _ _ _ (by decide)).trans xCell), declaredRun, scope⟩

end InitECandidate.Solver.GasBudget.CallValueFee

#print axioms InitECandidate.Solver.GasBudget.CallAccessFee.setup_exception
#print axioms InitECandidate.Solver.GasBudget.CallValueFee.setup_exception
