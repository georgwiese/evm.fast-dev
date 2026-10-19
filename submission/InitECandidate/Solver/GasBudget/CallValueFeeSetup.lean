import InitECandidate.Solver.GasBudget.CallValueFee
import InitECandidate.Solver.Input.NormalWordDeclaration

namespace InitECandidate.Solver.GasBudget.CallValueFee
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def transferUpdate : ProgHOL 64 := .ite (.cmp .equal (localVar "vz") (.const 0#64))
  (.assign .local (ofString "transfer_cost") (.const 11300#64)) .skip
def withTransfer (continuation : ProgHOL 64) : ProgHOL 64 :=
  .dec (ofString "transfer_cost") .one (.const 0#64) (.seq transferUpdate (program continuation))

theorem transfer_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Zero.Quad)
    (vz : source.locals.lookup (ofString "vz") = some (.val (.word (U256Zero.resultWord words))))
    (initial : source.locals.lookup (ofString "transfer_cost") = some (.val (.word 0#64))) :
    ∃ target, evaluateHOLFiniteState source transferUpdate = (none, target) ∧
      target = {source with locals := target.locals} ∧
      target.locals.lookup (ofString "transfer_cost") = some (.val (.word (ForwardCredit.valueFee words))) ∧
      (∀ key : String, ofString "transfer_cost" ≠ ofString key → target.locals.lookup (ofString key) = source.locals.lookup (ofString key)) := by
  by_cases nonzero : U256Zero.resultWord words = 0#64
  · let target := bind source "transfer_cost" 11300#64
    have assigned := WitnessRadix.StateSteps.assign_execute source "transfer_cost" (.const 11300#64) 0#64 11300#64 initial rfl
    refine ⟨target, ?_, rfl, ?_, ?_⟩
    · rw [transferUpdate, evaluateHOLFiniteState_ite]
      simpa [evalHOLExact, toExact, localVar, vz, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, nonzero] using assigned
    · simpa only [ForwardCredit.valueFee, if_pos nonzero] using bind_lookup_same source "transfer_cost" 11300#64
    · intro key different
      exact bind_lookup_other _ _ _ _ different
  · refine ⟨source, ?_, rfl, ?_, by intro key different; rfl⟩
    · rw [transferUpdate, evaluateHOLFiniteState_ite]
      simp [evalHOLExact, toExact, localVar, vz, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, nonzero]
    · simpa only [ForwardCredit.valueFee, if_neg nonzero] using initial

/-- Actual zero-clock value-fee declaration/branch exposes the genuine fee
program with the correct current transfer word and preserved argument locals. -/
theorem setup_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (access memoryCost expand : BitVec 64) (words : U256Zero.Quad) (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (vz : source.locals.lookup (ofString "vz") = some (.val (.word (U256Zero.resultWord words))))
    (accessCell : source.locals.lookup (ofString "access_cost") = some (.val (.word access)))
    (xCell : source.locals.lookup (ofString "x") = some (.rStruct [.val (.word memoryCost), .val (.word expand)]))
    (run : evaluateHOLFiniteState source (withTransfer continuation) = (some (.returned returned), post)) :
    ∃ ready inner, emptyLocalsHOLFinite ready = emptyLocalsHOLFinite source ∧
      ready.locals.lookup (ofString "access_cost") = some (.val (.word access)) ∧
      ready.locals.lookup (ofString "transfer_cost") = some (.val (.word (ForwardCredit.valueFee words))) ∧
      ready.locals.lookup (ofString "x") = some (.rStruct [.val (.word memoryCost), .val (.word expand)]) ∧
      evaluateHOLFiniteState ready (program continuation) = (some (.returned returned), inner) ∧
      post = restore source "transfer_cost" inner ∧
      (∀ key : String, ofString "transfer_cost" ≠ ofString key →
        ready.locals.lookup (ofString key) = source.locals.lookup (ofString key)) := by
  obtain ⟨inner, declaredRun, scope⟩ := Input.declaration_return_word source post "transfer_cost" (.const 0#64) 0#64
    (.seq transferUpdate (program continuation)) returned rfl run
  let initial := bind source "transfer_cost" 0#64
  have initialVZ : initial.locals.lookup (ofString "vz") = some (.val (.word (U256Zero.resultWord words))) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans vz
  obtain ⟨ready, updateRun, canonical, transferCell, other⟩ := transfer_execute initial words initialVZ (bind_lookup_same _ _ _)
  have fields := congrArg emptyLocalsHOLFinite canonical
  change emptyLocalsHOLFinite ready = emptyLocalsHOLFinite source at fields
  have clock := congrArg PanSemStateFiniteExact.clock canonical
  change ready.clock = initial.clock at clock
  rw [WitnessRadix.StateSteps.next_sequence initial ready transferUpdate (program continuation) updateRun (by omega)] at declaredRun
  refine ⟨ready, inner, fields,
    (other "access_cost" (by decide)).trans ((bind_lookup_other _ _ _ _ (by decide)).trans accessCell), transferCell,
    (other "x" (by decide)).trans ((bind_lookup_other _ _ _ _ (by decide)).trans xCell), declaredRun, scope, ?_⟩
  intro key different
  exact (other key different).trans (bind_lookup_other _ _ _ _ different)

end InitECandidate.Solver.GasBudget.CallValueFee

#print axioms InitECandidate.Solver.GasBudget.CallValueFee.transfer_execute
#print axioms InitECandidate.Solver.GasBudget.CallValueFee.setup_normal
