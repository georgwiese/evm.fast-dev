import InitECandidate.Solver.GasBudget.CallValueFeeSetup

namespace InitECandidate.Solver.GasBudget.CallAccessFee
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def resultWord (warm : BitVec 64) : BitVec 64 := if warm = 0#64 then 3000#64 else 100#64
def update : ProgHOL 64 := .ite (.cmp .equal (localVar "warm") (.const 0#64))
  (.assign .local (ofString "access_cost") (.const 3000#64)) .skip
def program (continuation : ProgHOL 64) : ProgHOL 64 :=
  .dec (ofString "access_cost") .one (.const 100#64) (.seq update continuation)

theorem range (warm : BitVec 64) : 100 ≤ (resultWord warm).toNat ∧ (resultWord warm).toNat ≤ 3000 := by
  unfold resultWord
  split <;> decide

theorem update_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (warm : BitVec 64)
    (warmLocal : source.locals.lookup (ofString "warm") = some (.val (.word warm)))
    (initial : source.locals.lookup (ofString "access_cost") = some (.val (.word 100#64))) :
    ∃ target, evaluateHOLFiniteState source update = (none, target) ∧ target = {source with locals := target.locals} ∧
      target.locals.lookup (ofString "access_cost") = some (.val (.word (resultWord warm))) ∧
      (∀ key : String, ofString "access_cost" ≠ ofString key → target.locals.lookup (ofString key) = source.locals.lookup (ofString key)) := by
  by_cases cold : warm = 0#64
  · let target := bind source "access_cost" 3000#64
    have assigned := WitnessRadix.StateSteps.assign_execute source "access_cost" (.const 3000#64) 100#64 3000#64 initial rfl
    refine ⟨target, ?_, rfl, ?_, ?_⟩
    · rw [update, evaluateHOLFiniteState_ite]
      simpa [evalHOLExact, toExact, localVar, warmLocal, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, cold] using assigned
    · simpa only [resultWord, if_pos cold] using bind_lookup_same source "access_cost" 3000#64
    · intro key different
      exact bind_lookup_other _ _ _ _ different
  · refine ⟨source, ?_, rfl, ?_, by intro key different; rfl⟩
    · rw [update, evaluateHOLFiniteState_ite]
      simp [evalHOLExact, toExact, localVar, warmLocal, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, cold]
    · simpa only [resultWord, if_neg cold] using initial

theorem setup_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (warm : BitVec 64)
    (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (warmLocal : source.locals.lookup (ofString "warm") = some (.val (.word warm)))
    (run : evaluateHOLFiniteState source (program continuation) = (some (.returned returned), post)) :
    ∃ ready inner, emptyLocalsHOLFinite ready = emptyLocalsHOLFinite source ∧
      ready.locals.lookup (ofString "access_cost") = some (.val (.word (resultWord warm))) ∧
      (∀ key : String, ofString "access_cost" ≠ ofString key → ready.locals.lookup (ofString key) = source.locals.lookup (ofString key)) ∧
      evaluateHOLFiniteState ready continuation = (some (.returned returned), inner) ∧ post = restore source "access_cost" inner := by
  obtain ⟨inner, declaredRun, scope⟩ := Input.declaration_return_word source post "access_cost" (.const 100#64) 100#64 (.seq update continuation) returned rfl run
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

#print axioms InitECandidate.Solver.GasBudget.CallAccessFee.range
#print axioms InitECandidate.Solver.GasBudget.CallAccessFee.update_execute
#print axioms InitECandidate.Solver.GasBudget.CallAccessFee.setup_normal
