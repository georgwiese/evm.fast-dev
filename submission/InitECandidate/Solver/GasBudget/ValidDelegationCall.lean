import InitECandidate.Solver.GasBudget.ValidDelegation
import InitECandidate.Solver.Input.ScopedCallData
import InitECandidate.Solver.Input.ScopedCallException

namespace InitECandidate.Solver.GasBudget.ValidDelegation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem normal_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : Input.OriginalCode.Installed source.code)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "is_valid_delegation") arguments continuation) =
      (some (.returned returned), post)) :
    1 ≤ source.clock ∧ ∃ answer inner, (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState (bind {source with clock := source.clock - 1} name answer) continuation = (some (.returned returned), inner) ∧
      post = restore source name inner := by
  obtain ⟨positive, values, actual, callee, shape, target, result, inner, args, called, bodyRun, checked, tailRun, scope⟩ :=
    Input.CallNormal.scoped_data source post name .one (ofString "is_valid_delegation") arguments continuation returned run
  have bodyEq := Input.LocalEffects.lookup_body source.code (ofString "is_valid_delegation") formals body .one
    (original_code source.code installed) values actual callee shape called
  rw [bodyEq] at bodyRun
  obtain ⟨binary, targetEq⟩ := body_normal (callEntryStateHOLFinite source callee) target result bodyRun
  obtain ⟨answer, binaryWord, resultEq⟩ : ∃ answer : BitVec 64, (answer = 0#64 ∨ answer = 1#64) ∧ result = .val (.word answer) := by
    rcases binary with zero | one
    · exact ⟨0#64, Or.inl rfl, zero⟩
    · exact ⟨1#64, Or.inr rfl, one⟩
  rw [resultEq] at tailRun
  refine ⟨positive, answer, inner, binaryWord, ?_, scope⟩
  have canonical : Input.CallNormal.continuationEntry source target name (.val (.word answer)) =
      bind {source with clock := source.clock - 1} name answer := by rw [targetEq]; rfl
  rw [canonical] at tailRun
  exact tailRun

theorem exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : Input.OriginalCode.Installed source.code)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "is_valid_delegation") arguments continuation) =
      (some (.exception identifier payload), post)) :
    1 ≤ source.clock ∧ ∃ answer inner, (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState (bind {source with clock := source.clock - 1} name answer) continuation = (some (.exception identifier payload), inner) ∧
      post = restore source name inner := by
  obtain ⟨positive, values, actual, callee, shape, target, args, called, cases⟩ :=
    Input.CallNormal.scoped_exception_data source post name .one (ofString "is_valid_delegation") arguments continuation identifier payload run
  have bodyEq := Input.LocalEffects.lookup_body source.code (ofString "is_valid_delegation") formals body .one
    (original_code source.code installed) values actual callee shape called
  rcases cases with escaped | continued
  · obtain ⟨bodyRun, scope⟩ := escaped
    rw [bodyEq] at bodyRun
    exact ((safe source.code) (callEntryStateHOLFinite source callee) rfl identifier payload (congrArg Prod.fst bodyRun)).elim
  · obtain ⟨result, inner, bodyRun, checked, tailRun, scope⟩ := continued
    rw [bodyEq] at bodyRun
    obtain ⟨binary, targetEq⟩ := body_normal (callEntryStateHOLFinite source callee) target result bodyRun
    obtain ⟨answer, binaryWord, resultEq⟩ : ∃ answer : BitVec 64, (answer = 0#64 ∨ answer = 1#64) ∧ result = .val (.word answer) := by
      rcases binary with zero | one
      · exact ⟨0#64, Or.inl rfl, zero⟩
      · exact ⟨1#64, Or.inr rfl, one⟩
    rw [resultEq] at tailRun
    refine ⟨positive, answer, inner, binaryWord, ?_, scope⟩
    have canonical : Input.CallNormal.continuationEntry source target name (.val (.word answer)) =
        bind {source with clock := source.clock - 1} name answer := by rw [targetEq]; rfl
    rw [canonical] at tailRun
    exact tailRun

end InitECandidate.Solver.GasBudget.ValidDelegation

#print axioms InitECandidate.Solver.GasBudget.ValidDelegation.normal_prefix
#print axioms InitECandidate.Solver.GasBudget.ValidDelegation.exception_prefix
