import InitECandidate.Solver.GasBudget.RootExitProgram

namespace InitECandidate.Solver.GasBudget.RootExit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

def rootState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (parent previous : BitVec 64) :=
  bind (Input.putGlobal (Input.putGlobal source "ev" parent) "cur_cont" previous) "go" 0#64

/-- Actual root-only exit restores both saved globals and clears the real
loop flag, with no call/loop clock and no assumed destination-shape check. -/
theorem root_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cont parent previous : BitVec 64)
    (continuation : source.globals.lookup (ofString "cur_cont") = some (.val (.word cont)))
    (mappedParent : source.memaddrs (cont + 0#64)) (storedParent : source.memory (cont + 0#64) = .word parent)
    (mappedPrevious : source.memaddrs (cont + 8#64)) (storedPrevious : source.memory (cont + 8#64) = .word previous)
    (normal : evaluateHOLFiniteState source rootBranch = (none, target)) : target = rootState source parent previous := by
  obtain ⟨first, firstRun, lastRun⟩ := Input.sequence_none source target setParent (.seq setContinuation setGo) normal
  have parentRead := Input.global_field_read source "cur_cont" cont 0#64 parent continuation mappedParent storedParent
  have firstEq := Input.global_assign_none source first "ev" (recordLoad 0#64) parent parentRead firstRun
  subst first
  let entered := Input.putGlobal source "ev" parent
  have enteredCont : entered.globals.lookup (ofString "cur_cont") = some (.val (.word cont)) :=
    (Input.putGlobal.lookup_other source "ev" parent (ofString "cur_cont") (by decide)).trans continuation
  have previousRead := Input.global_field_read entered "cur_cont" cont 8#64 previous enteredCont mappedPrevious storedPrevious
  obtain ⟨second, continuationRun, goRun⟩ := Input.sequence_none entered target setContinuation setGo lastRun
  have secondEq := Input.global_assign_none entered second "cur_cont" (recordLoad 8#64) previous previousRead continuationRun
  subst second
  exact Input.assign_none _ target "go" (.const 0#64) 0#64 rfl goRun

theorem root_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (parent previous : BitVec 64) :
    (rootState source parent previous).locals.lookup (ofString "go") = some (.val (.word 0#64)) ∧
      (rootState source parent previous).globals.lookup (ofString "ev") = some (.val (.word parent)) ∧
      (rootState source parent previous).globals.lookup (ofString "cur_cont") = some (.val (.word previous)) ∧
      (rootState source parent previous).globals.lookup (ofString "heap_ptr") = source.globals.lookup (ofString "heap_ptr") ∧
      (rootState source parent previous).globals.lookup (ofString "journal_n") = source.globals.lookup (ofString "journal_n") ∧
      (rootState source parent previous).memory = source.memory ∧ (rootState source parent previous).clock = source.clock := by
  refine ⟨bind_lookup_same _ _ _, ?_, Input.putGlobal.lookup_same _ _ _, ?_, ?_, rfl, rfl⟩
  · exact (Input.putGlobal.lookup_other _ "cur_cont" previous (ofString "ev") (by decide)).trans (Input.putGlobal.lookup_same source "ev" parent)
  · exact (Input.putGlobal.lookup_other _ "cur_cont" previous (ofString "heap_ptr") (by decide)).trans
      (Input.putGlobal.lookup_other source "ev" parent (ofString "heap_ptr") (by decide))
  · exact (Input.putGlobal.lookup_other _ "cur_cont" previous (ofString "journal_n") (by decide)).trans
      (Input.putGlobal.lookup_other source "ev" parent (ofString "journal_n") (by decide))

end InitECandidate.Solver.GasBudget.RootExit

#print axioms InitECandidate.Solver.GasBudget.RootExit.root_normal
#print axioms InitECandidate.Solver.GasBudget.RootExit.root_fields
