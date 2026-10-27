import InitECandidate.Solver.Input.GlobalEffects
import InitECandidate.Solver.Input.TrapCost

namespace InitECandidate.Solver.Input.GlobalEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem of_readonly (key : MlS) (code) (program : ProgHOL 64) (pure : LocalEffects.Preserves code program) :
    Preserves key code program := by
  intro source installed
  have fields := pure source installed
  have codeEq := congrArg PanSemStateFiniteExact.code fields
  have globalEq := congrArg (fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>current.globals.lookup key) fields
  exact Prod.ext codeEq globalEq

theorem global_other (key : MlS) (code) (name : MlS) (expression : ExpHOL 64) (other : key≠name) :
    Preserves key code (.assign .global name expression) := by
  intro source installed
  rw [evaluateHOLFiniteState_assign]
  split
  · rfl
  · split
    · simp [erase,setKvarHOLFinite,setGlobalHOLFinite,HolFiniteMapExact.update,FUPDATE,other,Ne.symm other]
    · rfl

theorem store (key : MlS) (code) (address value : ExpHOL 64) : Preserves key code (.store address value) := by
  intro source installed
  rw [evaluateHOLFiniteState_store]
  repeat first | rfl | split

theorem shared_store (key : MlS) (code) (size : OpSize) (address value : ExpHOL 64) :
    Preserves key code (.shMemStore size address value) := by
  intro source installed
  apply Prod.ext
  · exact (Input.evaluation_fields source (evaluateHOLFiniteState source (.shMemStore size address value)).2 (.shMemStore size address value)
      (evaluateHOLFiniteState source (.shMemStore size address value)).1 rfl).2.2.2
  · change (evaluateHOLFiniteState source (.shMemStore size address value)).2.globals.lookup key=source.globals.lookup key
    rw [evaluateHOLFiniteState_shMemStore]
    change (shMemStoreClauseHOLFiniteExact source size address value).2.globals key=source.globals.lookup key
    unfold shMemStoreClauseHOLFiniteExact shMemStoreClauseHOLExact shMemStoreHOLExact
    dsimp only
    repeat' first | rfl | split

theorem external (key : MlS) (code) (name : MlS) (configuration configurationLength array arrayLength : ExpHOL 64) :
    Preserves key code (.extCall name configuration configurationLength array arrayLength) := by
  intro source installed
  rw [evaluateHOLFiniteState_extCall_source]
  repeat first | rfl | split

/-- Shared loads into caller locals retain every global on all outcomes,
including missing host bytes and terminal oracle replies. -/
theorem shared_load (key : MlS) (code) (operator : OpSize) (name : MlS) (expression : ExpHOL 64) :
    Preserves key code (.shMemLoad operator .local name expression) := by
  classical
  intro source installed
  rw [evaluateHOLFiniteState_shMemLoad_source]
  simp only [shMemLoadHOLFiniteExact]
  repeat' first
    | rfl
    | unfold setKvarFfiHOLFinite
    | unfold setKvarHOLFinite
    | unfold setVarHOLFinite
    | split

end InitECandidate.Solver.Input.GlobalEffects

#print axioms InitECandidate.Solver.Input.GlobalEffects.of_readonly
#print axioms InitECandidate.Solver.Input.GlobalEffects.global_other
#print axioms InitECandidate.Solver.Input.GlobalEffects.store
#print axioms InitECandidate.Solver.Input.GlobalEffects.shared_store
#print axioms InitECandidate.Solver.Input.GlobalEffects.external
#print axioms InitECandidate.Solver.Input.GlobalEffects.shared_load
