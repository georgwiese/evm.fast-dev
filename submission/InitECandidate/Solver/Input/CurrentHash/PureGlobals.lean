import InitECandidate.Solver.Input.CurrentHash.StraightCost
import InitECandidate.Solver.Input.CurrentHash.MemoryGlobals
import InitECandidate.Solver.Input.CurrentHash.Sha256Pair

namespace InitECandidate.Solver.Input.CurrentHash.PureGlobals
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem basic (key : MlS) (code) (routine : Code.Routine) (member : routine ∈ [.heap_mark,.max,.st_le32]) :
    GlobalEffects.Preserves key code (Code.body routine) :=
  (StraightBody.effects key code (Code.body routine) (StraightCost.basic_supported routine member)).2

theorem basic_call (key : MlS) (code) (installed : OriginalCode.Installed code) (routine : Code.Routine)
    (member : routine ∈ [.heap_mark,.max,.st_le32]) (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    GlobalEffects.Preserves key code (.call (LocalEffects.callInfo destination) (Code.name routine) arguments) :=
  GlobalEffects.call_body key code destination (Code.name routine) arguments (Code.formals routine) (Code.body routine) (Code.shape routine)
    (Code.installed code installed routine) (basic key code routine member)

theorem le64 (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code (Code.body .st_le64) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_st_le64,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  exact GlobalEffects.sequence key code _ _ (basic_call key code installed .st_le32 (by simp) (some none) _)
    (GlobalEffects.sequence key code _ _ (basic_call key code installed .st_le32 (by simp) (some none) _) (GlobalEffects.returned key code _))

theorem le64_call (key : MlS) (code) (installed : OriginalCode.Installed code) (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    GlobalEffects.Preserves key code (.call (LocalEffects.callInfo destination) (Code.name .st_le64) arguments) :=
  GlobalEffects.call_body key code destination (Code.name .st_le64) arguments (Code.formals .st_le64) (Code.body .st_le64) (Code.shape .st_le64)
    (Code.installed code installed .st_le64) (le64 key code installed)

/-- Actual length mixing changes ordinary memory but preserves every global,
including the heap, on every outcome. No input values or mapping are assumed. -/
theorem mix (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code (Code.body .mix_in_length) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_mix_in_length,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  exact GlobalEffects.sequence key code _ _ (MemoryGlobals.call .zero key code installed (some none) _)
    (GlobalEffects.sequence key code _ _ (le64_call key code installed (some none) _)
      (GlobalEffects.sequence key code _ _
        (GlobalEffects.call_body key code (some none) (Code.name .sha256_pair) _ (Code.formals .sha256_pair) (Code.body .sha256_pair) (Code.shape .sha256_pair)
          (Code.installed code installed .sha256_pair) (Sha256Pair.any_key key code)) (GlobalEffects.returned key code _)))

theorem mix_call (key : MlS) (code) (installed : OriginalCode.Installed code) (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    GlobalEffects.Preserves key code (.call (LocalEffects.callInfo destination) (Code.name .mix_in_length) arguments) :=
  GlobalEffects.call_body key code destination (Code.name .mix_in_length) arguments
    (Code.formals .mix_in_length) (Code.body .mix_in_length) (Code.shape .mix_in_length) (Code.installed code installed .mix_in_length) (mix key code installed)

theorem u64 (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code (Code.body .htr_u64_at) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_htr_u64_at,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  exact GlobalEffects.sequence key code _ _ (MemoryGlobals.call .zero key code installed (some none) _)
    (GlobalEffects.sequence key code _ _ (MemoryGlobals.call .copy key code installed (some none) _) (GlobalEffects.returned key code _))

end InitECandidate.Solver.Input.CurrentHash.PureGlobals

#print axioms InitECandidate.Solver.Input.CurrentHash.PureGlobals.basic
#print axioms InitECandidate.Solver.Input.CurrentHash.PureGlobals.basic_call
#print axioms InitECandidate.Solver.Input.CurrentHash.PureGlobals.le64
#print axioms InitECandidate.Solver.Input.CurrentHash.PureGlobals.le64_call
#print axioms InitECandidate.Solver.Input.CurrentHash.PureGlobals.mix
#print axioms InitECandidate.Solver.Input.CurrentHash.PureGlobals.mix_call
#print axioms InitECandidate.Solver.Input.CurrentHash.PureGlobals.u64
