import InitECandidate.Solver.GasBudget.MemoryExtendProgram
import InitECandidate.Solver.Input.NoneControl

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def clamped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length capacity expand : BitVec 64) :=
  if capacity * 2#64 < newLength length expand then
    setVarHOLFinite (ofString "ncap") (.val (.word (newLength length expand + 1024#64))) source else source

theorem clamp_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length capacity expand : BitVec 64)
    (ncapLocal : source.locals.lookup (ofString "ncap") = some (.val (.word (capacity * 2#64))))
    (nlenLocal : source.locals.lookup (ofString "nlen") = some (.val (.word (newLength length expand)))) :
    evaluateHOLFiniteState source clamp = (none, clamped source length capacity expand) := by
  classical
  by_cases fallback : capacity * 2#64 < newLength length expand
  all_goals simp [clamp, clamped, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_assign, evaluateHOLFiniteState_skip,
    evalHOLExact, evalListHOLExact, toExact, localVar, ncapLocal, nlenLocal, fallback, valueIsWord, valueWord, wordOpHOL, wordOp,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, isValidValueHOLFinite, lookupKvarHOLFinite, shapeOfHOLExact, shapeEqHOL_eq_true,
    setKvarHOLFinite]

theorem clamped_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length capacity expand : BitVec 64)
    (ncapLocal : source.locals.lookup (ofString "ncap") = some (.val (.word (capacity * 2#64)))) :
    (clamped source length capacity expand).locals.lookup (ofString "ncap") = some (.val (.word (chosenCapacity length capacity expand))) := by
  by_cases fallback : capacity * 2#64 < newLength length expand
  all_goals simp [clamped, chosenCapacity, fallback, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ncapLocal]

theorem clamped_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length capacity expand : BitVec 64) :
    emptyLocalsHOLFinite (clamped source length capacity expand) = emptyLocalsHOLFinite source := by
  unfold clamped
  split <;> rfl

theorem clamped_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length capacity expand : BitVec 64) (key : String)
    (other : ofString "ncap" ≠ ofString key) :
    (clamped source length capacity expand).locals.lookup (ofString key) = source.locals.lookup (ofString key) := by
  unfold clamped
  split
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, other, Ne.symm other]
  · rfl

theorem grow_prefix_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (length capacity expand : BitVec 64)
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (nlenLocal : source.locals.lookup (ofString "nlen") = some (.val (.word (newLength length expand))))
    (normal : evaluateHOLFiniteState source growBranch = (none, post)) :
    ∃ inner, evaluateHOLFiniteState (clamped (WitnessRadix.QueryBranch.bind source "ncap" (capacity * 2#64)) length capacity expand) growTail = (none, inner) ∧
      post = restore source "ncap" inner := by
  have read : eval source (.panop .mul [localVar "cap", .const 2#64]) = some (.val (.word (capacity * 2#64))) := by
    simp [eval, evalHOLExact, evalListHOLExact, toExact, localVar, capLocal, valueIsWord, valueWord, panOpHOL]
  obtain ⟨inner, run, postEq⟩ := Input.declaration_none source post "ncap" (.panop .mul [localVar "cap", .const 2#64])
    (capacity * 2#64) (.seq clamp growTail) read normal
  let entered := WitnessRadix.QueryBranch.bind source "ncap" (capacity * 2#64)
  have ncapE : entered.locals.lookup (ofString "ncap") = some (.val (.word (capacity * 2#64))) := bind_lookup_same _ _ _
  have nlenE : entered.locals.lookup (ofString "nlen") = some (.val (.word (newLength length expand))) :=
    (bind_lookup_other _ "ncap" "nlen" _ (by decide)).trans nlenLocal
  have actual := clamp_execute entered length capacity expand ncapE nlenE
  have clock := congrArg PanSemStateFiniteExact.clock (clamped_fields entered length capacity expand)
  change (clamped entered length capacity expand).clock = entered.clock at clock
  rw [WitnessRadix.StateSteps.next_sequence entered _ clamp growTail actual (by omega)] at run
  exact ⟨inner, run, postEq⟩

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.clamp_execute
#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.grow_prefix_normal
