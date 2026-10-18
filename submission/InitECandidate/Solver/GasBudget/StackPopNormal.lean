import InitECandidate.Solver.GasBudget.FrameField
import InitECandidate.Solver.Input.NormalDeclarationEntry
import InitECandidate.Solver.Input.PureGuardNormalPrefix
import InitECandidate.Solver.Input.ReturnNormal
import InitECandidate.Solver.Input.ScalarNormal

namespace InitECandidate.Solver.GasBudget.StackPop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def body : ProgHOL 64 := match Guest.guestFn_stack_pop with | .function fn => progToHOL fn.body | _ => .skip
def test : ExpHOL 64 := .cmp .equal (localVar "sp") (.const 0#64)
def guard : ProgHOL 64 := .ite test (.raise (ofString "EvmErr") (.const 2#64)) .skip
def decremented : ExpHOL 64 := .op .sub [localVar "sp", .const 1#64]
def decrement : ProgHOL 64 := .assign .local (ofString "sp") decremented
def writeSP : ProgHOL 64 := .store (frameAddress 16#64) (localVar "sp")
def returnedValue : ExpHOL 64 := .load (.comb [.one, .one, .one, .one])
  (.op .add [frameLoad 8#64, .panop .mul [localVar "sp", .const 32#64]])
def afterGuard : ProgHOL 64 := .seq decrement (.seq writeSP (.return returnedValue))
def tail : ProgHOL 64 := .seq guard afterGuard

theorem body_shape : body = .dec (ofString "sp") .one (frameLoad 16#64) tail := by
  simp only [body, Guest.guestFn_stack_pop, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, tail, guard, test, afterGuard, decrement, decremented,
    writeSP, returnedValue, frameLoad, frameAddress, localVar]

/-- Actual stack_pop derives its successful sp read, underflow guard and
single frame mutation. It has no body call clock and cannot alter the
physical gas ledger. Stack-data reads remain those of the original return. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    ∃ sp : BitVec 64, source.memaddrs (frame + 16#64) ∧ source.memory (frame + 16#64) = .word sp ∧ sp ≠ 0#64 ∧
      post.clock = source.clock ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := StoreWord.put source.memory (frame + 16#64) (sp - 1#64)} ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      post.memory (frame + 184#64) = source.memory (frame + 184#64) ∧
      (∀ address, address ≠ frame + 16#64 → post.memory address = source.memory address) := by
  rw [body_shape] at normal
  obtain ⟨declared, inner, read, typed, innerRun, restored⟩ := Input.CallNormal.declaration_normal_entry source post "sp" .one (frameLoad 16#64) tail value normal
  have mapped := Input.load_one_mapped source (frameAddress 16#64) (frame + 16#64) declared (address_read source frame 16#64 ev) read
  cases spCell : source.memory (frame + 16#64) with
  | word sp =>
    have spRead := frame_read source frame 16#64 sp ev mapped spCell
    have declaredEq : declared = .val (.word sp) := Option.some.inj (read.symm.trans spRead)
    subst declared
    let entered := bind source "sp" sp
    have spE : entered.locals.lookup (ofString "sp") = some (.val (.word sp)) := bind_lookup_same _ _ _
    have guardSafe : Input.PureGuard guard := .ite _ (.raise _ _) .skip
    obtain ⟨guardRun, restRun⟩ := guardSafe.normal_prefix entered inner afterGuard value innerRun
    have nonzero : sp ≠ 0#64 := by
      intro zero
      have testRead : eval entered test = some (.val (.word 1#64)) := by
        simp [eval, test, evalHOLExact, toExact, localVar, spE, zero, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      simp only [eval] at testRead
      rw [guard, evaluateHOLFiniteState_ite, testRead] at guardRun
      change evaluateHOLFiniteState entered (.raise (ofString "EvmErr") (.const 2#64)) = (none, entered) at guardRun
      rw [evaluateHOLFiniteState_raise] at guardRun
      simp only [evalHOLExact] at guardRun
      split at guardRun <;> (try split at guardRun) <;> cases guardRun
    have decrementRead : eval entered decremented = some (.val (.word (sp - 1#64))) := by
      simp [eval, decremented, evalHOLExact, evalListHOLExact, toExact, localVar, spE, valueIsWord, valueWord, wordOpHOL, wordOp]
    have decrementRun := StateSteps.assign_execute entered "sp" decremented sp (sp - 1#64) spE decrementRead
    let next := bind entered "sp" (sp - 1#64)
    rw [afterGuard, StateSteps.next_sequence entered next decrement _ decrementRun (Nat.le_refl _)] at restRun
    have writeSafe : Input.LocalPrefix (ofString "sp") writeSP := .store _ _
    obtain ⟨stored, storeRun, returnRun, saved⟩ := writeSafe.normal_continue next inner _ value restRun
    have spN : next.locals.lookup (ofString "sp") = some (.val (.word (sp - 1#64))) := bind_lookup_same _ _ _
    have valueRead : eval next (localVar "sp") = some (.val (.word (sp - 1#64))) := by simpa only [eval, localVar, evalHOLExact, toExact] using spN
    have storedEq := FrameField.normal_word next stored frame 16#64 (sp - 1#64) (localVar "sp") ev valueRead storeRun
    obtain ⟨returnedRead, innerEq⟩ := Input.return_normal stored inner returnedValue value returnRun
    have postMemory : post.memory = StoreWord.put source.memory (frame + 16#64) (sp - 1#64) := by
      rw [restored, innerEq, storedEq]
      rfl
    have postClock : post.clock = source.clock := by rw [restored, innerEq, storedEq]; rfl
    refine ⟨sp, mapped, rfl, nonzero, postClock, ?_, ?_, ?_, ?_⟩
    · rw [restored, innerEq, storedEq]
      rfl
    · rw [postMemory]
      exact FrameField.put_budget source.memory frame 16#64 (sp - 1#64) (by decide) (by decide) (by decide)
    · rw [postMemory]
      exact FrameField.put_other source.memory frame 16#64 (sp - 1#64) 184#64 (by decide)
    · intro address away
      rw [postMemory]
      exact if_neg away

end InitECandidate.Solver.GasBudget.StackPop

#print axioms InitECandidate.Solver.GasBudget.StackPop.body_shape
#print axioms InitECandidate.Solver.GasBudget.StackPop.body_normal
