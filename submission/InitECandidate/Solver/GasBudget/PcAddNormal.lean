import InitECandidate.Solver.GasBudget.Calls
import InitECandidate.Solver.GasBudget.FrameField
import InitECandidate.Solver.Input.ScalarNormal
import InitECandidate.Solver.Input.IgnoredCallNormal

namespace InitECandidate.Solver.GasBudget.PcAdd
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def body : ProgHOL 64 := match Guest.guestFn_pc_add with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "n", .one)]
def expression : ExpHOL 64 := .op .add [frameLoad 0#64, localVar "n"]
def increment : ProgHOL 64 := .store (frameAddress 0#64) expression

theorem body_shape : body = .seq increment (.return (.const 0#64)) := by
  simp only [body, Guest.guestFn_pc_add, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, increment, expression, frameLoad, frameAddress, localVar]

/-- The actual pc_add body derives its reached mapped pc cell and has no
body call/loop cost. Address arithmetic retains the implementation's wrapping
word semantics. No natural pc-increment/non-wrap premise is imposed. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame amount : BitVec 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (amountLocal : source.locals.lookup (ofString "n") = some (.val (.word amount)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    ∃ pc : BitVec 64, source.memaddrs (frame + 0#64) ∧ source.memory (frame + 0#64) = .word pc ∧
      value = .val (.word 0#64) ∧
      post = emptyLocalsHOLFinite {source with memory := StoreWord.put source.memory (frame + 0#64) (pc + amount)} := by
  rw [body_shape] at normal
  have safe : Input.LocalPrefix (ofString "n") increment := .store _ _
  obtain ⟨stored, storeRun, returnRun, _⟩ := safe.normal_continue source post _ value normal
  have mapped : source.memaddrs (frame + 0#64) := Input.store_mapped_normal source stored _ expression _
    (address_read source frame 0#64 ev)
    (by intro result observed; have length := Input.op_length source .add [frameLoad 0#64, localVar "n"] result observed; omega) storeRun
  cases pcCell : source.memory (frame + 0#64) with
  | word pc =>
    have pcRead := frame_read source frame 0#64 pc ev mapped pcCell
    have read : eval source expression = some (.val (.word (pc + amount))) := by
      simp only [eval] at pcRead ⊢
      simp only [expression, evalHOLExact, evalListHOLExact, pcRead]
      simp [evalHOLExact, toExact, localVar, amountLocal, valueIsWord, valueWord, wordOpHOL, wordOp]
    have storedEq := FrameField.normal_word source stored frame 0#64 (pc + amount) expression ev read storeRun
    have actualReturn : evaluateHOLFiniteState stored (.return (.const 0#64)) =
        (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite stored) := by
      simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
    have sameValue := congrArg Prod.fst (returnRun.symm.trans actualReturn)
    have samePost := congrArg Prod.snd (returnRun.symm.trans actualReturn)
    refine ⟨pc, mapped, rfl, ?_, ?_⟩
    · simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using sameValue
    · change post = emptyLocalsHOLFinite stored at samePost
      rw [samePost, storedEq]

theorem call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame amount : BitVec 64)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word amount)])
    (code : source.code.lookup (ofString "pc_add") = some (formals, body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "pc_add") arguments) = (none, target)) :
    ∃ pc : BitVec 64, 1 ≤ source.clock ∧ target.clock = source.clock - 1 ∧
      source.memaddrs (frame + 0#64) ∧ source.memory (frame + 0#64) = .word pc ∧
      target = {source with memory := StoreWord.put source.memory (frame + 0#64) (pc + amount), clock := source.clock - 1} ∧
      regularBudget target.memory frame = regularBudget source.memory frame ∧
      target.memory (frame + 184#64) = source.memory (frame + 184#64) := by
  obtain ⟨callee, called, amountLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "pc_add") "n" body amount code
  obtain ⟨positive, post, returned, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "pc_add") arguments [.val (.word amount)] body callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨pc, mapped, pcCell, valueEq, postEq⟩ := body_normal entry post frame amount ev amountLocal returned bodyRun
  rw [valueEq] at bodyRun
  have actual := ignored_return source post (ofString "pc_add") arguments [.val (.word amount)] body callee 1 args called positive bodyRun
    (show emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - 1} from by rw [postEq]; rfl)
  rw [postEq] at actual
  have same := congrArg Prod.snd (normal.symm.trans actual)
  change target = {source with memory := StoreWord.put source.memory (frame + 0#64) (pc + amount), clock := source.clock - 1} at same
  refine ⟨pc, positive, by rw [same], mapped, pcCell, same, ?_, ?_⟩
  · rw [same]
    exact FrameField.put_budget source.memory frame 0#64 (pc + amount) (by decide) (by decide) (by decide)
  · rw [same]
    exact FrameField.put_other source.memory frame 0#64 (pc + amount) 184#64 (by decide)

end InitECandidate.Solver.GasBudget.PcAdd

#print axioms InitECandidate.Solver.GasBudget.PcAdd.body_shape
#print axioms InitECandidate.Solver.GasBudget.PcAdd.body_normal
#print axioms InitECandidate.Solver.GasBudget.PcAdd.call_normal
