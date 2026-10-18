import InitECandidate.Solver.GasBudget.FrameExceptionView
import InitECandidate.Solver.GasBudget.RefillMemory
import InitECandidate.Solver.GasBudget.PrefixEnvironment

namespace InitECandidate.Solver.GasBudget.FrameException
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def clearMemory (memory : Memory) (frame empty : BitVec 64) : Memory :=
  StoreWord.put (StoreWord.put memory (frame + 120#64) empty) (frame + 128#64) 0#64
def choiceMemory (memory : Memory) (frame err empty : BitVec 64) : Memory :=
  if err = 1#64 then StoreWord.put memory (frame + 160#64) err
  else clearMemory (WordWrites.write memory (Halt.writes frame (wordAt memory (frame + 64#64))
    (wordAt memory (frame + 184#64)) err)) frame empty
def memoryAfter (memory : Memory) (frame continuation err empty gas spill reservoir : BitVec 64) : Memory :=
  StoreWord.put (choiceMemory (WordWrites.write memory (Refill.writes frame gas spill reservoir)) frame err empty)
    (continuation + 32#64) 1#64

theorem clear_data_memory (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame empty : BitVec 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (emptyGlobal : source.globals.lookup (ofString "evm_empty") = some (.val (.word empty)))
    (normal : evaluateHOLFiniteState source clearData = (none, target)) :
    target = {source with memory := clearMemory source.memory frame empty} := by
  obtain ⟨first, firstRun, lastRun⟩ := Input.sequence_none source target _ _ normal
  have emptyRead : eval source (.var .global (ofString "evm_empty")) = some (.val (.word empty)) := by
    simpa only [eval, evalHOLExact, toExact] using emptyGlobal
  have firstEq := FrameField.normal_word source first frame 120#64 empty _ ev emptyRead firstRun
  have firstEV : first.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [firstEq]; exact ev
  have lastEq := FrameField.normal_word first target frame 128#64 0#64 (.const 0#64) firstEV rfl lastRun
  rw [lastEq, firstEq]
  rfl

theorem choice_memory (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame err empty : BitVec 64)
    (errLocal : source.locals.lookup (ofString "err") = some (.val (.word err)))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (emptyGlobal : source.globals.lookup (ofString "evm_empty") = some (.val (.word empty)))
    (haltCode : source.code.lookup (ofString "frame_halt") = some (Halt.formals, Halt.body, .one))
    (mapped : ∀ offset ∈ ([64, 160, 184] : List Nat), source.memaddrs (frame + BitVec.ofNat 64 offset))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (normal : evaluateHOLFiniteState source choice = (none, target)) :
    target = {source with memory := choiceMemory source.memory frame err empty, clock := source.clock - choicePrice err} := by
  have test : eval source condition = some (.val (.word (if err = 1#64 then 0#64 else 1#64))) := by
    simp [eval, condition, evalHOLExact, toExact, localVar, errLocal, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simp only [eval] at test
  rw [choice, evaluateHOLFiniteState_ite, test] at normal
  by_cases same : err = 1#64
  · have specialRun : evaluateHOLFiniteState source specialError = (none, target) := by simpa [same] using normal
    have errRead : eval source (localVar "err") = some (.val (.word err)) := by simpa only [eval, localVar, evalHOLExact, toExact] using errLocal
    have targetEq := FrameField.normal_word source target frame 160#64 err _ ev errRead specialRun
    simpa only [choiceMemory, if_pos same, choicePrice, Nat.sub_zero] using targetEq
  · have regularRun : evaluateHOLFiniteState source regularError = (none, target) := by simpa [same] using normal
    obtain ⟨called, haltRun, clearRun⟩ := Input.sequence_none source target halt clearData regularRun
    have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "err"] = some [.val (.word err)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, localVar, toExact, errLocal]
    obtain ⟨positive, clock, halted, budget, gasZero, errorCell⟩ := Halt.call_normal source called frame
      (wordAt source.memory (frame + 64#64)) (wordAt source.memory (frame + 184#64)) err _ args haltCode ev mapped
      (memory_word _ _) (memory_word _ _) cap haltRun
    have calledEV : called.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [halted]; exact ev
    have calledEmpty : called.globals.lookup (ofString "evm_empty") = some (.val (.word empty)) := by rw [halted]; exact emptyGlobal
    have cleared := clear_data_memory called target frame empty calledEV calledEmpty clearRun
    rw [halted] at cleared
    simpa only [choiceMemory, if_neg same, choicePrice] using cleared

/-- Complete original normal handler-body memory, including refill, either
real error branch, return-data clear and the actual continuation done word. -/
theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (view : View source) (err : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (errLocal : source.locals.lookup (ofString "err") = some (.val (.word err)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    post.memory = memoryAfter source.memory view.frame view.continuation err view.empty view.gas view.spill view.reservoir := by
  rw [body_shape] at normal
  have refillSafe : Input.LocalPrefix (ofString "err") refill := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨refilled, refillRun, branchRun, saved⟩ := refillSafe.normal_continue source post _ value normal
  obtain ⟨positive, refillFrame, refillOutside⟩ := Refill.call_memory source refilled view.frame view.message view.gas view.spill view.reservoir
    (original_refill_code source.code installed) view.ev view.refillMapped view.messageCell view.gasCell view.spillCell
    view.reservoirMapped view.reservoirCell view.reservoirAway refillRun
  have refillBudget := (refill_normal source refilled view.frame view.message view.gas view.spill view.reservoir
    (original_refill_code source.code installed) view.ev view.refillMapped view.messageCell view.gasCell view.spillCell
    view.reservoirMapped view.reservoirCell view.reservoirAway view.cap refillRun).2.2.2
  have currentEV : refilled.globals.lookup (ofString "ev") = some (.val (.word view.frame)) := by rw [refillFrame]; exact view.ev
  have currentEmpty : refilled.globals.lookup (ofString "evm_empty") = some (.val (.word view.empty)) := by rw [refillFrame]; exact view.emptyGlobal
  have currentErr : refilled.locals.lookup (ofString "err") = some (.val (.word err)) := by rw [refillFrame]; exact errLocal
  have currentCode : refilled.code.lookup (ofString "frame_halt") = some (Halt.formals, Halt.body, .one) := by rw [refillFrame]; exact original_halt_code source.code installed
  have currentMapped : ∀ offset ∈ ([64, 160, 184] : List Nat), refilled.memaddrs (view.frame + BitVec.ofNat 64 offset) := by
    intro offset member
    rw [refillFrame]
    exact view.haltMapped offset member
  have currentCap : regularBudget refilled.memory view.frame ≤ 16777216 := by rw [refillBudget]; exact view.cap
  obtain ⟨chosen, chooseRun, tailRun, saved⟩ := choice_safe.normal_continue refilled post (.seq markDone returnZero) value branchRun
  have chosenEq := choice_memory refilled chosen view.frame err view.empty currentErr currentEV currentEmpty currentCode currentMapped currentCap chooseRun
  have chosenCont : chosen.globals.lookup (ofString "cur_cont") = some (.val (.word view.continuation)) := by rw [chosenEq, refillFrame]; exact view.curCont
  have doneSafe : Input.LocalPrefix (ofString "err") markDone := .store _ _
  obtain ⟨done, doneRun, returnRun, saved⟩ := doneSafe.normal_continue chosen post returnZero value tailRun
  have addressRead : eval chosen doneAddress = some (.val (.word (view.continuation + 32#64))) := by
    simp [eval, doneAddress, addConst, evalHOLExact, evalListHOLExact, toExact, chosenCont, valueIsWord, valueWord, wordOpHOL, wordOp]
  obtain ⟨mapped, doneEq⟩ := Input.word_store_normal chosen done doneAddress (.const 1#64) (view.continuation + 32#64) 1#64 addressRead rfl doneRun
  have actualReturn : evaluateHOLFiniteState done returnZero = (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite done) := by
    simp [returnZero, evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have postEq := congrArg Prod.snd (returnRun.symm.trans actualReturn)
  change post = emptyLocalsHOLFinite done at postEq
  have postMemory := congrArg PanSemStateFiniteExact.memory postEq
  change post.memory = done.memory at postMemory
  rw [postMemory, doneEq, chosenEq, refillFrame]
  rfl

end InitECandidate.Solver.GasBudget.FrameException

#print axioms InitECandidate.Solver.GasBudget.FrameException.clear_data_memory
#print axioms InitECandidate.Solver.GasBudget.FrameException.choice_memory
#print axioms InitECandidate.Solver.GasBudget.FrameException.body_memory
