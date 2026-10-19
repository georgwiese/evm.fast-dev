import InitECandidate.Solver.GasBudget.MemoryBufferOwnership
import InitECandidate.Solver.GasBudget.PcAddNormal

namespace InitECandidate.Solver.GasBudget.MemoryFinish
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def program : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64]) MemoryExtend.returnZero

theorem normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch : BitVec 64)
    (view : MemoryExtend.View source frame base length capacity pointer scratch) (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState source program = (some (.returned returned), post)) :
    1 ≤ source.clock ∧ returned = .val (.word 0#64) ∧ post.clock = source.clock - 1 ∧
      MemoryExtend.View post frame base length capacity pointer scratch ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      post.memory (frame + 184#64) = source.memory (frame + 184#64) ∧ post.globals = source.globals ∧
      (∀ query, query ≠ frame + 0#64 → post.memory query = source.memory query) := by
  have safe : Input.LocalPrefix (ofString "n") (.call (some (none, none)) (ofString "pc_add") [.const 1#64]) := .call none _ _ (by simp)
  obtain ⟨advanced, pcRun, returnRun, retained⟩ := safe.normal_continue source post MemoryExtend.returnZero returned run
  obtain ⟨pc, funded, clock, mapped, cell, advancedEq, budget, used⟩ := PcAdd.call_normal source advanced frame 1#64 [.const 1#64] rfl
    (OriginalCodeEnvironment.pc_add source.code view.installed) view.ev pcRun
  obtain ⟨read, postEq⟩ := Input.return_normal advanced post (.const 0#64) returned returnRun
  have value : returned = .val (.word 0#64) := by simpa [eval, evalHOLExact] using (Option.some.inj read).symm
  have advancedView : MemoryExtend.View advanced frame base length capacity pointer scratch := by
    have memoryView := view.with_memory (StoreWord.put source.memory (frame + 0#64) (pc + 1#64))
      (FrameField.put_other source.memory frame 0#64 (pc + 1#64) 24#64 (by decide) |>.trans view.baseCell)
      (FrameField.put_other source.memory frame 0#64 (pc + 1#64) 32#64 (by decide) |>.trans view.lengthCell)
      (FrameField.put_other source.memory frame 0#64 (pc + 1#64) 40#64 (by decide) |>.trans view.capacityCell)
    exact memoryView.after_erase (by rw [advancedEq]; rfl)
  refine ⟨funded, value, ?_, advancedView.after_erase (by rw [postEq]; rfl), ?_, ?_, ?_, ?_⟩
  · rw [postEq]; exact clock
  · rw [postEq]; exact budget
  · rw [postEq]; exact used
  · rw [postEq, advancedEq]; rfl
  · intro query other
    rw [postEq, advancedEq]
    change StoreWord.put source.memory (frame + 0#64) (pc + 1#64) query = source.memory query
    simp only [StoreWord.put, if_neg other]

end InitECandidate.Solver.GasBudget.MemoryFinish

#print axioms InitECandidate.Solver.GasBudget.MemoryFinish.normal
