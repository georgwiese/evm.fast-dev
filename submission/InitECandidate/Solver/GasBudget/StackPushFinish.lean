import InitECandidate.Solver.GasBudget.StackPushNonGrowthCall
import InitECandidate.Solver.GasBudget.PcAddNormal
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.GasBudget.StackPush
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def finish (arguments : List (ExpHOL 64)) : ProgHOL 64 :=
  .seq (.call (some (none, none)) (ofString "stack_push") arguments)
    (.seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64]) (.return (.const 0#64)))

/-- The common actual opcode suffix pushes to an existing free slot and
advances pc, preserving gas and returning zero. Both helper clocks and tuple
checks follow from the real normal suffix, rather than a supplied trace. -/
theorem finish_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base sp capacity : BitVec 64)
    (arguments : List (ExpHOL 64))
    (code : source.code.lookup (ofString "stack_push") = some (formals, body, .one))
    (pcCode : source.code.lookup (ofString "pc_add") = some (PcAdd.formals, PcAdd.body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (spCell : source.memory (frame + 16#64) = .word sp) (capCell : source.memory (frame + 232#64) = .word capacity)
    (baseMapped : source.memaddrs (frame + 8#64)) (baseCell : source.memory (frame + 8#64) = .word base)
    (room : sp < capacity) (bounded : capacity.toNat ≤ 1024)
    (separate : ∀ offset ∈ ([64, 184, 192] : List Nat), ∀ index < 4,
      frame + BitVec.ofNat 64 offset ≠ (base + sp * 32#64) + BitVec.ofNat 64 (8 * index))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (finish arguments) = (some (.returned value), post)) :
    2 ≤ source.clock ∧ value = .val (.word 0#64) ∧ post.clock = source.clock - 2 ∧
      post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - 2} ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      post.memory (frame + 184#64) = source.memory (frame + 184#64) ∧
      post.memory (frame + 16#64) = .word (sp + 1#64) ∧
      (wordAt post.memory (frame + 16#64)).toNat = sp.toNat + 1 ∧
      (∀ address, address ≠ frame + 0#64 → address ≠ frame + 16#64 →
        (∀ index < 4, address ≠ (base + sp * 32#64) + BitVec.ofNat 64 (8 * index)) →
        post.memory address = source.memory address) := by
  rw [finish] at normal
  have pushSafe : Input.LocalPrefix (ofString "setup") (.call (some (none, none)) (ofString "stack_push") arguments) :=
    .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨pushed, pushRun, restRun, saved⟩ := pushSafe.normal_continue source post _ value normal
  obtain ⟨pushFits, pushClock, pushFrame, pushBudget, finalSP, depth, depthBound, usedSame, outside⟩ :=
    non_growth_call_normal source pushed frame base sp capacity arguments code ev spCell capCell baseMapped baseCell room bounded separate pushRun
  have pushedPC : pushed.code.lookup (ofString "pc_add") = some (PcAdd.formals, PcAdd.body, .one) := by rw [pushFrame]; exact pcCode
  have pushedEV : pushed.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [pushFrame]; exact ev
  have pcSafe : Input.LocalPrefix (ofString "setup") (.call (some (none, none)) (ofString "pc_add") [.const 1#64]) :=
    .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨advanced, pcRun, returnRun, savedAgain⟩ := pcSafe.normal_continue pushed post _ value restRun
  obtain ⟨pc, pcFits, pcClock, pcMapped, pcCell, pcFrame, pcBudget, pcUsed⟩ :=
    PcAdd.call_normal pushed advanced frame 1#64 [.const 1#64] rfl pushedPC pushedEV pcRun
  obtain ⟨returnedRead, postEq⟩ := Input.return_normal advanced post (.const 0#64) value returnRun
  have valueEq : value = .val (.word 0#64) := (Option.some.inj returnedRead).symm
  have fullFrame : advanced = {source with memory := advanced.memory, clock := source.clock - 2} := by
    have memoryEq := congrArg PanSemStateFiniteExact.memory pcFrame
    change advanced.memory = WitnessRadix.StoreWord.put pushed.memory (frame + 0#64) (pc + 1#64) at memoryEq
    have canonical := pcFrame
    rw [← memoryEq, pushClock] at canonical
    have combined := canonical.trans (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
      {state with memory := advanced.memory, clock := source.clock - 1 - 1}) pushFrame)
    simpa only [show source.clock - 1 - 1 = source.clock - 2 from by omega] using combined
  have pcSP : advanced.memory (frame + 16#64) = pushed.memory (frame + 16#64) := by
    rw [pcFrame]
    exact FrameField.put_other pushed.memory frame 0#64 (pc + 1#64) 16#64 (by decide)
  refine ⟨by omega, valueEq, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [postEq]; change advanced.clock = _; omega
  · rw [postEq]; exact congrArg emptyLocalsHOLFinite fullFrame
  · rw [postEq]; exact pcBudget.trans pushBudget
  · rw [postEq]; exact pcUsed.trans usedSame
  · rw [postEq]; exact pcSP.trans finalSP
  · rw [postEq]
    change (WitnessRadix.MemoryBytes.wordBits (advanced.memory (frame + 16#64))).toNat = _
    rw [pcSP]
    exact depth
  · intro address notPC notSP away
    rw [postEq, pcFrame]
    change WitnessRadix.StoreWord.put pushed.memory (frame + 0#64) (pc + 1#64) address = source.memory address
    rw [show WitnessRadix.StoreWord.put pushed.memory (frame + 0#64) (pc + 1#64) address = pushed.memory address from if_neg notPC]
    exact outside address notSP away

end InitECandidate.Solver.GasBudget.StackPush

#print axioms InitECandidate.Solver.GasBudget.StackPush.finish_normal
