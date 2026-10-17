import InitECandidate.Solver.WitnessRadix.PopStoreFrame
import InitECandidate.Solver.WitnessRadix.TerminalFinish

namespace InitECandidate.Solver.WitnessRadix.TerminalProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch PopProgram

theorem after_store_continue {F : Type} (source : PanSemStateFiniteExact 64 F)
    (depth oldStart oldCount oldBit destination pendingStart pendingCount pendingNode start count parent bit : BitVec 64)
    (nonzero : depth ≠ 0#64)
    (locals : Locals source depth oldStart oldCount oldBit destination pendingStart pendingCount pendingNode)
    (cells : Cells source depth pendingStart pendingCount pendingNode start count parent bit) :
    evaluateHOLFiniteState source afterStore = (some .continue, popPost source depth start count parent bit) := by
  classical
  have chosen : evaluateHOLFiniteState source (.ite depthTest BuildEntry.returnZero .skip) = (none, source) := by
    rw [evaluateHOLFiniteState_ite]
    simp [depthTest, localVar, evalHOLExact, toExact, locals.depthLocal, nonzero,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [after_store_shape, StateSteps.next_sequence source source _ popCode chosen (Nat.le_refl _)]
  exact pop_execute source depth oldStart oldCount oldBit destination pendingStart pendingCount pendingNode
    start count parent bit locals cells

/-- Complete actual leaf-store-and-pop transition. Explicit word separation
justifies retaining all four pending-task reads through the leaf store. -/
theorem terminal_continue {F : Type} (source : PanSemStateFiniteExact 64 F)
    (depth oldStart oldCount oldBit destination pendingStart pendingCount pendingNode start count parent bit ordinal : BitVec 64)
    (nonzero : depth ≠ 0#64)
    (readOrdinal : eval source ordinalExpression = some (.val (.word ordinal)))
    (locals : Locals source depth oldStart oldCount oldBit destination pendingStart pendingCount pendingNode)
    (cells : Cells source depth pendingStart pendingCount pendingNode start count parent bit)
    (safe : StoreSafe destination depth pendingStart pendingCount pendingNode parent)
    (mapped : source.memaddrs destination) :
    evaluateHOLFiniteState source terminalCode =
      (some .continue, popPost { source with
        memory := StoreWord.put source.memory destination (ordinal * 2#64 + 1#64) }
        depth start count parent bit) := by
  classical
  let ordState := bind source "ordinal" ordinal
  let written := { ordState with memory := StoreWord.put source.memory destination (ordinal * 2#64 + 1#64) }
  have locals' := locals_ordinal source depth oldStart oldCount oldBit destination pendingStart pendingCount pendingNode ordinal locals
  have cells' : Cells ordState depth pendingStart pendingCount pendingNode start count parent bit :=
    cells_of_fields (source := source) (target := ordState) rfl rfl cells
  have storedCells := cells_store ordState depth pendingStart pendingCount pendingNode start count parent bit
    destination (ordinal * 2#64 + 1#64) cells' safe
  have afterRun := after_store_continue written depth oldStart oldCount oldBit destination pendingStart pendingCount pendingNode
    start count parent bit nonzero
      (locals_of_field (source := ordState) (target := written) rfl locals') storedCells
  have ordinalLocal : ordState.locals.lookup (ofString "ordinal") = some (.val (.word ordinal)) :=
    bind_lookup_same source "ordinal" ordinal
  have destLocal : ordState.locals.lookup (ofString "dest") = some (.val (.word destination)) := locals'.destLocal
  have destRead : eval ordState (localVar "dest") = some (.val (.word destination)) := by
    simp [eval, localVar, evalHOLExact, toExact, destLocal]
  have write := StoreWord.execute ordState (localVar "dest") tagExpression destination (ordinal * 2#64 + 1#64)
    destRead (tag_read ordState ordinal ordinalLocal) mapped
  have sequence := (StateSteps.next_sequence ordState written
    (.store (localVar "dest") tagExpression) afterStore write (Nat.le_refl _)).trans afterRun
  simp only [eval] at readOrdinal
  rw [terminal_shape, evaluateHOLFiniteState_dec_total]
  simp only [readOrdinal, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  change (let output := evaluateHOLFiniteState ordState (.seq (.store (localVar "dest") tagExpression) afterStore);
    (output.1, restore source "ordinal" output.2)) = _
  rw [sequence]
  change (some (PanSemResultExact.continue : PanSemResultExact 64),
    restore source "ordinal" (popPost written depth start count parent bit)) = _
  rw [restore_pop_ordinal]
  have restored : restore source "ordinal" written =
      { source with memory := StoreWord.put source.memory destination (ordinal * 2#64 + 1#64) } := by
    change { restore source "ordinal" (bind source "ordinal" ordinal) with
      memory := StoreWord.put source.memory destination (ordinal * 2#64 + 1#64) } = _
    rw [restore_bound]
  rw [restored]

end InitECandidate.Solver.WitnessRadix.TerminalProgram

#print axioms InitECandidate.Solver.WitnessRadix.TerminalProgram.terminal_continue
