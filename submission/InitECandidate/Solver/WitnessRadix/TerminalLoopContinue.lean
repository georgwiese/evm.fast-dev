import InitECandidate.Solver.WitnessRadix.TerminalContinue
import InitECandidate.Solver.WitnessRadix.TerminalReads

namespace InitECandidate.Solver.WitnessRadix.TerminalProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open QueryBranch PopProgram

theorem main_body_continue {F : Type} (source : PanSemStateFiniteExact 64 F)
    (depth oldStart oldCount oldBit destination pendingStart pendingCount pendingNode start count parent bit ordinal : BitVec 64)
    (nonzero : depth ≠ 0#64)
    (test : eval source terminalTest = some (.val (.word 1#64)))
    (readOrdinal : eval source ordinalExpression = some (.val (.word ordinal)))
    (locals : Locals source depth oldStart oldCount oldBit destination pendingStart pendingCount pendingNode)
    (cells : Cells source depth pendingStart pendingCount pendingNode start count parent bit)
    (safe : StoreSafe destination depth pendingStart pendingCount pendingNode parent)
    (mapped : source.memaddrs destination) :
    evaluateHOLFiniteState source BuildEntry.mainBody =
      (some .continue, popPost { source with
        memory := StoreWord.put source.memory destination (ordinal * 2#64 + 1#64) }
        depth start count parent bit) := by
  classical
  have terminalRun := terminal_continue source depth oldStart oldCount oldBit destination pendingStart pendingCount pendingNode
    start count parent bit ordinal nonzero readOrdinal locals cells safe mapped
  let next := popPost { source with memory := StoreWord.put source.memory destination (ordinal * 2#64 + 1#64) }
    depth start count parent bit
  have chosen : evaluateHOLFiniteState source (.ite terminalTest terminalCode .skip) = (some .continue, next) := by
    simp only [eval] at test
    rw [evaluateHOLFiniteState_ite, test]
    simpa using terminalRun
  rw [main_body_shape]
  exact StateSteps.stopped_sequence source next _ _ _ chosen (Nat.le_refl _)

/-- Exact outer-loop unrolling through the terminal continuation. It pays
the surrounding while clock once and resumes at the next concrete task. -/
theorem main_loop_continue {F : Type} (source : PanSemStateFiniteExact 64 F)
    (depth oldStart oldCount oldBit destination pendingStart pendingCount pendingNode start count parent bit ordinal : BitVec 64)
    (nonzero : depth ≠ 0#64)
    (test : eval (decClockHOLFinite source) terminalTest = some (.val (.word 1#64)))
    (readOrdinal : eval (decClockHOLFinite source) ordinalExpression = some (.val (.word ordinal)))
    (locals : Locals source depth oldStart oldCount oldBit destination pendingStart pendingCount pendingNode)
    (cells : Cells source depth pendingStart pendingCount pendingNode start count parent bit)
    (safe : StoreSafe destination depth pendingStart pendingCount pendingNode parent)
    (mapped : source.memaddrs destination) (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source BuildEntry.mainLoop =
      evaluateHOLFiniteState (popPost { decClockHOLFinite source with
        memory := StoreWord.put source.memory destination (ordinal * 2#64 + 1#64) }
        depth start count parent bit) BuildEntry.mainLoop := by
  classical
  let entry := decClockHOLFinite source
  let next := popPost { entry with memory := StoreWord.put source.memory destination (ordinal * 2#64 + 1#64) }
    depth start count parent bit
  have locals' := locals_of_field (source := source) (target := entry) rfl locals
  have cells' := cells_of_fields (source := source) (target := entry) rfl rfl cells
  have bodyRun : evaluateHOLFiniteState (decClockHOLFinite source) BuildEntry.mainBody = (some .continue, next) :=
    main_body_continue entry depth oldStart oldCount oldBit destination pendingStart pendingCount pendingNode
      start count parent bit ordinal nonzero test readOrdinal locals' cells' safe mapped
  have positive : source.clock ≠ 0 := by omega
  rw [main_loop_shape, evaluateHOLFiniteState_while_total]
  simp only [evalHOLFinite, evalHOLExact]
  rw [if_pos (by decide)]
  simp only [if_neg positive, bodyRun]
  rw [StateSteps.fixed_clock (decClockHOLFinite source) next _ (Nat.le_refl _)]

end InitECandidate.Solver.WitnessRadix.TerminalProgram

#print axioms InitECandidate.Solver.WitnessRadix.TerminalProgram.main_loop_continue
