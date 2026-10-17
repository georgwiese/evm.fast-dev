import InitECandidate.Solver.WitnessRadix.PopParent
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.WitnessRadix.PopProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

structure Locals {F : Type} (source : PanSemStateFiniteExact 64 F)
    (depth start count bit dest pendingStart pendingCount pendingNode : BitVec 64) : Prop where
  depthLocal : source.locals.lookup (ofString "depth") = some (.val (.word depth))
  startLocal : source.locals.lookup (ofString "start") = some (.val (.word start))
  countLocal : source.locals.lookup (ofString "count") = some (.val (.word count))
  bitLocal : source.locals.lookup (ofString "bit") = some (.val (.word bit))
  destLocal : source.locals.lookup (ofString "dest") = some (.val (.word dest))
  pendingStartLocal : source.locals.lookup (ofString "pending_start") = some (.val (.word pendingStart))
  pendingCountLocal : source.locals.lookup (ofString "pending_count") = some (.val (.word pendingCount))
  pendingNodeLocal : source.locals.lookup (ofString "pending_node") = some (.val (.word pendingNode))

structure Cells {F : Type} (source : PanSemStateFiniteExact 64 F)
    (depth pendingStart pendingCount pendingNode start count parent bit : BitVec 64) : Prop where
  startMapped : source.memaddrs (pendingStart + (depth - 1#64) * 8#64)
  startWord : source.memory (pendingStart + (depth - 1#64) * 8#64) = .word start
  countMapped : source.memaddrs (pendingCount + (depth - 1#64) * 8#64)
  countWord : source.memory (pendingCount + (depth - 1#64) * 8#64) = .word count
  parentMapped : source.memaddrs (pendingNode + (depth - 1#64) * 8#64)
  parentWord : source.memory (pendingNode + (depth - 1#64) * 8#64) = .word parent
  bitMapped : source.memaddrs parent
  bitWord : source.memory parent = .word bit

def popPost {F : Type} (source : PanSemStateFiniteExact 64 F)
    (depth start count parent bit : BitVec 64) : PanSemStateFiniteExact 64 F :=
  bind (bind (bind (bind (bind source "depth" (depth - 1#64)) "start" start)
    "count" count) "bit" (bit + 1#64)) "dest" (parent + 16#64)

/-- The complete literal pending-task pop. Concrete suffix cells and parent
bit determine the next task; only five locals change and no clock is paid. -/
theorem pop_execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (depth oldStart oldCount oldBit oldDest pendingStart pendingCount pendingNode start count parent bit : BitVec 64)
    (locals : Locals source depth oldStart oldCount oldBit oldDest pendingStart pendingCount pendingNode)
    (cells : Cells source depth pendingStart pendingCount pendingNode start count parent bit) :
    evaluateHOLFiniteState source TerminalProgram.popCode =
      (some .continue, popPost source depth start count parent bit) := by
  classical
  let depthState := bind source "depth" (depth - 1#64)
  let startState := bind depthState "start" start
  let countState := bind startState "count" count
  have depthOther (name : String) (nd : ofString "depth" ≠ ofString name) :
      depthState.locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
    bind_lookup_other source "depth" name _ nd
  have startOther (name : String) (nd : ofString "depth" ≠ ofString name)
      (ns : ofString "start" ≠ ofString name) :
      startState.locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
    dsimp only [startState, depthState]
    rw [bind_lookup_other _ "start" name _ ns, bind_lookup_other source "depth" name _ nd]
  have countOther (name : String) (nd : ofString "depth" ≠ ofString name)
      (ns : ofString "start" ≠ ofString name) (nc : ofString "count" ≠ ofString name) :
      countState.locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
    dsimp only [countState, startState, depthState]
    rw [bind_lookup_other _ "count" name _ nc, bind_lookup_other _ "start" name _ ns,
      bind_lookup_other source "depth" name _ nd]
  have depth1 : depthState.locals.lookup (ofString "depth") = some (.val (.word (depth - 1#64))) :=
    bind_lookup_same source "depth" _
  have depth2 : startState.locals.lookup (ofString "depth") = some (.val (.word (depth - 1#64))) := by
    rw [bind_lookup_other depthState "start" "depth" start (by decide)]
    exact depth1
  have depth3 : countState.locals.lookup (ofString "depth") = some (.val (.word (depth - 1#64))) := by
    rw [bind_lookup_other startState "count" "depth" count (by decide)]
    exact depth2
  have depthRun := StateSteps.assign_execute source "depth" _ depth (depth - 1#64)
    locals.depthLocal (decrement_read source depth locals.depthLocal)
  have startRead := pending_read depthState "pending_start" pendingStart (depth - 1#64) start
    ((depthOther _ (by decide)).trans locals.pendingStartLocal) depth1 cells.startMapped cells.startWord
  have startRun := StateSteps.assign_execute depthState "start" _ oldStart start
    ((depthOther _ (by decide)).trans locals.startLocal) startRead
  have countRead := pending_read startState "pending_count" pendingCount (depth - 1#64) count
    ((startOther _ (by decide) (by decide)).trans locals.pendingCountLocal) depth2 cells.countMapped cells.countWord
  have countRun := StateSteps.assign_execute startState "count" _ oldCount count
    ((startOther _ (by decide) (by decide)).trans locals.countLocal) countRead
  have parentRead := pending_read countState "pending_node" pendingNode (depth - 1#64) parent
    ((countOther _ (by decide) (by decide) (by decide)).trans locals.pendingNodeLocal)
    depth3 cells.parentMapped cells.parentWord
  have parentRun := parent_declaration countState parent bit oldBit oldDest parentRead
    ((countOther _ (by decide) (by decide) (by decide)).trans locals.bitLocal)
    ((countOther _ (by decide) (by decide) (by decide)).trans locals.destLocal)
    cells.bitMapped cells.bitWord
  rw [pop_shape]
  rw [StateSteps.next_sequence source depthState decrement _ depthRun (Nat.le_refl _)]
  rw [StateSteps.next_sequence depthState startState startAssignment _ startRun (Nat.le_refl _)]
  rw [StateSteps.next_sequence startState countState countAssignment _ countRun (Nat.le_refl _)]
  exact parentRun

end InitECandidate.Solver.WitnessRadix.PopProgram

#print axioms InitECandidate.Solver.WitnessRadix.PopProgram.pop_execute
