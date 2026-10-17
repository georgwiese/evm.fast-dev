import InitECandidate.Solver.WitnessRadix.AllocationBody
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.WitnessRadix.SplitProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

structure EntryLocals {F : Type} (source : PanSemStateFiniteExact 64 F)
    (node depth start count zeros bit dest pendingStart pendingCount pendingNode : BitVec 64) : Prop where
  nextLocal : source.locals.lookup (ofString "node_next") = some (.val (.word node))
  depthLocal : source.locals.lookup (ofString "depth") = some (.val (.word depth))
  startLocal : source.locals.lookup (ofString "start") = some (.val (.word start))
  countLocal : source.locals.lookup (ofString "count") = some (.val (.word count))
  zerosLocal : source.locals.lookup (ofString "zeros") = some (.val (.word zeros))
  bitLocal : source.locals.lookup (ofString "bit") = some (.val (.word bit))
  destLocal : source.locals.lookup (ofString "dest") = some (.val (.word dest))
  pendingStartLocal : source.locals.lookup (ofString "pending_start") = some (.val (.word pendingStart))
  pendingCountLocal : source.locals.lookup (ofString "pending_count") = some (.val (.word pendingCount))
  pendingNodeLocal : source.locals.lookup (ofString "pending_node") = some (.val (.word pendingNode))

theorem entry_environment {F : Type} (source : PanSemStateFiniteExact 64 F)
    (node depth start count zeros bit dest pendingStart pendingCount pendingNode : BitVec 64)
    (locals : EntryLocals source node depth start count zeros bit dest pendingStart pendingCount pendingNode) :
    Locals (bind source "node" node) node depth start count zeros bit dest pendingStart pendingCount pendingNode := by
  have other (name : String) (neq : ofString "node" ≠ ofString name) := bind_lookup_other source "node" name node neq
  exact ⟨bind_lookup_same source "node" node,
    (other _ (by decide)).trans locals.nextLocal,
    (other _ (by decide)).trans locals.depthLocal,
    (other _ (by decide)).trans locals.startLocal,
    (other _ (by decide)).trans locals.countLocal,
    (other _ (by decide)).trans locals.zerosLocal,
    (other _ (by decide)).trans locals.bitLocal,
    (other _ (by decide)).trans locals.destLocal,
    (other _ (by decide)).trans locals.pendingStartLocal,
    (other _ (by decide)).trans locals.pendingCountLocal,
    (other _ (by decide)).trans locals.pendingNodeLocal⟩

theorem restore_branch_node {F : Type} (saved state : PanSemStateFiniteExact 64 F)
    (node depth start count zeros bit dest pendingStart pendingCount pendingNode : BitVec 64) :
    restore saved "node" (branchPost state node depth start count zeros bit dest pendingStart pendingCount pendingNode) =
      branchPost (restore saved "node" state) node depth start count zeros bit dest pendingStart pendingCount pendingNode := by
  unfold branchPost
  rw [restore_bind_other saved _ "node" "bit" _ (by decide),
    restore_bind_other saved _ "node" "dest" _ (by decide),
    restore_bind_other saved _ "node" "count" _ (by decide),
    restore_bind_other saved _ "node" "depth" _ (by decide),
    restore_bind_other saved _ "node" "node_next" _ (by decide)]
  rfl

/-- Complete literal branch allocation/push including the scoped node capture.
The exact seven-word memory update and five persistent locals are exposed. -/
theorem allocation_execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (node depth start count zeros bit dest pendingStart pendingCount pendingNode : BitVec 64)
    (locals : EntryLocals source node depth start count zeros bit dest pendingStart pendingCount pendingNode)
    (mapped : Mapped source node depth dest pendingStart pendingCount pendingNode) :
    evaluateHOLFiniteState source allocationCode =
      (none, branchPost source node depth start count zeros bit dest pendingStart pendingCount pendingNode) := by
  classical
  let nodeState := bind source "node" node
  have locals' := entry_environment source node depth start count zeros bit dest pendingStart pendingCount pendingNode locals
  have mapped' : Mapped nodeState node depth dest pendingStart pendingCount pendingNode :=
    ⟨mapped.nodeMapped, mapped.zeroMapped, mapped.oneMapped, mapped.destMapped,
      mapped.startMapped, mapped.countMapped, mapped.parentMapped⟩
  have bodyRun := body_execute nodeState node depth start count zeros bit dest pendingStart pendingCount pendingNode locals' mapped'
  have nextRead : eval source (localVar "node_next") = some (.val (.word node)) := by
    simp [eval, localVar, evalHOLExact, toExact, locals.nextLocal]
  simp only [eval] at nextRead
  rw [allocation_shape, evaluateHOLFiniteState_dec_total]
  simp only [nextRead, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  change (let output := evaluateHOLFiniteState nodeState allocationBody;
    (output.1, restore source "node" output.2)) = _
  rw [bodyRun]
  change (none, restore source "node" (branchPost nodeState node depth start count zeros bit dest pendingStart pendingCount pendingNode)) = _
  rw [restore_branch_node]
  have restored : restore source "node" nodeState = source := restore_bound _ _ _
  rw [restored]

end InitECandidate.Solver.WitnessRadix.SplitProgram

#print axioms InitECandidate.Solver.WitnessRadix.SplitProgram.allocation_execute
