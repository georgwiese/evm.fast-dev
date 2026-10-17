import InitECandidate.Solver.JumpDest.Branch

namespace InitECandidate.Solver.JumpDest
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

private theorem next_op_bind (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64) :
    eval (WitnessRadix.QueryBranch.bind source "op" word) nextByte = eval source nextByte := by
  simp [eval, nextByte, localVar, evalHOLExact, evalListHOLExact, toExact,
    WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString]
  rfl

def opExpression : ExpHOL 64 := .loadByte (.op .add [localVar "code", localVar "pc"])
noncomputable def stepMemory (memory : WitnessRadix.WordWrites.Memory)
    (bitmap opcode index old : BitVec 64) : WitnessRadix.WordWrites.Memory := by
  classical
  exact if opcode = 91#64 then WitnessRadix.StoreWord.put memory (bitmap + wordOffset index) (setBit old index) else memory
noncomputable def stepState (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bitmap opcode index length next old : BitVec 64) :=
  WitnessRadix.QueryBranch.bind {source with memory := stepMemory source.memory bitmap opcode index old}
    "pc" (index + selectedAdvance opcode index length next)

/-- One complete actual scan iteration, including both declarations,
conditional lookahead, optional bitmap write, PC assignment and lexical
restorations. Byte reads are actual expression premises, not an opcode oracle.
The following loop entry proof must supply them from its mapped code region. -/
theorem step_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bitmap opcode index length next old : BitVec 64)
    (bmLocal : source.locals.lookup (ofString "bm") = some (.val (.word bitmap)))
    (pcLocal : source.locals.lookup (ofString "pc") = some (.val (.word index)))
    (nLocal : source.locals.lookup (ofString "n") = some (.val (.word length)))
    (loaded : eval source opExpression = some (.val (.word opcode)))
    (loadedNext : index + 1#64 < length → eval source nextByte = some (.val (.word next)))
    (mapped : source.memaddrs (bitmap + wordOffset index))
    (cell : source.memory (bitmap + wordOffset index) = .word old) :
    evaluateHOLFiniteState source step = (none, stepState source bitmap opcode index length next old) := by
  classical
  let opState := WitnessRadix.QueryBranch.bind source "op" opcode
  let inner := WitnessRadix.QueryBranch.bind opState "adv" 1#64
  have opI : inner.locals.lookup (ofString "op") = some (.val (.word opcode)) :=
    (bind_lookup_other opState "adv" "op" _ (by decide)).trans (bind_lookup_same _ _ _)
  have pcI : inner.locals.lookup (ofString "pc") = some (.val (.word index)) :=
    (bind_lookup_other opState "adv" "pc" _ (by decide)).trans
      ((bind_lookup_other source "op" "pc" _ (by decide)).trans pcLocal)
  have nI : inner.locals.lookup (ofString "n") = some (.val (.word length)) :=
    (bind_lookup_other opState "adv" "n" _ (by decide)).trans
      ((bind_lookup_other source "op" "n" _ (by decide)).trans nLocal)
  have bmI : inner.locals.lookup (ofString "bm") = some (.val (.word bitmap)) :=
    (bind_lookup_other opState "adv" "bm" _ (by decide)).trans
      ((bind_lookup_other source "op" "bm" _ (by decide)).trans bmLocal)
  have loadedI : index + 1#64 < length → eval inner nextByte = some (.val (.word next)) := by
    intro following
    change eval (WitnessRadix.QueryBranch.bind opState "adv" 1#64) nextByte = _
    rw [next_bind, next_op_bind]
    exact loadedNext following
  have branchRun := branch_execute inner bitmap opcode index length next old bmI opI pcI nI
    (bind_lookup_same _ _ _) loadedI mapped cell
  let branched := branchState inner bitmap opcode index length next old
  have pcB : branched.locals.lookup (ofString "pc") = some (.val (.word index)) := by
    unfold branched branchState
    split
    · exact pcI
    · exact (bind_lookup_other inner "adv" "pc" _ (by decide)).trans pcI
  have advB : branched.locals.lookup (ofString "adv") = some (.val (.word (selectedAdvance opcode index length next))) := by
    unfold branched branchState
    split
    · rename_i isMark
      simpa only [selectedAdvance, if_pos isMark] using bind_lookup_same opState "adv" 1#64
    · exact bind_lookup_same _ _ _
  have clockB : branched.clock = inner.clock := by unfold branched branchState; split <;> rfl
  have pcRead : eval branched (.op .add [localVar "pc", localVar "adv"]) =
      some (.val (.word (index + selectedAdvance opcode index length next))) := by
    simp [eval, localVar, evalHOLExact, evalListHOLExact, toExact, pcB, advB,
      valueIsWord, valueWord, wordOpHOL, wordOp]
  have advanceRun := WitnessRadix.StateSteps.assign_execute branched "pc" _ index _ pcB pcRead
  have innerRun : evaluateHOLFiniteState inner (.seq branch advancePC) =
      (none, WitnessRadix.QueryBranch.bind branched "pc" (index + selectedAdvance opcode index length next)) := by
    rw [WitnessRadix.StateSteps.next_sequence inner branched _ _ branchRun (by rw [clockB])]
    exact advanceRun
  have advScope := Input.ScalarScope.declare_execute opState _ "adv" (.const 1#64) 1#64
    (.seq branch advancePC) none rfl innerRun
  have opScope := Input.ScalarScope.declare_execute source _ "op" opExpression opcode
    (.dec (ofString "adv") .one (.const 1#64) (.seq branch advancePC)) none loaded advScope
  change evaluateHOLFiniteState source step = _ at opScope
  rw [opScope]
  simp only [Prod.mk.injEq, true_and]
  rw [restore_bind_other opState branched "adv" "pc" _ (by decide)]
  rw [restore_bind_other source _ "op" "pc" _ (by decide)]
  unfold branched branchState
  split
  · rename_i isMark
    have restoreAdv : restore opState "adv" {inner with memory := stepMemory source.memory bitmap opcode index old} =
        {opState with memory := stepMemory source.memory bitmap opcode index old} := by
      change {restore opState "adv" inner with memory := stepMemory source.memory bitmap opcode index old} =
        {opState with memory := stepMemory source.memory bitmap opcode index old}
      rw [restore_bound opState "adv" 1#64]
    have restoreOp : restore source "op" {opState with memory := stepMemory source.memory bitmap opcode index old} =
        {source with memory := stepMemory source.memory bitmap opcode index old} := by
      change {restore source "op" opState with memory := stepMemory source.memory bitmap opcode index old} =
        {source with memory := stepMemory source.memory bitmap opcode index old}
      rw [restore_bound source "op" opcode]
    simp only [stepMemory, if_pos isMark] at restoreAdv restoreOp
    change WitnessRadix.QueryBranch.bind
      (restore source "op" (restore opState "adv" {inner with memory := (WitnessRadix.StoreWord.put source.memory
        (bitmap + wordOffset index) (setBit old index))})) "pc" (index + selectedAdvance opcode index length next) = _
    rw [restoreAdv, restoreOp]
    simp only [stepState, stepMemory, if_pos isMark]
  · rename_i notMark
    rw [bind_overwrite opState "adv" 1#64 (selectedAdvance opcode index length next),
      restore_bound opState "adv" (selectedAdvance opcode index length next), restore_bound source "op" opcode]
    simp only [stepState, stepMemory, if_neg notMark]

theorem step_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bitmap opcode index length next old : BitVec 64) :
    (stepState source bitmap opcode index length next old).clock = source.clock ∧
      (stepState source bitmap opcode index length next old).locals.lookup (ofString "pc") =
        some (.val (.word (index + selectedAdvance opcode index length next))) ∧
      (stepState source bitmap opcode index length next old).memaddrs = source.memaddrs :=
  ⟨rfl, bind_lookup_same _ _ _, rfl⟩

theorem step_away (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bitmap opcode index length next old query : BitVec 64)
    (inside : index.toNat < length.toNat) (below : bitmap.toNat + bitmapBytes length.toNat ≤ query.toNat) :
    (stepState source bitmap opcode index length next old).memory query = source.memory query := by
  unfold stepState
  change stepMemory source.memory bitmap opcode index old query = _
  unfold stepMemory
  split
  · exact marked_memory_away source.memory bitmap index query old length.toNat inside below
  · rfl

theorem step_outside (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bitmap opcode index length next old query : BitVec 64)
    (inside : index.toNat < length.toNat) (outside : Outside bitmap (bitmapBytes length.toNat) query) :
    (stepState source bitmap opcode index length next old).memory query = source.memory query := by
  unfold stepState
  change stepMemory source.memory bitmap opcode index old query = _
  unfold stepMemory
  split
  · exact if_neg (outside.selected bitmap query index length.toNat inside)
  · rfl

end InitECandidate.Solver.JumpDest

#print axioms InitECandidate.Solver.JumpDest.step_execute
#print axioms InitECandidate.Solver.JumpDest.step_fields
#print axioms InitECandidate.Solver.JumpDest.step_away

#print axioms InitECandidate.Solver.JumpDest.step_outside
