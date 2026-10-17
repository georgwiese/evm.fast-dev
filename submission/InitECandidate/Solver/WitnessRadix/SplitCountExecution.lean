import InitECandidate.Solver.WitnessRadix.SplitCountInputs
import InitECandidate.Solver.WitnessRadix.SplitScopePost

namespace InitECandidate.Solver.WitnessRadix.SplitCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch SplitScope

def post {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext) : PanSemStateFiniteExact 64 F :=
  SplitScope.post { source with clock := source.clock - context.input.length } context

/-- Count, choose the non-unary branch, stable-partition both arrays and push
its right task. All four scoped counters/cursors are restored. -/
theorem execute {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (premises : Inputs source context) :
    evaluateHOLFiniteState source TerminalProgram.remainingCode = (none, post source context) := by
  classical
  let zeroState := bind source "zeros" 0#64
  let entered := bind zeroState "i" 0#64
  have other : ∀ name : MlS, ofString "i" ≠ name → ofString "zeros" ≠ name →
      entered.locals.lookup name = source.locals.lookup name := by
    intro name ni nz
    simp [entered, zeroState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ni, nz]
  have locals' := task_locals_of_lookup source entered context other premises.locals
  have index' : entered.locals.lookup (ofString "i") = some (.val (.word 0#64)) :=
    bind_lookup_same zeroState "i" 0#64
  have zero' : entered.locals.lookup (ofString "zeros") = some (.val (.word 0#64)) := by
    rw [bind_lookup_other zeroState "i" "zeros" 0#64 (by decide)]
    exact bind_lookup_same source "zeros" 0#64
  have views' : ∀ ordinal ∈ context.input, MemoryBytes.ByteView entered
      (context.keys + ordinal * 32#64) (context.keyFor ordinal) := by
    intro ordinal member
    exact MemoryBytes.byteView_of_fields source entered rfl rfl rfl _ _ (premises.ready.views ordinal member)
  obtain ⟨target, countRun, finalIndex, finalZeros, counterOther, frame⟩ :=
    CountProgram.loop_execute context.input entered context.src (BitVec.ofNat 64 context.start) context.keys
      0#64 context.keyFor context.position 0 context.input.length premises.inside premises.small (Nat.zero_add _)
      locals'.srcLocal locals'.startLocal locals'.keysLocal locals'.bitLocal zero' index' locals'.countLocal
      premises.ready.rows views' (by change context.input.length ≤ source.clock; have := premises.enough; omega)
  have zerosTarget : target.locals.lookup (ofString "zeros") =
      some (.val (.word (BitVec.ofNat 64 (zeroCount context)))) := by
    simpa [zeroCount, CountProgram.zeroCount, ScatterProgram.zeros, ScatterProgram.keep] using finalZeros
  have localsTarget := task_locals_of_lookup entered target context counterOther locals'
  have clockEq : target.clock = source.clock - context.input.length := congrArg (fun state => state.clock) frame
  have memoryEq : source.memory = target.memory := (congrArg (fun state => state.memory) frame).symm
  have domainEq : source.memaddrs = target.memaddrs := (congrArg (fun state => state.memaddrs) frame).symm
  have endianEq : source.be = target.be := (congrArg (fun state => state.be) frame).symm
  have targetPremises : SplitScope.Inputs target context :=
    ⟨premises.inside, premises.fits, premises.allocation, (by rw [clockEq]; have := premises.enough; omega),
      localsTarget.srcLocal, localsTarget.dstLocal, localsTarget.keysLocal, finalIndex,
      entry_locals target context localsTarget zerosTarget,
      SplitProgram.mapped_of_field (source := source) (target := target) domainEq premises.mapped,
      ScatterProgram.ready_of_fields source target memoryEq domainEq endianEq _ _ _ _ _ _ _ _ premises.ready⟩
  have afterRun := after_count_split target context targetPremises premises.small premises.splitZero premises.splitOne
  have sequence : evaluateHOLFiniteState entered (.seq CountProgram.countLoop UnaryProgram.afterCount) =
      (none, SplitScope.post target context) :=
    (StateSteps.next_sequence entered target CountProgram.countLoop UnaryProgram.afterCount countRun
      (by change target.clock ≤ source.clock; omega)).trans afterRun
  have outside : ∀ query : MlS, query ≠ ofString "zeros" → query ≠ ofString "i" →
      target.locals.lookup query = source.locals.lookup query := by
    intro query nz ni
    exact (counterOther query (Ne.symm ni) (Ne.symm nz)).trans (other query (Ne.symm ni) (Ne.symm nz))
  have fields : emptyLocalsHOLFinite target =
      emptyLocalsHOLFinite { source with clock := source.clock - context.input.length } := by
    simpa only [entered, zeroState, QueryBranch.bind, setVarHOLFinite, emptyLocalsHOLFinite] using frame
  have restoredCounters : restore source "zeros" (restore zeroState "i" target) =
      { source with clock := source.clock - context.input.length } := by
    have savedI : zeroState.locals.lookup (ofString "i") = source.locals.lookup (ofString "i") :=
      bind_lookup_other source "zeros" "i" 0#64 (by decide)
    rw [restore_saved zeroState source target "i" savedI]
    exact restore_two_frame source target _ "zeros" "i" (by decide) outside rfl fields
  rw [UnaryProgram.remaining_shape, evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  change (let output := (evaluateHOLFiniteState zeroState
      (.dec (ofString "i") .one (.const 0#64) (.seq CountProgram.countLoop UnaryProgram.afterCount)));
    (output.1, restore source "zeros" output.2)) = _
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  change (let output := evaluateHOLFiniteState entered (.seq CountProgram.countLoop UnaryProgram.afterCount);
    (output.1, restore source "zeros" (restore zeroState "i" output.2))) = _
  rw [sequence]
  change (none, restore source "zeros" (restore zeroState "i" (SplitScope.post target context))) = _
  rw [restore_post zeroState target context "i" (by decide) (by decide) (by decide) (by decide) (by decide),
    restore_post source _ context "zeros" (by decide) (by decide) (by decide) (by decide) (by decide), restoredCounters]
  rfl

end InitECandidate.Solver.WitnessRadix.SplitCount

#print axioms InitECandidate.Solver.WitnessRadix.SplitCount.execute
