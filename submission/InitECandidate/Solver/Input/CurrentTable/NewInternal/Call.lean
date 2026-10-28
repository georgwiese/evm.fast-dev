import InitECandidate.Solver.Input.CurrentTable.NewInternal.NoGrow
import InitECandidate.Solver.Input.ScopedCallClassified
import InitECandidate.Solver.Input.CallResumeLookup
import InitECandidate.Solver.ClockPaddingFull
import InitECandidate.Solver.Input.WordPairEnvironment

namespace InitECandidate.Solver.Input.CurrentTable.NewInternal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

theorem normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap base node bit : BitVec 64)
    (ready : NewNode.Context source table node cap) (installed : OriginalCode.Installed source.code)
    (array : AllocatedBytes.Arena base (32*(cap.toNat+1))) (aligned : base.toNat%8 = 0)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (bitCell : source.locals.lookup (ofString "bit") = some (.val (.word bit)))
    (nodesCell : source.memory (table+40#64) = .word base) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source body = (some (.returned value),post)) :
    value = .val (.word node) ∧ 1 ≤ source.clock ∧ post.clock = source.clock-1 ∧
      LocalEffects.erase post = LocalEffects.erase (stored (New.putField source table 64 (node+1#64)) base node bit) := by
  let padded := {source with clock := source.clock+1}
  have context : NewNode.Context padded table node cap := ready.of_frame rfl
  have actual := body_execute padded table cap base node bit context installed array aligned tableCell bitCell nodesCell (by change 1 ≤ source.clock+1; omega)
  have lifted := panPropsEvaluateAddClockEq body source (some (.returned value)) post 1
    ⟨run,by intro impossible; cases impossible⟩
  have answer := congrArg Prod.fst (lifted.symm.trans actual)
  have answerEq : value = .val (.word node) := by
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using answer
  have endpoint := congrArg Prod.snd (lifted.symm.trans actual)
  dsimp only at endpoint
  have clock := congrArg PanSemStateFiniteExact.clock endpoint
  change post.clock+1 = source.clock+1-1 at clock
  have frame := congrArg LocalEffects.erase endpoint
  change LocalEffects.erase post = LocalEffects.erase (stored (New.putField source table 64 (node+1#64)) base node bit) at frame
  exact ⟨answerEq,by omega,by omega,frame⟩

/-- The real current internal-node scoped caller either stops within two
ticks or reaches its unchanged continuation with the actual physical writes. -/
theorem scoped_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap base node bit : BitVec 64)
    (ready : NewNode.Context source table node cap) (installed : OriginalCode.Installed source.code)
    (array : AllocatedBytes.Arena base (32*(cap.toNat+1))) (aligned : base.toNat%8 = 0)
    (nodesCell : source.memory (table+40#64) = .word base)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address => Classical.propDecidable (source.memaddrs address)) expressions =
      some [.val (.word table),.val (.word bit)])
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_new_internal") expressions continuation) = (outcome,post)) :
    (source.clock-post.clock ≤ 2 ∧ ∀ value,outcome ≠ some (.returned value)) ∨
      ∃ target inner,LocalEffects.erase target = LocalEffects.erase (stored (New.putField source table 64 (node+1#64)) base node bit) ∧
        target.clock ≤ source.clock ∧ source.clock-target.clock ≤ 2 ∧
        evaluateHOLFiniteState (CallNormal.continuationEntry source target name (.val (.word node))) continuation = (outcome,inner) ∧
        post = restore source name inner := by
  classical
  obtain ⟨callee,called,tableCell,bitCell⟩ := word_pair_environment source.code.lookup (ofString "htab_new_internal")
    (ofString "t") (ofString "bit") body .one table bit (by decide) (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have context : NewNode.Context entry table node cap := ready.of_frame rfl
  rcases CallNormal.scoped_classified source post name .one (ofString "htab_new_internal") expressions _ body continuation callee .one 1
    args called (price entry table cap base node bit context installed array aligned tableCell bitCell nodesCell) outcome run with stopped | reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩ := reached
    obtain ⟨answer,paid,clock,frame⟩ := normal entry target table cap base node bit context installed array aligned tableCell bitCell nodesCell value bodyRun
    rw [answer] at continued
    exact Or.inr ⟨target,inner,frame,forward,cost,continued,endpoint⟩

end InitECandidate.Solver.Input.CurrentTable.NewInternal

#print axioms InitECandidate.Solver.Input.CurrentTable.NewInternal.normal
#print axioms InitECandidate.Solver.Input.CurrentTable.NewInternal.scoped_trace
