import InitECandidate.Solver.Mpt.InsertEmptyFinish
import InitECandidate.Solver.Mpt.NodeConstructorCost
import InitECandidate.Solver.Input.ClockCostCurrentLoop

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem after_choice_local (key : MlS) (notResult : key≠ofString "result") (notNode : key≠ofString "node")
    (notSlot : key≠ofString "slot") (notLevel : key≠ofString "level") : Input.LocalPrefix key afterChoice := by
  rw [after_choice_shape]
  exact .seq (.ite _ (.assign _ _ notResult) (.store _ _))
    (.seq (.assign _ _ notNode) (.seq (.assign _ _ notSlot) (.assign _ _ notLevel)))

theorem after_choice_quiet (code) : Input.QuietClock.Preserves code afterChoice := by
  rw [after_choice_shape]
  exact Input.QuietClock.sequence code _ _
    (Input.QuietClock.conditional code _ _ _ (Input.QuietClock.assign code _ _) (Input.QuietClock.store code _ _))
    (Input.QuietClock.sequence code _ _ (Input.QuietClock.assign code _ _)
      (Input.QuietClock.sequence code _ _ (Input.QuietClock.assign code _ _) (Input.QuietClock.assign code _ _)))

/-- The actual empty-node traversal body spends at most three ticks;
every normal continuation clears go, even if unrelated ABI reads can fail. -/
theorem empty_iteration_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (go : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word 0#64)))
    (goCell : source.locals.lookup (ofString "go")=some (.val (.word go)))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source loopBody).2.clock≤3 ∧
      ((evaluateHOLFiniteState source loopBody).1=none →
        (evaluateHOLFiniteState source loopBody).2.locals.lookup (ofString "go")=some (.val (.word 0#64))) := by
  let ready:=dispatchEntry source
  have trace:=prefix_execution source go goCell
  have projected:=trace.project (.seq nodeChoice afterChoice)
  rw [←iteration_shape] at projected
  have readyNode : ready.locals.lookup (ofString "node")=some (.val (.word 0#64)):=by
    simpa [ready,dispatchEntry,prepared,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using nodeCell
  have chosen:=empty_choice ready readyNode
  have leafPrice : Input.ClockCost.Bound source.code leafCall 3:=
    Input.ClockCost.call_body source.code (some (some (ofString "r"))) (ofString "node_new_leaf") leafArguments
      (NodeConstructor.formals .leaf) (NodeConstructor.body .leaf) .one 2
      (NodeConstructor.original_code .leaf source.code installed) (NodeConstructor.scalar_body_price .leaf (by decide) source.code installed)
  have readyPrice:=Input.ClockCost.sequence_current ready nodeChoice afterChoice 3 0
    (by rw [chosen]; exact leafPrice ready rfl) (Input.ClockCost.of_quiet ready.code afterChoice (after_choice_quiet ready.code))
  have clockEq:=congrArg Prod.snd projected
  change (evaluateHOLFiniteState source loopBody).2.clock=(evaluateHOLFiniteState ready (.seq nodeChoice afterChoice)).2.clock at clockEq
  refine ⟨?_,?_⟩
  · rw [clockEq]
    exact readyPrice
  · intro normal
    have resultEq:=congrArg Prod.fst projected
    change (evaluateHOLFiniteState source loopBody).1=(evaluateHOLFiniteState ready (.seq nodeChoice afterChoice)).1 at resultEq
    have continued : (evaluateHOLFiniteState ready (.seq nodeChoice afterChoice)).1=none:=resultEq.symm.trans normal
    have suffix : Input.LocalPrefix (ofString "go") (.seq leafCall afterChoice):=
      .seq (.call (some (ofString "r")) _ _ (by intro name same; have equal:=Option.some.inj same; subst name; decide))
        (after_choice_local _ (by decide) (by decide) (by decide) (by decide))
    have suffixEq : evaluateHOLFiniteState ready (.seq nodeChoice afterChoice)=evaluateHOLFiniteState ready (.seq leafCall afterChoice):=by
      simp only [evaluateHOLFiniteState_seq_line780,chosen]
    have frame:=suffix.summary_full ready
    have suffixNormal : (evaluateHOLFiniteState ready (.seq leafCall afterChoice)).1=none:=by rwa [suffixEq] at continued
    have localEq:=trace.local_result (ofString "go")
      (by simp [iterationActions,Input.CallPrefix.Action.avoids,ofString]) (.seq nodeChoice afterChoice)
    rw [←iteration_shape] at localEq
    rw [localEq,suffixEq,frame.1 suffixNormal]
    exact bind_lookup_same (prepared source) "go" 0#64

def EmptyInvariant (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop:=
  ∃ go : BitVec 64,source.locals.lookup (ofString "go")=some (.val (.word go)) ∧
    (go≠0#64 → source.locals.lookup (ofString "node")=some (.val (.word 0#64)))
noncomputable def emptyRank (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat:=by
  classical
  exact if source.locals.lookup (ofString "go")=some (.val (.word 0#64)) then 0 else 1

theorem empty_active (source : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : EmptyInvariant source) (word : BitVec 64)
    (read : evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) test=some (.val (.word word)))
    (nonzero : word≠0#64) :
    ∃ go,source.locals.lookup (ofString "go")=some (.val (.word go)) ∧
      source.locals.lookup (ofString "node")=some (.val (.word 0#64)) ∧ emptyRank source=1 := by
  obtain ⟨go,goCell,node⟩:=valid
  have active : go≠0#64:=by
    intro same
    have zero : word=0#64:=by
      simpa [test,localVar,evalHOLFinite,evalHOLExact,toExact,goCell,same,Flapjack.Compiler.Encoders.Asm.wordCmpHOL] using read.symm
    exact nonzero zero
  exact ⟨go,goCell,node active,by simp [emptyRank,goCell,active]⟩

/-- The empty root uses exactly one possible traversal iteration. Failed
reads, allocation guards and insufficient clocks are covered as well. -/
theorem empty_body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word 0#64)))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤4 := by
  have priced:=Input.ClockCost.ranked_loop_current source.code test loopBody 3 EmptyInvariant emptyRank
    (by
      intro current codeEq valid word read nonzero funded
      obtain ⟨go,goCell,node,rank⟩:=empty_active current valid word read nonzero
      exact (empty_iteration_cost (decClockHOLFinite current) go node goCell (by rw [show (decClockHOLFinite current).code=source.code from codeEq]; exact installed)).1)
    (by
      intro current codeEq valid word read nonzero
      obtain ⟨go,goCell,node,rank⟩:=empty_active current valid word read nonzero
      refine ⟨by rw [rank]; decide,?_⟩
      intro funded
      dsimp only
      intro continuing
      have summary:=loop_body_safe.summary_full (decClockHOLFinite current)
      have normal : (evaluateHOLFiniteState (decClockHOLFinite current) loopBody).1=none:=continuing.resolve_right summary.2.2.2
      have zeroGo:=(empty_iteration_cost (decClockHOLFinite current) go node goCell (by rw [show (decClockHOLFinite current).code=source.code from codeEq]; exact installed)).2 normal
      exact ⟨⟨0#64,zeroGo,by intro impossible; exact (impossible rfl).elim⟩,by rw [rank]; simp [emptyRank,zeroGo]⟩)
    (setup source) rfl ⟨1#64,(setup_locals source).2.2,by intro active; exact (setup_saved source _ (by decide) (by decide) (by decide)).trans nodeCell⟩
  have rankOne : emptyRank (setup source)=1:=by simp [emptyRank,(setup_locals source).2.2]
  rw [rankOne] at priced
  rw [body_shape]
  simp only [actions,Input.CallPrefix.program]
  apply Input.ClockCost.declared_current source "result" (.const 0#64) 0#64 _ 4 rfl
  apply Input.ClockCost.declared_current _ "slot" (.const 0#64) 0#64 _ 4 rfl
  apply Input.ClockCost.declared_current _ "go" (.const 1#64) 1#64 _ 4 rfl
  rw [loop_shape]
  exact Input.ClockCost.sequence_current (setup source) _ _ 4 0 priced (Input.ClockCost.returned source.code _)

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.empty_iteration_cost
#print axioms InitECandidate.Solver.Mpt.Insert.after_choice_local
#print axioms InitECandidate.Solver.Mpt.Insert.after_choice_quiet
#print axioms InitECandidate.Solver.Mpt.Insert.empty_active
#print axioms InitECandidate.Solver.Mpt.Insert.empty_body_cost
