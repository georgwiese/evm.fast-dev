import InitECandidate.Solver.Input.MerkleInnerMemory
import InitECandidate.Solver.Input.MerkleOuterLoop

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem outer_step_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor stp accel query : BitVec 64) (cur capacity : Nat)
    (inside : cur≤capacity) (arena : AllocatedBytes.Arena cursor (32*capacity)) (workspace : ShaPair.Workspace source stp accel)
    (current : source.locals.lookup (ofString "cur")=some (.val (.word (BitVec.ofNat 64 cur))))
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (stateAway : CopyGeneral.Away stp query 64) (accelAway : CopyGeneral.Away accel query 96) (bufferAway : CopyGeneral.Away cursor query (32*capacity))
    (run : evaluateHOLFiniteState source outerStep=(none,post)) : post.memory query=source.memory query := by
  have upper := arena.upper
  have small : cur<2^64 := by omega
  have halfSmall : cur/2<2^63 := by omega
  rw [outer_shape.2.1] at run
  obtain ⟨halfPost,halfRun,endpoint⟩ := declaration_none source post "half" halfExpression (BitVec.ofNat 64 (cur/2)) afterHalf (half_read source cur small current) run
  change evaluateHOLFiniteState (halfEntry source cur) (.dec (ofString "j") .one (.const 0#64) outerInnerTail)=(none,halfPost) at halfRun
  obtain ⟨rawPost,bodyRun,halfEndpoint⟩ := declaration_none (halfEntry source cur) halfPost "j" (.const 0#64) 0#64 outerInnerTail rfl halfRun
  change evaluateHOLFiniteState (innerEntry source cur) (.seq innerLoop outerAssign)=(none,rawPost) at bodyRun
  obtain ⟨innerPost,innerRun,assigned⟩ := sequence_none (innerEntry source cur) rawPost innerLoop outerAssign bodyRun
  have currentWorkspace := ShaPair.Workspace.of_fields source (innerEntry source cur) stp accel workspace rfl rfl rfl rfl
  have bufferCell : (innerEntry source cur).locals.lookup (ofString "buf")=some (.val (.word cursor)) :=
    (bind_lookup_other _ "j" "buf" _ (by decide)).trans ((bind_lookup_other source "half" "buf" _ (by decide)).trans buffer)
  have halfCell : (innerEntry source cur).locals.lookup (ofString "half")=some (.val (.word (BitVec.ofNat 64 (cur/2)))) :=
    (bind_lookup_other _ "j" "half" _ (by decide)).trans (bind_lookup_same source "half" _)
  have smaller := AllocatedBytes.Arena.weaken cursor (32*capacity) (64*(cur/2)) arena (by omega)
  have smallerAway : CopyGeneral.Away cursor query (64*(cur/2)) := by
    simpa only [BitVec.add_zero] using CopyGeneral.Away.subrange cursor query (32*capacity) 0 (64*(cur/2)) bufferAway (by omega)
  have innerFrame := inner_loop_memory (innerEntry source cur) innerPost cursor stp accel query 0 (cur/2) halfSmall (by omega) currentWorkspace smaller bufferCell (bind_lookup_same _ _ _) halfCell stateAway accelAway smallerAway innerRun
  have lastFrame := MemoryAt.assign_current innerPost .local (ofString "cur") (localVar "half") query
  change evaluateHOLFiniteState innerPost (.assign .local (ofString "cur") (localVar "half"))=(none,rawPost) at assigned
  rw [assigned] at lastFrame
  rw [endpoint,halfEndpoint]
  exact lastFrame.trans innerFrame

/-- Actual normal dense halving rounds preserve the protected word and
use the real smaller pair counts; arbitrary computed hashes are allowed. -/
theorem outer_loop_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor stp accel query : BitVec 64) (cur capacity : Nat)
    (positive : 1≤cur) (inside : cur≤capacity) (arena : AllocatedBytes.Arena cursor (32*capacity)) (workspace : ShaPair.Workspace source stp accel)
    (current : source.locals.lookup (ofString "cur")=some (.val (.word (BitVec.ofNat 64 cur))))
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (stateAway : CopyGeneral.Away stp query 64) (accelAway : CopyGeneral.Away accel query 96) (bufferAway : CopyGeneral.Away cursor query (32*capacity))
    (run : evaluateHOLFiniteState source outerLoop=(none,post)) : post.memory query=source.memory query := by
  rw [outer_shape.1] at run
  apply MemoryAt.loop_normal source.code (ofString "buf") outerTest outerStep query
    (outer_other (ofString "buf") (by decide) (by decide) (by decide)).summary_full (outerValid cursor stp accel capacity) _ source post rfl ⟨cur,positive,inside,current,buffer,workspace⟩ run
  intro state codeEq actual word read nonzero funded target bodyRun
  obtain ⟨count,countPositive,countBound,countCell,bufferCell,currentWorkspace⟩ := actual
  have upper := arena.upper
  have expected := outer_test_read state count (by omega) countCell
  have active : 1<count := by
    by_contra inactive
    rw [if_neg inactive] at expected
    have zero : word=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
    exact nonzero zero
  have nextCur := outer_advances (decClockHOLFinite state) target count (by omega) countCell bodyRun
  have summary := (outer_other (ofString "buf") (by decide) (by decide) (by decide)).summary_full (decClockHOLFinite state)
  unfold LocalSummary at summary
  rw [bodyRun] at summary
  have nextBuffer := (summary.1 rfl).trans bufferCell
  have entryWorkspace := ShaPair.Workspace.of_fields state (decClockHOLFinite state) stp accel currentWorkspace rfl rfl rfl rfl
  have nextWorkspace := outer_workspace (decClockHOLFinite state) target stp accel entryWorkspace none bodyRun
  exact ⟨⟨count/2,by omega,by omega,nextCur,nextBuffer,nextWorkspace⟩,
    outer_step_memory (decClockHOLFinite state) target cursor stp accel query count capacity countBound arena entryWorkspace countCell bufferCell stateAway accelAway bufferAway bodyRun⟩

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.outer_step_memory
#print axioms InitECandidate.Solver.Input.Merkle.outer_loop_memory
