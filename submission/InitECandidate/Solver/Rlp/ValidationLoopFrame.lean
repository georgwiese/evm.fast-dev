import InitECandidate.Solver.Rlp.ValidationParseFrame
import InitECandidate.Solver.Rlp.ValidationLoop
import InitECandidate.Solver.Input.LoopInvariant

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Carry the actual ordinary-memory footprint through every normal original
loop iteration. The reached cursor never exceeds the incoming cursor, and
every word above that incoming cursor retains its original value. -/
theorem loop_none_outside (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rootEnd cursor limit position ending go : BitVec 64) (frames : List Frame)
    (view : View source rootEnd cursor limit position ending go frames)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source loop=(none,target)) :
    ∃ nextCursor,Arena target nextCursor limit ∧ nextCursor.toNat≤cursor.toNat ∧ Outside source target limit.toNat cursor.toNat := by
  let invariant := fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>
    Invariant rootEnd limit current ∧ (globalWord current "scratch_ptr").toNat≤cursor.toNat ∧ Outside source current limit.toNat cursor.toNat
  have initial : invariant source :=
    ⟨⟨cursor,position,ending,go,frames,view⟩,by simp only [globalWord,view.arena.cursorGlobal]; exact Nat.le_refl _,Outside.refl source limit.toNat cursor.toNat⟩
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      current.code=source.code → invariant current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) condition=some (.val (.word word)) →
      word≠0 → current.clock≠0 → ∀ post,
      evaluateHOLFiniteState (decClockHOLFinite current) loopBody=(none,post) → invariant post := by
    intro current codeEq model word read nonzero funded post bodyRun
    obtain ⟨currentCursor,currentPosition,currentEnding,currentGo,currentFrames,currentView⟩ := model.1
    have active := condition_active current currentGo word currentView.goCell currentView.binary read nonzero
    subst currentGo
    have entryView := View.clock current rootEnd currentCursor limit currentPosition currentEnding 1#64 currentFrames (current.clock-1) currentView
    have currentInstalled : Input.OriginalCode.Installed (decClockHOLFinite current).code := by change Input.OriginalCode.Installed current.code; rw [codeEq]; exact installed
    have next := (loop_body_none (decClockHOLFinite current) post rootEnd currentCursor limit currentPosition currentEnding currentFrames entryView currentInstalled bodyRun).1
    obtain ⟨nextCursor,nextArena,decreases,above⟩ := loop_body_none_outside (decClockHOLFinite current) post rootEnd currentCursor limit currentPosition currentEnding currentFrames entryView currentInstalled bodyRun
    have upper : currentCursor.toNat≤cursor.toNat := by
      have currentBound := model.2.1
      simpa only [globalWord,currentView.arena.cursorGlobal] using currentBound
    refine ⟨next,?_,?_⟩
    · simpa only [globalWord,nextArena.cursorGlobal] using decreases.trans upper
    · refine ⟨above.runtime.trans model.2.2.runtime, ?_⟩
      intro query beyond
      have currentOutside : query.toNat < limit.toNat ∨ currentCursor.toNat ≤ query.toNat := by
        rcases beyond with before | beyond
        · exact Or.inl before
        · exact Or.inr (upper.trans beyond)
      exact (above query currentOutside).trans (model.2.2 query beyond)
  rw [loop_shape] at normal
  have reached := Input.loop_invariant source.code (ofString "p") condition loopBody loop_body_prefix invariant progress source target rfl initial normal
  obtain ⟨nextCursor,nextPosition,nextEnding,nextGo,nextFrames,nextView⟩ := reached.1
  have bounded : nextCursor.toNat≤cursor.toNat := by simpa only [globalWord,nextView.arena.cursorGlobal] using reached.2.1
  exact ⟨nextCursor,nextView.arena,bounded,reached.2.2⟩

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.loop_none_outside
