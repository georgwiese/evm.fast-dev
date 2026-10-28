import InitECandidate.Solver.Input.CurrentHash.MerkleDenseCost
import InitECandidate.Solver.Input.CurrentHash.MerklePairMemory

namespace InitECandidate.Solver.Input.CurrentHash.MerkleDenseMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open MerkleDenseCost

/-- Both lexical counter declarations and the actual half-pair loop stay
inside the same allocated buffer; assigning cur changes no protected word. -/
theorem step_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer query : BitVec 64) (cur capacity : Nat)
    (small : capacity<2^63) (inside : cur≤capacity) (installed : OriginalCode.Installed source.code)
    (pointer : source.locals.lookup (ofString "buf") = some (.val (.word buffer)))
    (current : source.locals.lookup (ofString "cur") = some (.val (.word (BitVec.ofNat 64 cur))))
    (away : CopyGeneral.Away buffer query (32*capacity))
    (actual : evaluateHOLFiniteState source step = (none,post)) : post.memory query = source.memory query := by
  rw [source_shape.2] at actual
  obtain ⟨halfPost,halfRun,endpoint⟩ := declaration_none source post "half" halfExpression (BitVec.ofNat 64 (cur/2)) afterHalf
    (half_read source cur (by omega) current) actual
  change evaluateHOLFiniteState (halfEntry source cur) (.dec (ofString "j") .one (.const 0#64) innerTail) = (none,halfPost) at halfRun
  obtain ⟨rawPost,bodyRun,halfEndpoint⟩ := declaration_none (halfEntry source cur) halfPost "j" (.const 0#64) 0#64 innerTail rfl halfRun
  change evaluateHOLFiniteState (innerEntry source cur) (.seq (MerklePairLoops.loop .dense) assignment) = (none,rawPost) at bodyRun
  obtain ⟨middle,normal,assigned⟩ := Input.sequence_none (innerEntry source cur) rawPost _ _ bodyRun
  have nextPointer : (innerEntry source cur).locals.lookup (ofString "buf") = some (.val (.word buffer)) :=
    (bind_lookup_other _ "j" "buf" _ (by decide)).trans ((bind_lookup_other source "half" "buf" _ (by decide)).trans pointer)
  have halfCell : (innerEntry source cur).locals.lookup (ofString "half") = some (.val (.word (BitVec.ofNat 64 (cur/2)))) :=
    (bind_lookup_other _ "j" "half" _ (by decide)).trans (bind_lookup_same source "half" _)
  have loopFrame := MerklePairMemory.loop_memory .dense (innerEntry source cur) middle buffer query 0 (cur/2)
    (by omega) (by omega) installed nextPointer (bind_lookup_same _ _ _) halfCell (by
      intro j active
      exact CopyGeneral.Away.subrange buffer query (32*capacity) (32*j) 32 away (by omega)) normal
  have pureAssignment := MemoryAt.assign_current middle .local (ofString "cur") (localVar "half") query
  change evaluateHOLFiniteState middle (.assign .local (ofString "cur") (localVar "half")) = (none,rawPost) at assigned
  rw [assigned] at pureAssignment
  rw [endpoint,halfEndpoint]
  exact pureAssignment.trans loopFrame

/-- The whole actual shrinking dense loop preserves metadata outside its
buffer. Each same-trace normal body derives the next half count. -/
theorem loop_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer query : BitVec 64) (cur capacity : Nat)
    (small : capacity<2^63) (positive : 1≤cur) (inside : cur≤capacity) (installed : OriginalCode.Installed source.code)
    (pointer : source.locals.lookup (ofString "buf") = some (.val (.word buffer)))
    (current : source.locals.lookup (ofString "cur") = some (.val (.word (BitVec.ofNat 64 cur))))
    (away : CopyGeneral.Away buffer query (32*capacity))
    (actual : evaluateHOLFiniteState source loop = (none,post)) : post.memory query = source.memory query := by
  let ready := fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    state.locals.lookup (ofString "buf") = some (.val (.word buffer)) ∧ invariant capacity state
  rw [source_shape.1] at actual
  apply MemoryAt.loop_normal source.code (ofString "buf") (.cmp .less (.const 1#64) (localVar "cur")) step query
    ((other (ofString "buf") (by decide) (by decide) (by decide)).summary_full) ready _ source post rfl
    ⟨pointer,cur,positive,inside,current⟩ actual
  intro state codeEq stateReady word read nonzero funded target normal
  obtain ⟨pointer,position,positive,inside,current⟩ := stateReady
  have expected := test_read state position (by omega) current
  have active : 1<position := by
    by_cases active : 1<position
    · exact active
    rw [if_neg active] at expected
    have zero : word=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
    exact False.elim (nonzero zero)
  have currentCode : OriginalCode.Installed state.code := by rw [codeEq]; exact installed
  have next := halves (decClockHOLFinite state) target position (by omega) current normal
  have summary := (other (ofString "buf") (by decide) (by decide) (by decide)).summary_full (decClockHOLFinite state)
  unfold LocalSummary at summary
  rw [normal] at summary
  exact ⟨⟨(summary.1 rfl).trans pointer,position/2,by omega,by omega,next⟩,
    step_memory (decClockHOLFinite state) target buffer query position capacity small inside currentCode pointer current away normal⟩

theorem step_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code step := by
  rw [source_shape.2]
  exact GlobalEffects.declared key code _ _ _ _
    (GlobalEffects.declared key code _ _ _ _
      (GlobalEffects.sequence key code _ _ (MerklePairLoops.globals .dense key code installed) (GlobalEffects.assign key code _ _)))

theorem loop_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code loop := by
  rw [source_shape.1]
  exact GlobalEffects.loop key code _ _ (step_globals key code installed)

end InitECandidate.Solver.Input.CurrentHash.MerkleDenseMemory

#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleDenseMemory.step_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleDenseMemory.loop_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleDenseMemory.step_globals
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleDenseMemory.loop_globals
