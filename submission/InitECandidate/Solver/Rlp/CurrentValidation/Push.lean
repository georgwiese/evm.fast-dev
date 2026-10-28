import InitECandidate.Solver.Rlp.CurrentValidation.State
import InitECandidate.Solver.Input.ScratchVariableStore
import InitECandidate.Solver.Input.ScalarWordShape

namespace InitECandidate.Solver.Rlp.CurrentValidation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

/-- The actual nested-list push cannot continue. Its literal first store
uses raw rec, whose actual checked allocator return is a word. Its ordinary
address is below the current domain, even when scratch allocation succeeds. -/
theorem push_not_none (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arena : CurrentStartup.ArenaState source) (afterWord : BitVec 64)
    (afterCell : source.locals.lookup (ofString "after")=some (.val (.word afterWord)))
    (normal : evaluateHOLFiniteState source Validation.push=(none,post)) : False := by
  classical
  let rest : ProgHOL 64 := match Validation.pushStores with | .seq _ rest=>rest | _=>.skip
  change evaluateHOLFiniteState source (.decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 24#64]
    (.seq (.store (localVar "rec") (localVar "after")) rest))=(none,post) at normal
  obtain ⟨callee,called,amountCell⟩ := CallNormal.unary_environment source.code.lookup (ofString "scratch_alloc") "n"
    (Arenas.body .down) 24#64 (ScratchClear.allocator_installed source.code arena.code)
  obtain ⟨funded,target,returned,inner,allocation,checked,remaining,endpoint⟩ := CallNormal.scoped_none source post "rec" .one (ofString "scratch_alloc")
    [.const 24#64] [.val (.word 24#64)] (Arenas.body .down)
    (.seq (.store (localVar "rec") (localVar "after")) rest) callee .one rfl called normal
  have stopped:=ScratchStore.after_normal_variable_error source target callee 2701127680#64 2688618496#64 24 0 "rec" "after" afterWord rest returned
    (by decide) afterCell (by decide) (by decide) (by decide) (by decide) (by decide) arena.domain arena.code arena.scratch arena.frame amountCell allocation
  let ready:=CallNormal.continuationEntry source target "rec" returned
  have typed : shapeOfHOLExact returned=.one := (shapeEqHOL_eq_true _ _).mp (Bool.and_eq_true_iff.mp checked).1
  obtain ⟨pointer,valueEq⟩ := scalar_word_of_shape returned typed
  have cell : ready.locals.lookup (ofString "rec")=some (.val (.word pointer)) := by
    simp [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,valueEq]
  have read : eval ready (localVar "rec")=some (.val (.word pointer)) := by simp [eval,evalHOLExact,localVar,toExact,cell]
  have plusRead : eval ready (Scalar.plus (localVar "rec") 0)=some (.val (.word pointer)) :=
    by simpa only [BitVec.add_zero] using Scalar.plus_read ready (localVar "rec") pointer 0 read
  have same : evaluateHOLFiniteState ready (.store (localVar "rec") (localVar "after"))=
      evaluateHOLFiniteState ready (.store (Scalar.plus (localVar "rec") 0) (localVar "after")) := by
    simp only [eval] at read plusRead
    rw [evaluateHOLFiniteState_store,evaluateHOLFiniteState_store,read,plusRead]
  change evaluateHOLFiniteState ready (.seq (.store (Scalar.plus (localVar "rec") 0) (localVar "after")) rest)=(some .error,ready) at stopped
  change evaluateHOLFiniteState ready (.seq (.store (localVar "rec") (localVar "after")) rest)=(none,inner) at remaining
  rw [evaluateHOLFiniteState_seq_line780,same] at remaining
  rw [evaluateHOLFiniteState_seq_line780] at stopped
  rw [stopped] at remaining
  cases remaining

end InitECandidate.Solver.Rlp.CurrentValidation

#print axioms InitECandidate.Solver.Rlp.CurrentValidation.push_not_none
