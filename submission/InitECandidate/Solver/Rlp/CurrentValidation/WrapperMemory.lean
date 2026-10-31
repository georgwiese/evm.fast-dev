import InitECandidate.Solver.Rlp.CurrentValidation.Wrapper
import InitECandidate.Solver.Rlp.ValidationGlobals

namespace InitECandidate.Solver.Rlp.CurrentValidate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

/-- The real public validator restores all globals, retains its runtime and
protects memory outside the temporary interval. Scratch bytes may change. -/
theorem body_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : LiveArena source) (fits : pointer.toNat+length.toNat<2^64)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ MemoryMetadata.erase post=MemoryMetadata.erase source ∧
      Validation.Outside source post 2952790016 2965299200 := by
  obtain ⟨cursor,limit,physical,lower,upper⟩:=arena.cursors
  obtain ⟨returned,nextArena,outside⟩:=Validate.body_normal_outside source post pointer length cursor limit
    pointerCell lengthCell physical fits arena.code value normal
  have globals : post.globals=source.globals := by
    apply HolFiniteMapExact.ext
    funext key
    by_cases scratch : key=ofString "scratch_ptr"
    · subst key
      exact nextArena.cursorGlobal.trans physical.cursorGlobal.symm
    · have preserved := Validate.globals key source.code arena.code scratch source rfl
      change GlobalEffects.erase key (evaluateHOLFiniteState source body).2=GlobalEffects.erase key source at preserved
      rw [normal] at preserved
      exact congrArg Prod.snd preserved
  have metadata := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    {state with globals:=source.globals}) outside.runtime
  change MemoryMetadata.erase {post with globals:=source.globals}=MemoryMetadata.erase source at metadata
  rw [←globals] at metadata
  exact ⟨returned,metadata,outside.widen lower upper⟩

end InitECandidate.Solver.Rlp.CurrentValidate

#print axioms InitECandidate.Solver.Rlp.CurrentValidate.body_normal_frame
