import InitECandidate.Solver.Mpt.CurrentWitnessDecodeLeaf
import InitECandidate.Solver.Mpt.WitnessDecodeRecursiveCuts
import InitECandidate.Solver.Input.ConditionalNone
import InitECandidate.Solver.Input.NoFallthrough
import InitECandidate.Solver.Input.ScopedCallData

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem leaf_body_no_fallthrough : NoFallthrough leafBody := by
  rw [value_shape]
  apply NoFallthrough.scoped
  rw [after_value_shape]
  apply NoFallthrough.sequence
  rw [leaf_shape]
  apply NoFallthrough.scoped
  rw [after_leaf_shape]
  exact NoFallthrough.sequence _ _ (NoFallthrough.sequence _ _ (NoFallthrough.returned _))

/-- Both real compact branches return only flag0: the leaf returns flag0,
and the extension cannot return its first recursive scratch frame. -/
theorem after_compact_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arena : CurrentStartup.ArenaState source) : ReturnFacts.Returns source afterCompact ZeroResult := by
  rw [after_compact_shape]
  apply ReturnFacts.sequence
  · exact ReturnFacts.conditional source _ _ _ ZeroResult (leaf_body_zero source) (ReturnFacts.skip source ZeroResult)
  · intro middle normal
    have same : middle=source := by
      rcases conditional_none source middle _ leafBody .skip normal with yes|no
      · exact (leaf_body_no_fallthrough source (congrArg Prod.fst yes)).elim
      · rw [evaluateHOLFiniteState_skip] at no
        exact (congrArg Prod.snd no).symm
    subst middle
    intro post value returned
    exact (extension_body_no_return source post arena value returned).elim

/-- The actual compact constructor supplies the arena used by its real
continuation. The flag argument need not be guessed in advance. -/
theorem compact_call_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arena : CurrentStartup.ArenaState source) : ReturnFacts.Returns source compactCall ZeroResult := by
  intro post value normal
  rw [compact_shape] at normal
  obtain ⟨funded,values,actualBody,callee,shape,target,returned,inner,args,called,bodyRun,checked,continued,endpoint⟩:=
    CallNormal.scoped_data source post "cn" (.comb [.one,.one,.one]) (ofString "compact_to_nibbles") [field "pi" 1,field "pi" 2] afterCompact value normal
  have same:=LocalEffects.lookup_body source.code (ofString "compact_to_nibbles") CompactToNibbles.formals CompactToNibbles.body CompactToNibbles.resultShape
    (CompactToNibbles.original_code source.code arena.code) values actualBody callee shape called
  rw [same] at bodyRun
  have targetArena:=CompactToNibbles.current_arena (callEntryStateHOLFinite source callee) target (arena.of_frame rfl) _ bodyRun
  let ready:=CallNormal.continuationEntry source target "cn" returned
  have readyArena : CurrentStartup.ArenaState ready:=targetArena.of_frame rfl
  exact after_compact_zero ready readyArena inner value continued

theorem after_path_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arena : CurrentStartup.ArenaState source) : ReturnFacts.Returns source afterPath ZeroResult := by
  intro post value normal
  rw [after_path_shape] at normal
  have continued:=(Fail.guard_return source post _ [.const 5#64] compactCall value arena.code normal).2
  exact compact_call_zero source arena post value continued

/-- The first actual RLP row call preserves the current arena before its
compact/leaf suffix. Every genuine two-item node result therefore has flag0. -/
theorem current_pair_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (rows : Rows source array pointer bytes items) (selected : items[0]?=some item)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (arena : CurrentStartup.ArenaState source) : ReturnFacts.Returns source pairBody ZeroResult := by
  intro post value normal
  obtain ⟨args,positive,small,lower,upper⟩:=rows.arguments source array pointer bytes 0 items item selected arrayCell
  have fits : (Rlp.Slices.itemPointer pointer items 0).toNat+item.total.toNat<2^64 := by have h:=rows.fits; omega
  rw [path_shape] at normal
  obtain ⟨answer,clock,inner,valid,forward,cost,continued,endpoint⟩:=Rlp.CurrentItem.scoped_normal source post
    (Rlp.Slices.itemPointer pointer items 0) item.total arena fits "pi" (recordArguments 0) afterPath args value normal
  let ready:=setVarHOLFinite (ofString "pi") answer {source with clock:=clock}
  have readyArena : CurrentStartup.ArenaState ready:=arena.of_frame rfl
  exact after_path_zero ready readyArena inner value continued

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.after_compact_zero
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_pair_zero
