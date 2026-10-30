import InitECandidate.Solver.Rlp.ValidationChoose

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch


theorem push_none_outside (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rootEnd cursor limit position ending payload after : BitVec 64) (frames : List Frame)
    (view : View source rootEnd cursor limit position ending 1#64 frames)
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word payload)))
    (afterCell : source.locals.lookup (ofString "after")=some (.val (.word after)))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source push=(none,target)) :
    ∃ nextCursor,Arena target nextCursor limit ∧ nextCursor.toNat≤cursor.toNat ∧ Outside source target limit.toNat cursor.toNat := by
  obtain ⟨room,positive,same⟩ := push_none source target cursor limit position ending (topOf frames) payload after view.arena
    view.positionCell view.endCell view.topCell payloadCell afterCell installed normal
  obtain ⟨active,fits,below,lower,aligned⟩ := Arena.record_bounds source cursor limit view.arena room
  let pointer := Arenas.rounded .down cursor 24#64
  change pointer.toNat+24≤cursor.toNat at below
  rw [same]
  refine ⟨pointer,push_post_arena source cursor limit position ending (topOf frames) payload after view.arena room,by omega,?_⟩
  refine ⟨rfl, ?_⟩
  intro query outside
  change WitnessRadix.WordWrites.write source.memory (recordWrites pointer after ending (topOf frames)) query=source.memory query
  rcases outside with before | beyond
  · have lower := (Arenas.downward_guards cursor limit 24#64 view.arena.aligned room).2.2.1
    change limit.toNat ≤ pointer.toNat at lower
    exact record_lower_agreement source.memory pointer after ending (topOf frames) fits query (by omega)
  · exact record_upper_agreement source.memory pointer after ending (topOf frames) cursor.toNat fits below query beyond

theorem choose_none_outside (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rootEnd cursor limit position ending header headerPayload flag payload after : BitVec 64) (frames : List Frame)
    (view : View source rootEnd cursor limit position ending 1#64 frames)
    (hCell : source.locals.lookup (ofString "h")=some (Header.result header headerPayload flag))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word payload)))
    (afterCell : source.locals.lookup (ofString "after")=some (.val (.word after)))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source choose=(none,target)) :
    ∃ nextCursor,Arena target nextCursor limit ∧ nextCursor.toNat≤cursor.toNat ∧ Outside source target limit.toNat cursor.toNat := by
  rw [choose_evaluate source header headerPayload flag hCell] at normal
  by_cases zero : flag=0#64
  · rw [if_neg (not_not_intro zero)] at normal
    have readAfter : eval source (localVar "after")=some (.val (.word after)) := by simp [eval,evalHOLExact,localVar,toExact,afterCell]
    have assigned := WitnessRadix.StateSteps.assign_execute source "pos" (localVar "after") position after view.positionCell readAfter
    have same : target=bind source "pos" after := (Prod.mk.inj (normal.symm.trans assigned)).2
    rw [same]
    exact ⟨cursor,Arena.of_fields source _ cursor limit view.arena rfl rfl,Nat.le_refl _,⟨rfl,fun _ _=>rfl⟩⟩
  · rw [if_pos zero] at normal
    exact push_none_outside source target rootEnd cursor limit position ending payload after frames view payloadCell afterCell installed normal

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.Above.refl
#print axioms InitECandidate.Solver.Rlp.Validation.Above.trans
#print axioms InitECandidate.Solver.Rlp.Validation.push_none_outside
#print axioms InitECandidate.Solver.Rlp.Validation.choose_none_outside
