import InitECandidate.Solver.Input.Requests.CountLocals
import InitECandidate.Solver.Input.FixedList.CallerTrace
import InitECandidate.Solver.Input.DecoderRuntimeCode

namespace InitECandidate.Solver.Input.Requests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

structure CountsDone (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (words : Nat → BitVec 64) (total pointer cursor : BitVec 64)
    (index : Nat) (counts : Nat → BitVec 64) : Prop where
  model : CountLocals target words total pointer cursor
  bindings : ∀ position,index ≤ position → position < 5 → target.locals.lookup (ofString (countName position)) = some (.val (.word (counts position)))
  arithmetic : ∀ position,index ≤ position → position < 5 → (counts position).toNat = (countSpan words total position).toNat / (elementSize position).toNat ∧
    (countSpan words total position).toNat % (elementSize position).toNat = 0
  other : ∀ key,(∀ position,index ≤ position → position < 5 → key ≠ ofString (countName position)) → target.locals.lookup key = source.locals.lookup key
  frame : UDivMod.frozen target = UDivMod.frozen source
  forward : target.clock ≤ source.clock
  cost : source.clock - target.clock ≤ 67 * (5-index)

/-- All five original fixed-list calls, or any suffix, on an actual enclosing
non-timeout run. Every rejection is the real SszErr30/31; a passed suffix
retains the actual count words, quotient/remainder equations, complete frozen
state and lexical restoration. No future list return is postulated. -/
theorem counts_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (words : Nat → BitVec 64) (total pointer cursor : BitVec 64)
    (index rounds : Nat) (finish : index + rounds = 5) (model : CountLocals source words total pointer cursor)
    (installed : OriginalCode.Installed source.code) (shape : source.eshapes.lookup (ofString "SszErr") = some .one)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (countStage index) = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (∃ error : BitVec 64,(error = 30#64 ∨ error = 31#64) ∧ result = some (.exception (ofString "SszErr") (.val (.word error))) ∧ source.clock - post.clock ≤ 67 * rounds) ∨
    (∃ (target innerPost : PanSemStateFiniteExact 64 Guest.HostMemory) (counts : Nat → BitVec 64) (restoreStack : PanSemStateFiniteExact 64 Guest.HostMemory → PanSemStateFiniteExact 64 Guest.HostMemory),
      CountsDone source target words total pointer cursor index counts ∧ evaluateHOLFiniteState target (countStage 5) = (result,innerPost) ∧ post = restoreStack innerPost ∧
      (∀ state,emptyLocalsHOLFinite (restoreStack state) = emptyLocalsHOLFinite state)) := by
  induction rounds generalizing source post index with
  | zero =>
    have indexEq : index = 5 := by omega
    subst index
    have done : CountsDone source source words total pointer cursor 5 (fun _ => 0#64) :=
      ⟨model,by intros; omega,by intros; omega,by intros; rfl,rfl,Nat.le_refl _,by simp⟩
    exact Or.inr ⟨source,post,(fun _ => 0#64),id,done,run,rfl,fun _ => rfl⟩
  | succ rounds ih =>
    have small : index < 5 := by omega
    have args := CountLocals.arguments source words total pointer cursor model index small
    rw [count_stage_shape index small] at run
    rcases FixedList.caller_trace source post (countSpan words total index) (elementSize index) 9223372036854775807#64 (element_size_nonzero index).1
      (DecoderRuntime.division_code source.code installed) (DecoderRuntime.fail_code source.code installed) shape (DecoderRuntime.fixed_list_code source.code installed)
      (countName index) (countArguments index) (countStage (index+1)) args result run notTimeout with rejected | normal
    · obtain ⟨error,allowed,same,cost⟩ := rejected
      exact Or.inl ⟨error,allowed,same,by omega⟩
    · obtain ⟨next,innerPost,count,locals,countBound,forward,cost,frame,remaining,restored,arithmetic⟩ := normal
      have nextModel := CountLocals.after_call source next words total pointer cursor count model index locals
      have codeEq : next.code = source.code := by have h := congrArg PanSemStateFiniteExact.code frame; exact h
      have shapeEq : next.eshapes = source.eshapes := by have h := congrArg PanSemStateFiniteExact.eshapes frame; exact h
      have nextCode : OriginalCode.Installed next.code := codeEq.symm ▸ installed
      have nextShape : next.eshapes.lookup (ofString "SszErr") = some .one := by rw [shapeEq]; exact shape
      rcases ih next innerPost (index+1) (by omega) nextModel nextCode nextShape remaining with rejected | normal
      · obtain ⟨error,allowed,same,tailCost⟩ := rejected
        have finalClock : post.clock = innerPost.clock := by rw [restored]; rfl
        have finalForward := evaluateHOLFiniteState_clock_le next (countStage (index+1))
        rw [remaining] at finalForward
        change innerPost.clock ≤ next.clock at finalForward
        exact Or.inl ⟨error,allowed,same,by rw [finalClock]; omega⟩
      · obtain ⟨target,finalPost,tailCounts,tailRestore,completed,tailRun,tailEndpoint,tailPure⟩ := normal
        let counts := fun position => if position = index then count else tailCounts position
        have nextBinding : next.locals.lookup (ofString (countName index)) = some (.val (.word count)) := by
          rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
        have currentBinding : target.locals.lookup (ofString (countName index)) = some (.val (.word count)) :=
          (completed.other _ (fun position low inside => count_names_distinct index position small inside (by omega))).trans nextBinding
        have bindings (position : Nat) (low : index ≤ position) (inside : position < 5) : target.locals.lookup (ofString (countName position)) = some (.val (.word (counts position))) := by
          by_cases equal : position = index
          · subst position
            simpa only [counts,if_pos rfl] using currentBinding
          · simpa only [counts,if_neg equal] using completed.bindings position (by omega) inside
        have equations (position : Nat) (low : index ≤ position) (inside : position < 5) :
            (counts position).toNat = (countSpan words total position).toNat / (elementSize position).toNat ∧ (countSpan words total position).toNat % (elementSize position).toNat = 0 := by
          by_cases equal : position = index
          · subst position
            simpa only [counts,if_pos rfl] using arithmetic (element_size_nonzero index).2
          · simpa only [counts,if_neg equal] using completed.arithmetic position (by omega) inside
        have other (key : MlS) (untouched : ∀ position,index ≤ position → position < 5 → key ≠ ofString (countName position)) : target.locals.lookup key = source.locals.lookup key := by
          have prior := completed.other key (fun position low inside => untouched position (by omega) inside)
          have step : next.locals.lookup key = source.locals.lookup key := by
            rw [locals]
            simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm (untouched index (Nat.le_refl _) small)]
          exact prior.trans step
        have targetForward := completed.forward
        have tailCost := completed.cost
        have done : CountsDone source target words total pointer cursor index counts :=
          ⟨completed.model,bindings,equations,other,completed.frame.trans frame,Nat.le_trans targetForward forward,by omega⟩
        let restoreStack := fun state => restore source (countName index) (tailRestore state)
        have endpoint : post = restoreStack finalPost := by rw [restored,tailEndpoint]
        have pure (state : PanSemStateFiniteExact 64 Guest.HostMemory) : emptyLocalsHOLFinite (restoreStack state) = emptyLocalsHOLFinite state := tailPure state
        exact Or.inr ⟨target,finalPost,counts,restoreStack,done,tailRun,endpoint,pure⟩

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.counts_trace
