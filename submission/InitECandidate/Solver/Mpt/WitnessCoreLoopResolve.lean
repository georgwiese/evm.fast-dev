import InitECandidate.Solver.Mpt.WitnessCoreLoopInvariant

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open Input.Main.RunAttemptConstructors

/-- A genuine original resolver iteration installs the actual pending
hash and either delivers a fresh result or supplies a bounded next input.
Both alternatives preserve the full invariant and decrease actual rank. -/
theorem Invariant.resolve_normal (input : Guest.InputBlob) (frontier : Nat) (db heap cursor limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stack : List Entry)
    (invariant : Invariant input frontier db limit source ⟨heap,cursor,stack,.resolve,true⟩)
    (normal : evaluateHOLFiniteState source resolveBranch=(none,post)) :
    ∃ next : Configuration,Invariant input frontier db limit post next ∧
      next.rank limit<(Configuration.mk heap cursor stack .resolve true).rank limit := by
  obtain ⟨entry,rest,stackEq,waiting,slotCell⟩:=invariant.phase
  change stack=entry::rest at stackEq
  subst stack
  obtain ⟨oldResult,resultCell⟩:=invariant.words.result
  obtain ⟨oldPointer,pointerCell⟩:=invariant.words.pointer
  obtain ⟨oldLength,lengthCell⟩:=invariant.words.length
  obtain ⟨step,dbCell,goCell,words,frame⟩:=core_resolve_stack_normal input source post db heap cursor limit oldResult oldPointer oldLength 2#64 entry rest
    invariant.view (invariant.boundary input frontier db limit source _) invariant.dbCell invariant.topCell slotCell resultCell pointerCell lengthCell invariant.modeCell
    invariant.heapCell invariant.aligned invariant.scratch invariant.below invariant.heapLower invariant.installed normal
  have frozen:=invariant.frozen.database_frame input source post frontier heap invariant.frontierBefore frame dbCell
  have actualDb:=dbCell.trans invariant.dbCell
  have actualGo:=goCell.trans invariant.goCell
  have installed : Input.OriginalCode.Installed post.code:=by rw [frame.code]; exact invariant.installed
  obtain ⟨next,pending,nextCell,nextArena,aligned,grows,scratch,view,top,slot,shape⟩:=step
  let nextEntry : Entry:={entry with pending:=some pending}
  have fresh : FreshFrom frontier (nextEntry::rest):=invariant.fresh.advance frontier entry nextEntry rest rfl rfl
  have nextWaiting : Waiting (nextEntry::rest):=waiting.cons nextEntry rest ⟨pending,rfl⟩
  rcases shape with ⟨zero,node,result,mode,owned,rank⟩|⟨pointer,length,actualPointer,actualLength,mode,small,lower,before,validHash,rank⟩
  · have parentLower:=invariant.view.marks entry List.mem_cons_self
    have returnedOwned:=owned.weaken post node heap.toNat next.toNat (resultLower (nextEntry::rest)) next.toNat parentLower (Nat.le_refl _)
    exact ⟨⟨next,cursor,nextEntry::rest,.returning,true⟩,
      ⟨frozen,actualDb,nextCell,nextArena,aligned,invariant.heapLower.trans grows,invariant.frontierBefore.trans grows,
        scratch,invariant.below,view,fresh,words,top,mode,actualGo,⟨nextWaiting,node,result,returnedOwned⟩,Or.inl rfl,installed⟩,rank⟩
  · exact ⟨⟨next,cursor,nextEntry::rest,.decode,true⟩,
      ⟨frozen,actualDb,nextCell,nextArena,aligned,invariant.heapLower.trans grows,invariant.frontierBefore.trans grows,
        scratch,invariant.below,view,fresh,words,top,mode,actualGo,
        ⟨nextWaiting,pointer,length,actualPointer,actualLength,small,lower,before⟩,Or.inl rfl,installed⟩,rank⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Invariant.resolve_normal
