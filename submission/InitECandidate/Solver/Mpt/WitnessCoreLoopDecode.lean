import InitECandidate.Solver.Mpt.WitnessCoreLoopInvariant

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open Input.Main.RunAttemptConstructors

/-- A genuine original decode iteration preserves the complete global
materializer invariant and strictly decreases the physical rank. The
actual decoder result supplies both fresh allocation floors on a push. -/
theorem Invariant.decode_normal (input : Guest.InputBlob) (frontier : Nat) (db heap cursor limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stack : List Entry)
    (invariant : Invariant input frontier db limit source ⟨heap,cursor,stack,.decode,true⟩)
    (normal : evaluateHOLFiniteState source decodeBranch=(none,post)) :
    ∃ next : Configuration,Invariant input frontier db limit post next ∧
      next.rank limit<(Configuration.mk heap cursor stack .decode true).rank limit := by
  obtain ⟨waiting,pointer,length,pointerCell,lengthCell,small,lower,before⟩:=invariant.phase
  obtain ⟨oldResult,resultCell⟩:=invariant.words.result
  obtain ⟨oldSlot,slotCell⟩:=invariant.words.slot
  obtain ⟨frame,step,dbCell,goCell,words⟩:=core_decode_stack_normal input source post db pointer length heap cursor limit oldResult oldSlot 1#64 stack
    (invariant.boundary input frontier db limit source _) invariant.view invariant.dbCell pointerCell lengthCell invariant.topCell resultCell slotCell invariant.modeCell
    invariant.heapCell invariant.scratch invariant.heapLower before small lower invariant.below invariant.installed normal
  have databaseFrame:=DatabaseFrame.of_decode source post heap cursor limit frame invariant.below
  have frozen:=invariant.frozen.database_frame input source post frontier heap invariant.frontierBefore databaseFrame dbCell
  have actualDb:=dbCell.trans invariant.dbCell
  have actualGo:=goCell.trans invariant.goCell
  have installed : Input.OriginalCode.Installed post.code:=by rw [frame.code]; exact invariant.installed
  cases step with
  | terminal next node nextCell nextArena aligned grows scratch view top result mode owned rank=>
    have parentLower:=invariant.view.result_lower_le_heap source db cursor.toNat heap.toNat stack invariant.heapLower
    have returnedOwned:=owned.weaken post node heap.toNat next.toNat (resultLower stack) next.toNat parentLower (Nat.le_refl _)
    exact ⟨⟨next,cursor,stack,.returning,true⟩,
      ⟨frozen,actualDb,nextCell,nextArena,aligned,invariant.heapLower.trans grows,invariant.frontierBefore.trans grows,
        scratch,invariant.below,view,invariant.fresh,words,top,mode,actualGo,⟨waiting,node,result,returnedOwned⟩,Or.inl rfl,installed⟩,rank⟩
  | pushed data next nextCell nextArena aligned grows scratch view fresh freshRows freshPayload top slot mode rank=>
    let entry : Entry:=⟨WitnessRecord.pointer cursor,data,next.toNat,none⟩
    have freshStack : FreshFrom frontier (entry::stack):=
      invariant.fresh.cons frontier entry stack (invariant.frontierBefore.trans freshRows) (invariant.frontierBefore.trans freshPayload)
    have below : (WitnessRecord.pointer cursor).toNat≤2713717616:=by
      have ceiling:=(view.records entry List.mem_cons_self).ceiling
      change (WitnessRecord.pointer cursor).toNat+88≤2713717616 at ceiling
      omega
    exact ⟨⟨next,WitnessRecord.pointer cursor,entry::stack,.resolve,true⟩,
      ⟨frozen,actualDb,nextCell,nextArena,aligned,invariant.heapLower.trans grows,invariant.frontierBefore.trans grows,
        scratch,below,view,freshStack,words,top,mode,actualGo,⟨entry,stack,rfl,waiting,slot⟩,Or.inl rfl,installed⟩,rank⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Invariant.decode_normal
