import InitECandidate.Solver.Mpt.WitnessCoreLoopInvariant

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open Input.Main.RunAttemptConstructors

/-- A genuine original decode iteration preserves the complete global
materializer invariant and strictly decreases the physical rank. The
actual decoder result supplies both fresh allocation floors on a push. -/
theorem Invariant.decode_normal (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db heap cursor limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stack : List Entry)
    (invariant : Invariant databaseData frontier db limit source ⟨heap,cursor,stack,.decode,true⟩)
    (normal : evaluateHOLFiniteState source decodeBranch=(none,post)) :
    ∃ next : Configuration,Invariant databaseData frontier db limit post next ∧
      next.rank limit<(Configuration.mk heap cursor stack .decode true).rank limit := by
  obtain ⟨waiting,pointer,length,pointerCell,lengthCell,small,lower,before⟩:=invariant.phase
  obtain ⟨oldResult,resultCell⟩:=invariant.words.result
  obtain ⟨oldSlot,slotCell⟩:=invariant.words.slot
  obtain ⟨frame,step,dbCell,goCell,words⟩:=core_decode_stack_normal source post db pointer length heap cursor limit oldResult oldSlot 1#64 stack
    invariant.view invariant.dbCell pointerCell lengthCell invariant.topCell resultCell slotCell invariant.modeCell
    invariant.heapCell invariant.heapArena invariant.heapBound invariant.aligned invariant.live invariant.scratch
    (invariant.db_before databaseData frontier db limit source _) before small lower normal
  have database:=invariant.database.of_before heap.toNat (invariant.tableBefore.trans invariant.frontierBefore) frame.domain frame.endian frame.memoryBefore
  have actualDb:=dbCell.trans invariant.dbCell
  have actualGo:=goCell.trans invariant.goCell
  have installed : Input.OriginalCode.Installed post.code:=by rw [frame.code]; exact invariant.installed
  cases step with
  | terminal next node nextCell nextArena nextBound aligned grows scratch nextLive view top result mode owned decoded rank=>
    have parentLower:=invariant.view.result_lower_le_heap source db cursor.toNat heap.toNat stack invariant.heapLower
    have returnedOwned:=owned.weaken post node heap.toNat next.toNat (max frontier (resultLower stack)) next.toNat
      (max_le invariant.frontierBefore parentLower) (Nat.le_refl _)
    exact ⟨⟨next,cursor,stack,.returning,true⟩,
      ⟨database,invariant.tableBefore,invariant.databaseEq,actualDb,nextCell,nextArena,nextBound,aligned,invariant.heapLower.trans grows,invariant.frontierBefore.trans grows,
        scratch,nextLive,view,invariant.fresh,words,top,mode,actualGo,⟨waiting,node,result,returnedOwned⟩,Or.inl rfl,installed⟩,rank⟩
  | pushed data next nextCell nextArena nextBound aligned grows scratch nextLive view fresh initial freshRows freshPayload top slot mode rank=>
    let entry : Entry:=⟨WitnessRecord.pointer cursor,data,next.toNat,none⟩
    have freshStack : FreshFrom frontier (entry::stack):=
      invariant.fresh.cons frontier entry stack (invariant.frontierBefore.trans freshRows) (invariant.frontierBefore.trans freshPayload)
    exact ⟨⟨next,WitnessRecord.pointer cursor,entry::stack,.resolve,true⟩,
      ⟨database,invariant.tableBefore,invariant.databaseEq,actualDb,nextCell,nextArena,nextBound,aligned,invariant.heapLower.trans grows,invariant.frontierBefore.trans grows,
        scratch,nextLive,view,freshStack,words,top,mode,actualGo,⟨entry,stack,rfl,waiting,slot⟩,Or.inl rfl,installed⟩,rank⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Invariant.decode_normal
