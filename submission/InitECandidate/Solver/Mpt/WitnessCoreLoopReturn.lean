import InitECandidate.Solver.Mpt.WitnessCoreLoopInvariant

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors

/-- Every genuine normal original return iteration preserves the full
loop invariant and decreases rank. Empty top stops go; otherwise the
real pending hash/cache/stage path advances a branch or pops its parent. -/
theorem Invariant.return_normal (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db heap cursor limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stack : List Entry)
    (invariant : Invariant databaseData frontier db limit source ⟨heap,cursor,stack,.returning,true⟩)
    (normal : evaluateHOLFiniteState source returnBranch=(none,post)) :
    ∃ next : Configuration,Invariant databaseData frontier db limit post next ∧
      next.rank limit<(Configuration.mk heap cursor stack .returning true).rank limit := by
  obtain ⟨waiting,child,resultCell,owned⟩:=invariant.phase
  cases stack with
  | nil=>
    have run:=finish_return_execute source 1#64 invariant.goCell
    rw [return_choice source 0#64 invariant.topCell,if_pos rfl,run] at normal
    have postEq : post=QueryBranch.bind source "go" 0#64:=(congrArg Prod.snd normal).symm
    subst post
    let stopped:=QueryBranch.bind source "go" 0#64
    have other (name : String) (notGo : ofString "go"≠ofString name) : stopped.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
      bind_lookup_other source "go" name 0#64 notGo
    have database:=invariant.database.of_frame (show Input.LocalEffects.erase stopped=Input.LocalEffects.erase source from rfl)
    have words : DataWords stopped:=by
      obtain ⟨pointer,pointerCell⟩:=invariant.words.pointer
      obtain ⟨length,lengthCell⟩:=invariant.words.length
      obtain ⟨result,resultValue⟩:=invariant.words.result
      obtain ⟨slot,slotCell⟩:=invariant.words.slot
      exact ⟨⟨pointer,(other "cur_p" (by decide)).trans pointerCell⟩,⟨length,(other "cur_n" (by decide)).trans lengthCell⟩,
        ⟨result,(other "result" (by decide)).trans resultValue⟩,⟨slot,(other "slot" (by decide)).trans slotCell⟩⟩
    have phase : PhaseInvariant stopped frontier db heap [] .returning:=
      ⟨waiting,child,(other "result" (by decide)).trans resultCell,owned.of_fields source stopped child (max frontier (resultLower [])) heap.toNat rfl⟩
    have rank : (Configuration.mk heap cursor [] .returning false).rank limit<(Configuration.mk heap cursor [] .returning true).rank limit:=by
      simpa only [Configuration.rank,frames,List.map_nil] using WitnessStackRank.finish (WitnessStackRank.recordsLeft cursor.toNat limit.toNat)
    exact ⟨⟨heap,cursor,[],.returning,false⟩,
      ⟨database,invariant.tableBefore,invariant.databaseEq,(other "db" (by decide)).trans invariant.dbCell,invariant.heapCell,invariant.heapArena,invariant.heapBound,invariant.aligned,invariant.heapLower,invariant.frontierBefore,
        invariant.scratch.of_fields source stopped cursor limit rfl rfl,invariant.live.of_frame rfl,empty stopped db cursor.toNat heap.toNat,
        invariant.fresh,words,(other "top" (by decide)).trans invariant.topCell,(other "mode" (by decide)).trans invariant.modeCell,
        bind_lookup_same _ _ _,phase,Or.inr ⟨rfl,rfl⟩,invariant.installed⟩,rank⟩
  | cons entry rest=>
    obtain ⟨slot,slotCell⟩:=invariant.words.slot
    obtain ⟨hash,pendingEq⟩:=waiting entry List.mem_cons_self
    have pending:=invariant.view.pending entry List.mem_cons_self
    simp only [Pending,pendingEq] at pending
    have parentOwned:=owned.weaken source child (max frontier (resultLower (entry::rest))) heap.toNat entry.mark heap.toNat (Nat.le_max_right _ _) (Nat.le_refl _)
    have step:=core_return_stack_normal source post db heap cursor limit child slot hash entry rest invariant.view parentOwned invariant.topCell resultCell slotCell invariant.modeCell
      pending.1 invariant.heapCell invariant.heapArena invariant.heapBound invariant.aligned invariant.live invariant.scratch invariant.installed normal
    have database:=step.database databaseData source post frontier db heap cursor limit child slot entry rest invariant.database invariant.tableBefore invariant.fresh
    have words:=step.data_words source post db heap cursor limit child slot entry rest invariant.words
    obtain ⟨next,nextCell,nextArena,nextBound,aligned,grows,scratch,nextLive,shape,globals,domain,endian,code,memory,locals⟩:=step
    have actualDb:=(locals "db" (Or.inl rfl)).trans invariant.dbCell
    have actualGo:=(locals "go" (Or.inr (Or.inl rfl))).trans invariant.goCell
    have installed : Input.OriginalCode.Installed post.code:=by rw [code]; exact invariant.installed
    have olderWaiting:=waiting.tail entry rest
    rcases shape with ⟨nextEntry,sameRecord,sameMark,samePending,sameArray,samePayload,view,top,actualSlot,mode,result,rank⟩|
      ⟨view,node,resultOwned,top,result,mode,actualSlot,rank⟩
    · have fresh:=invariant.fresh.advance frontier entry nextEntry rest sameArray samePayload
      exact ⟨⟨next,cursor,nextEntry::rest,.resolve,true⟩,
        ⟨database,invariant.tableBefore,invariant.databaseEq,actualDb,nextCell,nextArena,nextBound,aligned,invariant.heapLower.trans grows,invariant.frontierBefore.trans grows,
          scratch,nextLive,view,fresh,words,top,mode,actualGo,⟨nextEntry,rest,rfl,olderWaiting,actualSlot⟩,Or.inl rfl,installed⟩,rank⟩
    · have lower : max frontier (resultLower rest)≤max (resultLower rest) entry.data.payload.startAddress:=
        max_le ((invariant.fresh entry List.mem_cons_self).2.trans (Nat.le_max_right _ _)) (Nat.le_max_left _ _)
      have returnedOwned:=resultOwned.weaken post node (max (resultLower rest) entry.data.payload.startAddress) next.toNat (max frontier (resultLower rest)) next.toNat lower (Nat.le_refl _)
      exact ⟨⟨next,cursor,rest,.returning,true⟩,
        ⟨database,invariant.tableBefore,invariant.databaseEq,actualDb,nextCell,nextArena,nextBound,aligned,invariant.heapLower.trans grows,invariant.frontierBefore.trans grows,
          scratch,nextLive,view,invariant.fresh.tail frontier entry rest,words,top,mode,actualGo,
          ⟨olderWaiting,node,result,returnedOwned⟩,Or.inl rfl,installed⟩,rank⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Invariant.return_normal
