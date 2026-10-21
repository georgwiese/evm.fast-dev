import InitECandidate.Solver.Mpt.WitnessCoreRegistryReturn
import InitECandidate.Solver.Input.RootBoundaryBounds

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors

/-- Every genuine normal original return iteration preserves the full
loop invariant and decreases rank. Empty top stops go; otherwise the
real pending hash/cache/stage path advances a branch or pops its parent. -/
theorem RichInvariant.return_normal (input : Guest.InputBlob) (frontier : Nat) (db heap cursor limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stack : List Entry)
    (rich : RichInvariant input frontier db limit source ⟨heap,cursor,stack,.returning,true⟩)
    (frontierLower : 2713731432≤frontier)
    (normal : evaluateHOLFiniteState source returnBranch=(none,post)) :
    ∃ next : Configuration,RichInvariant input frontier db limit post next ∧
      next.rank limit<(Configuration.mk heap cursor stack .returning true).rank limit := by
  have invariant:=rich.base
  obtain ⟨registry⟩:=rich.registry
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
    have frozen:=invariant.frozen.frame input source stopped frontier rfl rfl (other "db" (by decide)) (by intros; rfl)
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
    have base : Invariant input frontier db limit stopped ⟨heap,cursor,[],.returning,false⟩ :=
      ⟨frozen,(other "db" (by decide)).trans invariant.dbCell,invariant.heapCell,invariant.heapArena,invariant.aligned,invariant.heapLower,invariant.frontierBefore,
        invariant.scratch.of_fields source stopped cursor limit rfl rfl,invariant.below,empty stopped db cursor.toNat heap.toNat,
        invariant.fresh,words,(other "top" (by decide)).trans invariant.topCell,(other "mode" (by decide)).trans invariant.modeCell,
        bind_lookup_same _ _ _,phase,Or.inr ⟨rfl,rfl⟩,invariant.installed⟩
    obtain ⟨runningRegistry,validEq⟩:=registry.of_fields source stopped frontier db _ rfl rfl (other "result" (by decide))
    have stoppedRegistry:=runningRegistry.of_payloads stopped frontier db ⟨heap,cursor,[],.returning,true⟩ ⟨heap,cursor,[],.returning,false⟩ rfl rfl
      (by intro entry member; cases member)
    exact ⟨⟨heap,cursor,[],.returning,false⟩,⟨base,stoppedRegistry⟩,rank⟩
  | cons entry rest=>
    obtain ⟨slot,slotCell⟩:=invariant.words.slot
    obtain ⟨hash,pendingEq⟩:=waiting entry List.mem_cons_self
    have pending:=invariant.view.pending entry List.mem_cons_self
    simp only [Pending,pendingEq] at pending
    have parentOwned:=owned.weaken source child (max frontier (resultLower (entry::rest))) heap.toNat entry.mark heap.toNat (Nat.le_max_right _ _) (Nat.le_refl _)
    have step:=core_return_stack_normal source post db heap cursor limit child slot hash entry rest invariant.view parentOwned invariant.topCell resultCell slotCell invariant.modeCell
      pending.1 invariant.heapCell invariant.heapArena invariant.aligned invariant.scratch invariant.installed normal
    have frozen:=invariant.frozen.return_step input source post frontier db heap cursor limit child slot entry rest invariant.fresh invariant.view step
    have words:=step.data_words source post db heap cursor limit child slot entry rest invariant.words
    obtain ⟨next,nextCell,nextArena,aligned,grows,scratch,shape,globals,domain,endian,code,memory,locals⟩:=step
    have actualDb:=(locals "db" (Or.inl rfl)).trans invariant.dbCell
    have actualGo:=(locals "go" (Or.inr (Or.inl rfl))).trans invariant.goCell
    have installed : Input.OriginalCode.Installed post.code:=by rw [code]; exact invariant.installed
    have olderWaiting:=waiting.tail entry rest
    have dbUpper:=(invariant.boundary input frontier db limit source _).db_upper input source db invariant.dbCell
    have registryStep:=registry.return_normal source post frontier db heap next cursor limit child slot hash entry rest invariant.view parentOwned
      frontierLower invariant.frontierBefore (invariant.fresh entry List.mem_cons_self).2 dbUpper invariant.topCell resultCell slotCell invariant.modeCell pending.1
      invariant.heapCell invariant.heapArena invariant.aligned invariant.scratch invariant.installed nextCell normal
    rcases shape with ⟨nextEntry,sameRecord,sameMark,samePending,sameArray,samePayload,view,top,actualSlot,mode,result,rank⟩|
      ⟨view,node,resultOwned,top,result,mode,actualSlot,rank⟩
    · have fresh:=invariant.fresh.advance frontier entry nextEntry rest sameArray samePayload
      have base : Invariant input frontier db limit post ⟨next,cursor,nextEntry::rest,.resolve,true⟩ :=
        ⟨frozen,actualDb,nextCell,nextArena,aligned,invariant.heapLower.trans grows,invariant.frontierBefore.trans grows,
          scratch,invariant.below,view,fresh,words,top,mode,actualGo,⟨nextEntry,rest,rfl,olderWaiting,actualSlot⟩,Or.inl rfl,installed⟩
      rcases registryStep with ⟨registryEntry,sameRegistryRecord,registryView,registryMode,⟨nextRegistry⟩⟩|⟨registryMode,poppedRegistry⟩
      · have active:=nextRegistry.replace_head post frontier db next cursor registryEntry nextEntry rest .resolve true
          (sameRecord.trans sameRegistryRecord.symm) registryView (view.records nextEntry List.mem_cons_self)
        exact ⟨⟨next,cursor,nextEntry::rest,.resolve,true⟩,⟨base,active⟩,rank⟩
      · have impossible : (2#64 : BitVec 64)=0#64 := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (mode.symm.trans registryMode)))
        exact ((by decide : (2#64 : BitVec 64)≠0#64) impossible).elim
    · have lower : max frontier (resultLower rest)≤max (resultLower rest) entry.data.payload.startAddress:=
        max_le ((invariant.fresh entry List.mem_cons_self).2.trans (Nat.le_max_right _ _)) (Nat.le_max_left _ _)
      have returnedOwned:=resultOwned.weaken post node (max (resultLower rest) entry.data.payload.startAddress) next.toNat (max frontier (resultLower rest)) next.toNat lower (Nat.le_refl _)
      have base : Invariant input frontier db limit post ⟨next,cursor,rest,.returning,true⟩ :=
        ⟨frozen,actualDb,nextCell,nextArena,aligned,invariant.heapLower.trans grows,invariant.frontierBefore.trans grows,
          scratch,invariant.below,view,invariant.fresh.tail frontier entry rest,words,top,mode,actualGo,
          ⟨olderWaiting,node,result,returnedOwned⟩,Or.inl rfl,installed⟩
      rcases registryStep with ⟨registryEntry,sameRegistryRecord,registryView,registryMode,nextRegistry⟩|⟨registryMode,poppedRegistry⟩
      · have impossible : (0#64 : BitVec 64)=2#64 := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (mode.symm.trans registryMode)))
        exact ((by decide : (0#64 : BitVec 64)≠2#64) impossible).elim
      · exact ⟨⟨next,cursor,rest,.returning,true⟩,⟨base,poppedRegistry⟩,rank⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.RichInvariant.return_normal
