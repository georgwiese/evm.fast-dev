import InitECandidate.Solver.Mpt.WitnessCoreLoopStep

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors

/-- All older persistent storage in this fixed band survives an iteration.
This includes caller-owned nodes, not just the witness database footprint. -/
def StablePrefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier : Nat) : Prop:=
  ∀ query : BitVec 64,2713717616≤query.toNat → query.toNat<frontier → post.memory query=source.memory query

theorem Invariant.decode_prefix (input : Guest.InputBlob) (frontier : Nat) (db heap cursor limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stack : List Entry)
    (invariant : Invariant input frontier db limit source ⟨heap,cursor,stack,.decode,true⟩)
    (normal : evaluateHOLFiniteState source decodeBranch=(none,post)) : StablePrefix source post frontier := by
  obtain ⟨waiting,pointer,length,pointerCell,lengthCell,small,lower,before⟩:=invariant.phase
  obtain ⟨oldResult,resultCell⟩:=invariant.words.result
  obtain ⟨oldSlot,slotCell⟩:=invariant.words.slot
  have frame:=(core_decode_stack_normal input source post db pointer length heap cursor limit oldResult oldSlot 1#64 stack
    (invariant.boundary input frontier db limit source _) invariant.view invariant.dbCell pointerCell lengthCell invariant.topCell resultCell slotCell invariant.modeCell
    invariant.heapCell invariant.scratch invariant.heapLower before small lower invariant.below invariant.installed normal).1
  intro query lower upper
  exact frame.memory query (invariant.below.trans lower) (upper.trans_le invariant.frontierBefore)

theorem Invariant.resolve_prefix (input : Guest.InputBlob) (frontier : Nat) (db heap cursor limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stack : List Entry)
    (invariant : Invariant input frontier db limit source ⟨heap,cursor,stack,.resolve,true⟩)
    (normal : evaluateHOLFiniteState source resolveBranch=(none,post)) : StablePrefix source post frontier := by
  obtain ⟨entry,rest,stackEq,waiting,slotCell⟩:=invariant.phase
  change stack=entry::rest at stackEq
  subst stack
  obtain ⟨oldResult,resultCell⟩:=invariant.words.result
  obtain ⟨oldPointer,pointerCell⟩:=invariant.words.pointer
  obtain ⟨oldLength,lengthCell⟩:=invariant.words.length
  obtain ⟨step,dbCell,goCell,words,frame⟩:=core_resolve_stack_normal input source post db heap cursor limit oldResult oldPointer oldLength 2#64 entry rest
    invariant.view (invariant.boundary input frontier db limit source _) invariant.dbCell invariant.topCell slotCell resultCell pointerCell lengthCell invariant.modeCell
    invariant.heapCell invariant.aligned invariant.scratch invariant.below invariant.heapLower invariant.installed normal
  intro query lower upper
  exact frame.memory query lower (upper.trans_le invariant.frontierBefore)

theorem Invariant.return_prefix (input : Guest.InputBlob) (frontier : Nat) (db heap cursor limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stack : List Entry)
    (invariant : Invariant input frontier db limit source ⟨heap,cursor,stack,.returning,true⟩)
    (normal : evaluateHOLFiniteState source returnBranch=(none,post)) : StablePrefix source post frontier := by
  obtain ⟨waiting,child,resultCell,owned⟩:=invariant.phase
  cases stack with
  | nil=>
    have run:=finish_return_execute source 1#64 invariant.goCell
    rw [return_choice source 0#64 invariant.topCell,if_pos rfl,run] at normal
    have postEq : post=QueryBranch.bind source "go" 0#64:=(congrArg Prod.snd normal).symm
    intro query lower upper
    rw [postEq]; rfl
  | cons entry rest=>
    obtain ⟨slot,slotCell⟩:=invariant.words.slot
    obtain ⟨hash,pendingEq⟩:=waiting entry List.mem_cons_self
    have pending:=invariant.view.pending entry List.mem_cons_self
    simp only [Pending,pendingEq] at pending
    have parentOwned:=owned.weaken source child (max frontier (resultLower (entry::rest))) heap.toNat entry.mark heap.toNat (Nat.le_max_right _ _) (Nat.le_refl _)
    obtain ⟨next,nextCell,nextArena,aligned,grows,scratch,shape,globals,domain,endian,code,memory,locals⟩:=
      core_return_stack_normal source post db heap cursor limit child slot hash entry rest invariant.view parentOwned invariant.topCell resultCell slotCell invariant.modeCell
        pending.1 invariant.heapCell invariant.heapArena invariant.aligned invariant.scratch invariant.installed normal
    intro query lower upper
    have recordUpper:=(invariant.view.records entry List.mem_cons_self).ceiling
    have payloadLower:=(invariant.fresh entry List.mem_cons_self).2
    exact memory query (by omega) (upper.trans_le payloadLower)

/-- The literal mode dispatch retains the entire older persistent band. -/
theorem Invariant.body_prefix (input : Guest.InputBlob) (frontier : Nat) (db limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cfg : Configuration)
    (invariant : Invariant input frontier db limit source cfg) (running : cfg.running=true)
    (normal : evaluateHOLFiniteState source loopBody=(none,post)) : StablePrefix source post frontier := by
  rcases cfg with ⟨heap,cursor,stack,phase,active⟩
  change active=true at running
  subst active
  rw [loop_body_choice source (modeWord phase) invariant.modeCell] at normal
  cases phase with
  | returning=>
    simp only [modeWord,show (0#64 : BitVec 64)≠1#64 from by decide,show (0#64 : BitVec 64)≠2#64 from by decide,↓reduceIte] at normal
    exact invariant.return_prefix input frontier db heap cursor limit source post stack normal
  | decode=>
    simp only [modeWord,if_pos rfl] at normal
    exact invariant.decode_prefix input frontier db heap cursor limit source post stack normal
  | resolve=>
    simp only [modeWord,show (2#64 : BitVec 64)≠1#64 from by decide,↓reduceIte,if_pos rfl] at normal
    exact invariant.resolve_prefix input frontier db heap cursor limit source post stack normal

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Invariant.decode_prefix
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Invariant.resolve_prefix
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Invariant.return_prefix
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Invariant.body_prefix
