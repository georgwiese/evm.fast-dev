import InitECandidate.Solver.Mpt.WitnessCoreLoopStep

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors

/-- Every word before the fixed materializer-entry heap survives an
iteration, including caller-owned nodes, inputs and both databases. -/
def StablePrefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier : Nat) : Prop:=
  ∀ query : BitVec 64,query.toNat<frontier → post.memory query=source.memory query

theorem Invariant.decode_prefix (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db heap cursor limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stack : List Entry)
    (invariant : Invariant databaseData frontier db limit source ⟨heap,cursor,stack,.decode,true⟩)
    (normal : evaluateHOLFiniteState source decodeBranch=(none,post)) : StablePrefix source post frontier := by
  obtain ⟨waiting,pointer,length,pointerCell,lengthCell,small,lower,before⟩:=invariant.phase
  obtain ⟨oldResult,resultCell⟩:=invariant.words.result
  obtain ⟨oldSlot,slotCell⟩:=invariant.words.slot
  have frame:=(core_decode_stack_normal source post db pointer length heap cursor limit oldResult oldSlot 1#64 stack
    invariant.view invariant.dbCell pointerCell lengthCell invariant.topCell resultCell slotCell invariant.modeCell
    invariant.heapCell invariant.heapArena invariant.heapBound invariant.aligned invariant.live invariant.scratch
    (invariant.db_before databaseData frontier db limit source _) before small lower normal).1
  intro query upper
  exact frame.memoryBefore query (upper.trans_le invariant.frontierBefore)

theorem Invariant.resolve_prefix (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db heap cursor limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stack : List Entry)
    (invariant : Invariant databaseData frontier db limit source ⟨heap,cursor,stack,.resolve,true⟩)
    (normal : evaluateHOLFiniteState source resolveBranch=(none,post)) : StablePrefix source post frontier := by
  have databaseEq:=invariant.databaseEq
  subst db
  obtain ⟨entry,rest,stackEq,waiting,slotCell⟩:=invariant.phase
  change stack=entry::rest at stackEq
  subst stack
  obtain ⟨oldResult,resultCell⟩:=invariant.words.result
  obtain ⟨oldPointer,pointerCell⟩:=invariant.words.pointer
  obtain ⟨oldLength,lengthCell⟩:=invariant.words.length
  obtain ⟨step,dbCell,goCell,words,frame,database⟩:=core_resolve_stack_normal databaseData source post heap cursor limit oldResult oldPointer oldLength 2#64 entry rest
    invariant.view invariant.database (invariant.tableBefore.trans invariant.frontierBefore) invariant.dbCell invariant.topCell slotCell resultCell pointerCell lengthCell invariant.modeCell
    invariant.heapCell invariant.heapArena invariant.heapBound invariant.aligned invariant.live invariant.scratch normal
  intro query upper
  exact frame.memory query (upper.trans_le invariant.frontierBefore)

theorem Invariant.return_prefix (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db heap cursor limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stack : List Entry)
    (invariant : Invariant databaseData frontier db limit source ⟨heap,cursor,stack,.returning,true⟩)
    (normal : evaluateHOLFiniteState source returnBranch=(none,post)) : StablePrefix source post frontier := by
  obtain ⟨waiting,child,resultCell,owned⟩:=invariant.phase
  cases stack with
  | nil=>
    have run:=finish_return_execute source 1#64 invariant.goCell
    rw [return_choice source 0#64 invariant.topCell,if_pos rfl,run] at normal
    have postEq : post=QueryBranch.bind source "go" 0#64:=(congrArg Prod.snd normal).symm
    intro query upper
    rw [postEq]; rfl
  | cons entry rest=>
    obtain ⟨slot,slotCell⟩:=invariant.words.slot
    obtain ⟨hash,pendingEq⟩:=waiting entry List.mem_cons_self
    have pending:=invariant.view.pending entry List.mem_cons_self
    simp only [Pending,pendingEq] at pending
    have parentOwned:=owned.weaken source child (max frontier (resultLower (entry::rest))) heap.toNat entry.mark heap.toNat (Nat.le_max_right _ _) (Nat.le_refl _)
    obtain ⟨next,nextCell,nextArena,nextBound,aligned,grows,scratch,nextLive,shape,globals,domain,endian,code,memory,locals⟩:=
      core_return_stack_normal source post db heap cursor limit child slot hash entry rest invariant.view parentOwned invariant.topCell resultCell slotCell invariant.modeCell
        pending.1 invariant.heapCell invariant.heapArena invariant.heapBound invariant.aligned invariant.live invariant.scratch invariant.installed normal
    intro query upper
    have payloadLower:=(invariant.fresh entry List.mem_cons_self).2
    exact memory query (Or.inl (upper.trans_le payloadLower))

/-- The literal mode dispatch retains all earlier persistent memory. -/
theorem Invariant.body_prefix (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cfg : Configuration)
    (invariant : Invariant databaseData frontier db limit source cfg) (running : cfg.running=true)
    (normal : evaluateHOLFiniteState source loopBody=(none,post)) : StablePrefix source post frontier := by
  rcases cfg with ⟨heap,cursor,stack,phase,active⟩
  change active=true at running
  subst active
  rw [loop_body_choice source (modeWord phase) invariant.modeCell] at normal
  cases phase with
  | returning=>
    simp only [modeWord,show (0#64 : BitVec 64)≠1#64 from by decide,show (0#64 : BitVec 64)≠2#64 from by decide,↓reduceIte] at normal
    exact invariant.return_prefix databaseData frontier db heap cursor limit source post stack normal
  | decode=>
    simp only [modeWord,if_pos rfl] at normal
    exact invariant.decode_prefix databaseData frontier db heap cursor limit source post stack normal
  | resolve=>
    simp only [modeWord,show (2#64 : BitVec 64)≠1#64 from by decide,↓reduceIte,if_pos rfl] at normal
    exact invariant.resolve_prefix databaseData frontier db heap cursor limit source post stack normal

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Invariant.decode_prefix
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Invariant.resolve_prefix
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Invariant.return_prefix
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Invariant.body_prefix
