import InitECandidate.Solver.Mpt.DeleteDescentPushAdvance
import InitECandidate.Solver.Mpt.DeleteDescentOutputPure

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine original extension or branch scratch push derives its
allocation room, initialized PREV record and actual registered child.
The reconstructed descent invariant retains the entire query and gains
one saved frame only when the actual key position strictly increases. -/
theorem descent_push_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (kind : DeleteFrame.Kind) (words : String→BitVec 64)
    (topEq : words "top"=model.pending.top) (nodeEq : words "node"=model.node)
    (ready : ∀ field∈kind.fields words,field.value.Ready
      (QueryBranch.bind source kind.name (Arenas.resultWord .down model.pending.cursor 40#64)))
    (owned : DeleteFrame.Saved.Owned ⟨Arenas.resultWord .down model.pending.cursor 40#64,kind,words⟩ model.pending.graph)
    (matched : kind=.extension→(words "sl").toNat≤length.toNat-model.level.toNat)
    (branchBefore : kind=.branch→model.level.toNat<length.toNat)
    (normal : evaluateHOLFiniteState source kind.call=(none,target)) :
    Nonempty (DescentOutput source target key length limit nodeLower pathLower property model) := by
  let record:=Arenas.resultWord .down model.pending.cursor 40#64
  let current:=DeleteFrame.stored kind source model.pending.cursor words
  let saved : DeleteFrame.Saved:=⟨record,kind,words⟩
  obtain ⟨room,_funded,_view,_high,_clock,_domain,_endian,_code,inner,continued,endpoint⟩:=DeleteFrame.push_entry kind source target model.pending.cursor model.pending.frame words
    model.pending.scratch model.pending.scratchBefore ready model.pending.installed normal
  obtain ⟨graph,same,regions,disjoint,⟨values⟩,paths,pathRegions,separated,buffer,fields,stack,parents,scratch,recordBefore,low,high,globals⟩:=
    descent_push_memory source key length limit nodeLower pathLower property model kind words topEq room owned
  have members (node : BitVec 64) (member : model.pending.graph.valid node) : graph.valid node:=by rw [same]; exact member
  have currentOwned : saved.Owned graph:=owned.of_fields saved model.pending.graph graph members fields
  obtain ⟨child,nextLevel,childMember,advancedEq,increases,before⟩:=descent_push_advance source inner key length limit nodeLower pathLower property model kind words nodeEq
    ready graph paths currentOwned matched branchBefore continued
  rw [advancedEq] at endpoint
  let post:=DeleteFrame.advanced current record child nextLevel
  have currentOther (name : String) (other : ofString kind.name≠ofString name) :
      current.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    bind_lookup_other (Arenas.post {source with clock:=source.clock-1} .down model.pending.cursor 40#64) kind.name name record other
  have postOther (name : String) (notGo : ofString "go"≠ofString name) (notLevel : ofString "level"≠ofString name)
      (notNode : ofString "node"≠ofString name) (notTop : ofString "top"≠ofString name) :
      post.locals.lookup (ofString name)=current.locals.lookup (ofString name):=by
    exact (bind_lookup_other _ "go" name 1#64 notGo).trans
      ((bind_lookup_other _ "level" name nextLevel notLevel).trans
        ((bind_lookup_other _ "node" name child notNode).trans (bind_lookup_other _ "top" name record notTop)))
  have depth : (saved::model.pending.frames).length≤nextLevel.toNat:=by
    have previous:=model.depthBound
    simp only [List.length_cons]
    omega
  have frameBound : (saved::model.pending.frames).length≤64:=depth.trans (before.trans model.bounded)
  let pending : UnwindModel post limit nodeLower pathLower property := {
    heap:=model.pending.heap
    cursor:=record
    frame:=model.pending.frame
    top:=record
    result:=model.pending.result
    frames:=saved::model.pending.frames
    topCell:=(bind_lookup_other _ "go" "top" 1#64 (by decide)).trans
      ((bind_lookup_other _ "level" "top" nextLevel (by decide)).trans
        ((bind_lookup_other _ "node" "top" child (by decide)).trans (bind_lookup_same current "top" record)))
    resultCell:=(postOther "res" (by decide) (by decide) (by decide) (by decide)).trans
      ((currentOther "res" (by cases kind <;> decide)).trans model.pending.resultCell)
    heapCell:=(globals (ofString "heap_ptr") (by decide)).trans model.pending.heapCell
    heapArena:=model.pending.heapArena
    heapAligned:=model.pending.heapAligned
    scratch:=scratch.of_fields current post record model.pending.frame rfl rfl
    scratchBefore:=by have previous:=model.pending.scratchBefore; change record.toNat+40≤model.pending.cursor.toNat at recordBefore; omega
    floor:=model.pending.floor
    pathFloor:=model.pending.pathFloor
    nodeFloor:=model.pending.nodeFloor
    little:=model.pending.little
    installed:=model.pending.installed
    graph:=graph
    resultMember:=members model.pending.result model.pending.resultMember
    values:=values
    regions:=regions
    disjoint:=disjoint
    paths:=paths
    pathRegions:=pathRegions
    separated:=separated
    stack:=stack.of_memory current post record.toNat record (saved::model.pending.frames) (by intros; rfl)
    parents:=parents
    bounded:=frameBound }
  let next : DescentModel post key length limit nodeLower pathLower property := {
    pending:=pending
    node:=child
    level:=nextLevel
    go:=1#64
    keyCell:=(postOther "key" (by decide) (by decide) (by decide) (by decide)).trans
      ((currentOther "key" (by cases kind <;> decide)).trans model.keyCell)
    lengthCell:=(postOther "klen" (by decide) (by decide) (by decide) (by decide)).trans
      ((currentOther "klen" (by cases kind <;> decide)).trans model.lengthCell)
    nodeCell:=(bind_lookup_other _ "go" "node" 1#64 (by decide)).trans
      ((bind_lookup_other _ "level" "node" nextLevel (by decide)).trans (bind_lookup_same (QueryBranch.bind current "top" record) "node" child))
    levelCell:=(bind_lookup_other _ "go" "level" 1#64 (by decide)).trans (bind_lookup_same _ "level" nextLevel)
    goCell:=bind_lookup_same _ _ _
    goTyped:=Or.inr rfl
    bounded:=model.bounded
    levelBound:=before
    depthBound:=depth
    nodeMember:=childMember
    query:=buffer }
  have fresh : ofString kind.name∉descentLocals:=by cases kind <;> decide
  rw [endpoint]
  exact ⟨{
    next:=next.restore_auxiliary source post key length limit nodeLower pathLower property kind.name fresh
    grows:=Nat.le_refl _
    scratchDecreases:=by change record.toNat≤model.pending.cursor.toNat; change record.toNat+40≤model.pending.cursor.toNat at recordBefore; omega
    frameEq:=rfl
    members:=members
    freshMembers:=by intro node member; apply Or.inl; change graph.valid node at member; rw [same] at member; exact member
    fields:=fields
    memoryLow:=low
    memoryBand:=fun query above _=>high query above
    globals:=fun name _ notScratch=>globals name notScratch
    progress:=Or.inr increases }⟩

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.descent_push_normal
