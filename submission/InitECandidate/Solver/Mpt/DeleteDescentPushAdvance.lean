import InitECandidate.Solver.Mpt.DeleteDescentPushMemory
import InitECandidate.Solver.Mpt.DeleteFrameDescend

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Follow either actual advance after the initialized scratch stores.
The saved parent facts and consumed-query bounds concern the reached
current state; strict progress is derived from the genuine assignments. -/
theorem descent_push_advance (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (kind : DeleteFrame.Kind) (words : String→BitVec 64)
    (nodeEq : words "node"=model.node)
    (ready : ∀ field∈kind.fields words,field.value.Ready
      (QueryBranch.bind source kind.name (Arenas.resultWord .down model.pending.cursor 40#64)))
    (graph : TrieWalk.Graph (DeleteFrame.stored kind source model.pending.cursor words).memory source.memaddrs)
    (paths : graph.PathBytes source.be)
    (owned : DeleteFrame.Saved.Owned ⟨Arenas.resultWord .down model.pending.cursor 40#64,kind,words⟩ graph)
    (matched : kind=.extension→(words "sl").toNat≤length.toNat-model.level.toNat)
    (branchBefore : kind=.branch→model.level.toNat<length.toNat)
    (normal : evaluateHOLFiniteState (DeleteFrame.stored kind source model.pending.cursor words) kind.advance=(none,target)) :
    ∃ child nextLevel : BitVec 64,graph.valid child ∧
      target=DeleteFrame.advanced (DeleteFrame.stored kind source model.pending.cursor words)
        (Arenas.resultWord .down model.pending.cursor 40#64) child nextLevel ∧
      model.level.toNat<nextLevel.toNat ∧ nextLevel.toNat≤length.toNat := by
  let record:=Arenas.resultWord .down model.pending.cursor 40#64
  let current:=DeleteFrame.stored kind source model.pending.cursor words
  have currentOther (name : String) (other : ofString kind.name≠ofString name) :
      current.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    bind_lookup_other (Arenas.post {source with clock:=source.clock-1} .down model.pending.cursor 40#64) kind.name name record other
  have nodeCell : current.locals.lookup (ofString "node")=some (.val (.word model.node)):=
    (currentOther "node" (by cases kind <;> decide)).trans model.nodeCell
  have levelCell : current.locals.lookup (ofString "level")=some (.val (.word model.level)):=
    (currentOther "level" (by cases kind <;> decide)).trans model.levelCell
  have recordCell : current.locals.lookup (ofString kind.name)=some (.val (.word record)):=bind_lookup_same _ _ _
  obtain ⟨member,active,tag,data⟩:=owned
  change graph.valid (words "node") at member
  change words "node"≠0#64 at active
  change wordAt current.memory (words "node")=kind.tag at tag
  rw [nodeEq] at member active tag
  cases kind with
  | extension=>
    have slReady:=ready ⟨32,.saved "sl" (words "sl")⟩ (by simp [DeleteFrame.Kind.fields])
    have slCell : current.locals.lookup (ofString "sl")=some (.val (.word (words "sl"))):=slReady
    have lengthEq : words "sl"=wordAt current.memory (model.node+40#64):=by
      change wordAt current.memory (words "node"+32#64)=words "seg" ∧ wordAt current.memory (words "node"+40#64)=words "sl" at data
      rw [nodeEq] at data
      exact data.2.symm
    obtain ⟨child,childMember,endpoint,_addition,progress,before⟩:=DeleteFrame.extension_descend_normal current target record model.node model.level length (words "sl")
      graph member active tag paths lengthEq recordCell nodeCell levelCell slCell model.levelBound (matched rfl) model.bounded normal
    exact ⟨child,model.level+words "sl",childMember,endpoint,progress,before⟩
  | branch=>
    have idxReady:=ready ⟨32,.saved "idx" (words "idx")⟩ (by simp [DeleteFrame.Kind.fields])
    have idxCell0 : current.locals.lookup (ofString "idx")=some (.val (.word (words "idx"))):=idxReady
    have idxCell : current.locals.lookup (ofString "idx")=some (.val (.word (BitVec.ofNat 64 (words "idx").toNat))):=by
      simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using idxCell0
    have tag3 : wordAt current.memory model.node=3#64:=tag
    obtain ⟨child,childMember,endpoint,_addition,progress,before⟩:=DeleteFrame.branch_descend_normal current target record model.node model.level length (words "idx").toNat data
      graph member active (by rw [tag3]; decide) (by rw [tag3]; decide) (by rw [tag3]; decide)
      recordCell nodeCell idxCell levelCell (branchBefore rfl) model.bounded normal
    exact ⟨child,model.level+1#64,childMember,endpoint,progress,before⟩

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.descent_push_advance
