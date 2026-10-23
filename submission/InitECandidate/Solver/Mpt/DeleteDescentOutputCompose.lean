import InitECandidate.Solver.Mpt.DeleteDescentOutput
import InitECandidate.Solver.Mpt.TrieGraphPathFieldsFrame

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack PanSemStateFiniteExact GasBudget

/-- Compose actual descent outcomes ending in a stopped state. The
scratch cursor only moves down, so the later scratch writes retain the
entire incoming protected band, as well as all bytes below its frame. -/
theorem DescentOutput.then_stopped (source middle target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property)
    (first : DescentOutput source middle key length limit nodeLower pathLower property model)
    (second : DescentOutput middle target key length limit nodeLower pathLower property first.next)
    (stopped : second.next.go=0#64) :
    Nonempty {output : DescentOutput source target key length limit nodeLower pathLower property model // output.next.go=0#64} :=
  ⟨⟨{
    next:=second.next
    grows:=first.grows.trans second.grows
    scratchDecreases:=second.scratchDecreases.trans first.scratchDecreases
    frameEq:=second.frameEq.trans first.frameEq
    members:=fun node member=>second.members node (first.members node member)
    freshMembers:=by
      intro node member
      rcases second.freshMembers node member with old|fresh
      · exact first.freshMembers node old
      · exact Or.inr (first.grows.trans fresh)
    fields:=first.fields.trans model.pending.graph first.next.pending.graph second.fields first.members
    memoryLow:=by
      intro address before
      exact (second.memoryLow address (by rw [first.frameEq]; exact before)).trans (first.memoryLow address before)
    memoryBand:=fun address above before=>(second.memoryBand address (first.scratchDecreases.trans above) before).trans (first.memoryBand address above before)
    protectedWords:=by
      intro address safe above before
      obtain ⟨firstWord,firstSafe⟩:=first.protectedWords address safe above before
      obtain ⟨lastWord,lastSafe⟩:=second.protectedWords address firstSafe above (before.trans_le first.grows)
      exact ⟨lastWord.trans firstWord,lastSafe⟩
    globals:=fun name notHeap notScratch=>(second.globals name notHeap notScratch).trans (first.globals name notHeap notScratch)
    progress:=Or.inl stopped },stopped⟩⟩

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.DescentOutput.then_stopped
