import InitECandidate.Solver.Input.CurrentTable.Set.SpliceProgram
import InitECandidate.Solver.Input.CurrentTable.Set.Locals
import InitECandidate.Solver.Input.CurrentTable.NewLeaf.NextNode
import InitECandidate.Solver.Input.CurrentTable.NewInternal.Memory

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

def freshModel (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap pointer value : BitVec 64) (next count difference : Nat) :=
  NewInternal.model (NewLeaf.model source table cap (BitVec.ofNat 64 next) (BitVec.ofNat 64 count) pointer value)
    table cap (BitVec.ofNat 64 (next+1)) (BitVec.ofNat 64 difference)

/-- Both real constructor calls, with the second physical entry derived
from the first return. No future successful allocation/copy is a premise. -/
theorem fresh_allocation_trace {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root pointer value : BitVec 64}
    {next count difference : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop} (query : KeyBits.Key)
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (available : next+1 ≤ cap.toNat) (locals : Locals source table pointer value)
    (differenceCell : source.locals.lookup (ofString "d") = some (.val (.word (BitVec.ofNat 64 difference))))
    (installed : OriginalCode.Installed source.code) (little : source.be = false) (aligned : pointer.toNat%8 = 0)
    (beforeTable : pointer.toNat+32 ≤ table.toNat) (bytes : FirstDiff.ByteView source pointer query)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source newLeafCall = (outcome,post)) :
    (source.clock-post.clock ≤ 6 ∧ ∀ returned,outcome ≠ some (.returned returned)) ∨
      ∃ leafTarget leafPost internalTarget inner,
        LocalEffects.erase internalTarget = LocalEffects.erase (freshModel source table cap pointer value next count difference) ∧
        internalTarget.clock ≤ source.clock ∧ source.clock-internalTarget.clock ≤ 6 ∧
        evaluateHOLFiniteState (CallNormal.continuationEntry
          (CallNormal.continuationEntry source leafTarget "nl" (.val (.word (BitVec.ofNat 64 next))))
          internalTarget "ni" (.val (.word (BitVec.ofNat 64 (next+1))))) splice = (outcome,inner) ∧
        leafPost = restore (CallNormal.continuationEntry source leafTarget "nl" (.val (.word (BitVec.ofNat 64 next)))) "ni" inner ∧
        post = restore source "nl" leafPost := by
  have firstAvailable : next ≤ cap.toNat := by omega
  have fields := NewLeaf.fields_from_image query image firstAvailable little aligned beforeTable bytes
  have args : evalListHOLFinite source (h:=fun address => Classical.propDecidable (source.memaddrs address)) leafArguments =
      some [.val (.word table),.val (.word pointer),.val (.word value)] := by
    simp [leafArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,locals.tableCell,locals.keyCell,locals.valueCell]
  rw [splice_shapes.1] at run
  rcases NewLeaf.scoped_trace source post table cap (BitVec.ofNat 64 next) (BitVec.ofNat 64 count) pointer value query
    (image.allocator_context firstAvailable) fields beforeTable installed "nl" leafArguments newInternalCall args outcome run with stopped | reached
  · exact Or.inl ⟨by omega,stopped.2⟩
  · obtain ⟨leafTarget,leafPost,leafFrame,leafForward,leafCost,continued,endpoint⟩ := reached
    let resumed := CallNormal.continuationEntry source leafTarget "nl" (.val (.word (BitVec.ofNat 64 next)))
    have physical : LocalEffects.erase resumed = LocalEffects.erase (NewLeaf.model source table cap (BitVec.ofNat 64 next) (BitVec.ofNat 64 count) pointer value) := leafFrame
    have secondReady := NewLeaf.next_allocator image available physical
    have nodesCell := NewLeaf.next_nodes image available physical
    have resumedCode := LocalEffects.code_of_erase _ _ physical
    rw [NewLeaf.model_code] at resumedCode
    have secondInstalled : OriginalCode.Installed resumed.code := by rw [resumedCode]; exact installed
    have tableCell := (CallNormal.continuation_lookup_other source leafTarget "nl" "t" (.val (.word (BitVec.ofNat 64 next))) (by decide)).trans locals.tableCell
    have dCell := (CallNormal.continuation_lookup_other source leafTarget "nl" "d" (.val (.word (BitVec.ofNat 64 next))) (by decide)).trans differenceCell
    change resumed.locals.lookup (ofString "t") = some (.val (.word table)) at tableCell
    change resumed.locals.lookup (ofString "d") = some (.val (.word (BitVec.ofNat 64 difference))) at dCell
    have internalArgs : evalListHOLFinite resumed (h:=fun address => Classical.propDecidable (resumed.memaddrs address)) [localVar "t",localVar "d"] =
        some [.val (.word table),.val (.word (BitVec.ofNat 64 difference))] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,tableCell,dCell]
    rw [splice_shapes.2.1] at continued
    rcases NewInternal.scoped_trace resumed leafPost table cap (New.nodesPointer table cap) (BitVec.ofNat 64 (next+1)) (BitVec.ofNat 64 difference)
      secondReady secondInstalled image.geometry.nodes image.geometry.nodesAligned nodesCell "ni" [localVar "t",localVar "d"] splice internalArgs outcome continued with stopped | reached
    · have stoppedCost : leafTarget.clock-leafPost.clock ≤ 2 := stopped.1
      have price : source.clock-leafPost.clock ≤ 6 := by omega
      exact Or.inl ⟨by rw [endpoint]; exact price,stopped.2⟩
    · obtain ⟨internalTarget,inner,internalFrame,internalForward,internalCost,spliced,innerEndpoint⟩ := reached
      have physicalFrame : LocalEffects.erase internalTarget = LocalEffects.erase (freshModel source table cap pointer value next count difference) :=
        internalFrame.trans (NewInternal.model_frame _ _ table cap (BitVec.ofNat 64 (next+1)) (BitVec.ofNat 64 difference) physical)
      have forward : internalTarget.clock ≤ source.clock := by
        change internalTarget.clock ≤ leafTarget.clock at internalForward
        omega
      have price : source.clock-internalTarget.clock ≤ 6 := by
        change leafTarget.clock-internalTarget.clock ≤ 2 at internalCost
        omega
      exact Or.inr ⟨leafTarget,leafPost,internalTarget,inner,physicalFrame,forward,price,spliced,innerEndpoint,endpoint⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.fresh_allocation_trace
