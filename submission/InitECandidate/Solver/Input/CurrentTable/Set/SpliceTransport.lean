import InitECandidate.Solver.Input.CurrentTable.Set.SpliceMemory

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix QueryBranch

private theorem refreshed_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) :
    LocalEffects.erase (bind source "nodes" base) = LocalEffects.erase source := rfl

theorem parents_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base node parent leaf internal : BitVec 64)
    (frame : LocalEffects.erase target = LocalEffects.erase source) :
    LocalEffects.erase (parentsStored target base node parent leaf internal) = LocalEffects.erase (parentsStored source base node parent leaf internal) :=
  node_frame _ _ base node internal 0 (node_frame _ _ base leaf internal 0 (node_frame source target base internal parent 0 frame))

theorem children_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (base node leaf internal : BitVec 64) (query : KeyBits.Key) (difference : Nat)
    (frame : LocalEffects.erase target = LocalEffects.erase source) :
    LocalEffects.erase (childrenStored target base node leaf internal query difference) = LocalEffects.erase (childrenStored source base node leaf internal query difference) :=
  node_frame _ _ base internal _ 16 (node_frame source target base internal _ 8 frame)

theorem attached_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent internal oldLeft : BitVec 64)
    (frame : LocalEffects.erase target = LocalEffects.erase source) :
    LocalEffects.erase (attached target table cap node parent internal oldLeft) = LocalEffects.erase (attached source table cap node parent internal oldLeft) := by
  unfold attached
  split
  · exact header_frame source target table internal 56 frame
  · split <;> exact node_frame source target _ parent internal _ frame

/-- The exact splice memory model transports across the genuine callee
return frame, retaining all physical fields and arbitrary caller locals. -/
theorem splice_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent leaf internal oldLeft : BitVec 64)
    (query : KeyBits.Key) (difference : Nat) (frame : LocalEffects.erase target = LocalEffects.erase source) :
    LocalEffects.erase (spliceResult target table cap node parent leaf internal oldLeft query difference) =
      LocalEffects.erase (spliceResult source table cap node parent leaf internal oldLeft query difference) := by
  have start : LocalEffects.erase (bind target "nodes" (New.nodesPointer table cap)) =
      LocalEffects.erase (bind source "nodes" (New.nodesPointer table cap)) :=
    (refreshed_frame target _).trans (frame.trans (refreshed_frame source _).symm)
  exact attached_frame _ _ table cap node parent internal oldLeft
    (children_frame _ _ _ node leaf internal query difference (parents_frame _ _ _ node parent leaf internal start))

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.splice_frame
