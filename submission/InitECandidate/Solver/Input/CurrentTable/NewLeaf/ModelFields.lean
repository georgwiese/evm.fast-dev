import InitECandidate.Solver.Input.CurrentTable.NewLeaf.NoGrow

namespace InitECandidate.Solver.Input.CurrentTable
open Flapjack PanSemStateFiniteExact

/-- Small projection lemmas keep later state proofs from expanding every
copied field of a long chain of concrete store states. -/
theorem putNode_domain (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base node value : BitVec 64) (offset : Nat) :
    (putNode source base node offset value).memaddrs = source.memaddrs := rfl

theorem putField_domain (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table value : BitVec 64) (offset : Nat) :
    (New.putField source table offset value).memaddrs = source.memaddrs := rfl

theorem putOrder_domain (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap pos node : BitVec 64) :
    (NewLeaf.putOrder source table cap pos node).memaddrs = source.memaddrs := rfl

theorem keyCopy_domain (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer target : BitVec 64) :
    (KeyCopy.result source pointer target).memaddrs = source.memaddrs := rfl

theorem NewLeaf.stored_domain (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos value : BitVec 64) :
    (stored source table cap node pos value).memaddrs = source.memaddrs := by
  simp only [stored,tailStored,putField_domain,putOrder_domain,putNode_domain]

theorem NewLeaf.model_domain (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64) :
    (model source table cap node pos pointer value).memaddrs = source.memaddrs := by
  rw [model,stored_domain,keyCopy_domain,putField_domain]

end InitECandidate.Solver.Input.CurrentTable

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.model_domain
