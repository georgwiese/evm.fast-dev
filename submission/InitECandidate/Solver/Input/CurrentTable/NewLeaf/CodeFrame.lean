import InitECandidate.Solver.Input.CurrentTable.NewLeaf.ModelFields

namespace InitECandidate.Solver.Input.CurrentTable
open Flapjack PanSemStateFiniteExact

theorem putNode_code (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base node value : BitVec 64) (offset : Nat) :
    (putNode source base node offset value).code = source.code := rfl
theorem putField_code (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table value : BitVec 64) (offset : Nat) :
    (New.putField source table offset value).code = source.code := rfl
theorem putOrder_code (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap pos node : BitVec 64) :
    (NewLeaf.putOrder source table cap pos node).code = source.code := rfl
theorem keyCopy_code (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer target : BitVec 64) :
    (KeyCopy.result source pointer target).code = source.code := rfl

theorem NewLeaf.stored_code (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos value : BitVec 64) :
    (stored source table cap node pos value).code = source.code := by
  simp only [stored,tailStored,putField_code,putOrder_code,putNode_code]

theorem NewLeaf.model_code (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64) :
    (model source table cap node pos pointer value).code = source.code := by
  rw [model,stored_code,keyCopy_code,putField_code]

end InitECandidate.Solver.Input.CurrentTable

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.model_code
