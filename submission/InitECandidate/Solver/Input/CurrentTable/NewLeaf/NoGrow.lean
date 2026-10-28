import InitECandidate.Solver.Input.CurrentTable.NewLeaf.Allocate
import InitECandidate.Solver.Input.WordEnvironment
import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.Input.CurrentTable.NewLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

def nodeEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table node : BitVec 64) :=
  bind (New.putField {source with clock := source.clock-1} table 64 (node+1#64)) "n" node
def returnedState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64) :=
  restore source "n" (afterNodeReturned (nodeEntry source table node) table cap node pos pointer value)

/-- The unchanged current leaf constructor follows its real no-grow node
call, key copy and all six leaf/order/count stores. -/
theorem body_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64) (key : KeyBits.Key)
    (ready : NewNode.Context source table node cap) (fields : Fields source table cap node pos pointer key)
    (beforeTable : pointer.toNat+32 ≤ table.toNat) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value") = some (.val (.word value))) (enough : 3 ≤ source.clock) :
    evaluateHOLFiniteState source body =
      (some (.returned (.val (.word node))),returnedState source table cap node pos pointer value) := by
  classical
  obtain ⟨callee,called,calleeTable⟩ := word_environment source.code.lookup (ofString "htab_new_node")
    (ofString "t") NewNode.body .one table (NewNode.original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have calleeReady : NewNode.Context entry table node cap := ready.of_frame rfl
  have args : evalListHOLFinite source [localVar "t"] = some [.val (.word table)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,tableCell]
  have run := CallNormal.return_execute source (NewNode.returnedState entry table node) "n" .one (ofString "htab_new_node")
    [localVar "t"] [.val (.word table)] NewNode.body afterNode callee .one (.val (.word node)) args called (by omega)
    (calleeReady.execute calleeTable) (by simp [shapeOfHOLExact,shapeEqHOL])
  have resumed : CallNormal.continuationEntry source (NewNode.returnedState entry table node) "n" (.val (.word node)) =
      nodeEntry source table node := rfl
  have allocated : Fields (nodeEntry source table node) table cap node pos pointer key :=
    (fields.after_next beforeTable).of_frame rfl
  have locals : EntryLocals (nodeEntry source table node) table node pointer value :=
    ⟨(bind_lookup_other _ "n" "t" node (by decide)).trans tableCell,bind_lookup_same _ _ _,
      (bind_lookup_other _ "n" "key" node (by decide)).trans keyCell,
      (bind_lookup_other _ "n" "value" node (by decide)).trans valueCell⟩
  have tail := after_node_execute (nodeEntry source table node) table cap node pos pointer value key allocated locals installed
    (by change 2 ≤ source.clock-1; omega)
  rw [shapes.1,run,resumed,tail]
  rfl

def model (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64) :=
  stored (KeyCopy.result (New.putField source table 64 (node+1#64)) pointer (slot (New.keysPointer table) node 32)) table cap node pos value

theorem returned_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64) :
    LocalEffects.erase (returnedState source table cap node pos pointer value) =
      LocalEffects.erase (model source table cap node pos pointer value) ∧
    (returnedState source table cap node pos pointer value).clock = source.clock-3 := by
  constructor
  · rfl
  · change source.clock-1-2 = source.clock-3
    omega

theorem price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64) (key : KeyBits.Key)
    (ready : NewNode.Context source table node cap) (fields : Fields source table cap node pos pointer key)
    (beforeTable : pointer.toNat+32 ≤ table.toNat) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value") = some (.val (.word value))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock ≤ 3 := by
  by_cases enough : 3 ≤ source.clock
  · rw [body_execute source table cap node pos pointer value key ready fields beforeTable installed tableCell keyCell valueCell enough,
      (returned_frame source table cap node pos pointer value).2]
    omega
  · omega

end InitECandidate.Solver.Input.CurrentTable.NewLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.body_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.returned_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.price
