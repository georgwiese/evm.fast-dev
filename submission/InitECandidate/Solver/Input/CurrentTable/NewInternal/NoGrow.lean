import InitECandidate.Solver.Input.CurrentTable.NewInternal.Program
import InitECandidate.Solver.Input.CurrentTable.NewNode.Context
import InitECandidate.Solver.Input.WordEnvironment
import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.Input.CurrentTable.NewInternal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

def stored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base node bit : BitVec 64) :=
  putNode (putNode (putNode (putNode source base node 0 0#64) base node 8 0#64) base node 16 0#64) base node 24 bit

/-- The actual four internal-node writes execute without any loop ticks. -/
theorem stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base node cap bit : BitVec 64)
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (array : AllocatedBytes.Arena base (32*(cap.toNat+1))) (aligned : base.toNat%8 = 0)
    (inside : node.toNat ≤ cap.toNat)
    (baseCell : source.locals.lookup (ofString "nodes") = some (.val (.word base)))
    (nodeCell : source.locals.lookup (ofString "n") = some (.val (.word node)))
    (bitCell : source.locals.lookup (ofString "bit") = some (.val (.word bit))) :
    evaluateHOLFiniteState source stores =
      (some (.returned (.val (.word node))),emptyLocalsHOLFinite (stored source base node bit)) := by
  let one := putNode source base node 0 0#64
  let two := putNode one base node 8 0#64
  let three := putNode two base node 16 0#64
  have first := store_node source base node cap 0#64 0 (.const 0#64) domain array aligned inside (by decide) (by decide) baseCell nodeCell rfl
  have second := store_node one base node cap 0#64 8 (.const 0#64) domain array aligned inside (by decide) (by decide) baseCell nodeCell rfl
  have third := store_node two base node cap 0#64 16 (.const 0#64) domain array aligned inside (by decide) (by decide) baseCell nodeCell rfl
  have fourth := store_node three base node cap bit 24 (localVar "bit") domain array aligned inside (by decide) (by decide) baseCell nodeCell
    (Request.local_word three "bit" bit bitCell)
  rw [shapes.2.2.1,evaluateHOLFiniteState_seq_line780,first]
  simp only
  rw [shapes.2.2.2.1,evaluateHOLFiniteState_seq_line780,second]
  simp only
  rw [shapes.2.2.2.2.1,evaluateHOLFiniteState_seq_line780,third]
  simp only
  rw [shapes.2.2.2.2.2,evaluateHOLFiniteState_seq_line780,fourth]
  simp [evaluateHOLFiniteState_return,evalHOLExact,localVar,putNode,nodeCell,stored,one,two,three,
    shapeOfHOLExact,sizeOfShapeWithContextHOL]

def nodeEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table node : BitVec 64) :=
  bind (New.putField {source with clock := source.clock-1} table 64 (node+1#64)) "n" node

def returnedState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table base node bit : BitVec 64) :=
  restore source "n" (restore (nodeEntry source table node) "nodes"
    (emptyLocalsHOLFinite (stored (bind (nodeEntry source table node) "nodes" base) base node bit)))

/-- Real no-grow allocation followed by the original internal-node stores.
The complete body spends one call tick and writes the physical fresh slot. -/
theorem body_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap base node bit : BitVec 64)
    (ready : NewNode.Context source table node cap) (installed : OriginalCode.Installed source.code)
    (array : AllocatedBytes.Arena base (32*(cap.toNat+1))) (aligned : base.toNat%8 = 0)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (bitCell : source.locals.lookup (ofString "bit") = some (.val (.word bit)))
    (nodesCell : source.memory (table+40#64) = .word base) (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source body =
      (some (.returned (.val (.word node))),returnedState source table base node bit) := by
  classical
  obtain ⟨callee,called,calleeTable⟩ := word_environment source.code.lookup (ofString "htab_new_node")
    (ofString "t") NewNode.body .one table (NewNode.original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have calleeReady : NewNode.Context entry table node cap := ready.of_frame rfl
  have args : evalListHOLFinite source [localVar "t"] = some [.val (.word table)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,tableCell]
  have run := CallNormal.return_execute source (NewNode.returnedState entry table node) "n" .one (ofString "htab_new_node")
    [localVar "t"] [.val (.word table)] NewNode.body afterNode callee .one (.val (.word node)) args called enough
    (calleeReady.execute calleeTable) (by simp [shapeOfHOLExact,shapeEqHOL])
  have resumed : CallNormal.continuationEntry source (NewNode.returnedState entry table node) "n" (.val (.word node)) =
      nodeEntry source table node := rfl
  let resumedEntry := nodeEntry source table node
  have callerTable : resumedEntry.locals.lookup (ofString "t") = some (.val (.word table)) :=
    (bind_lookup_other _ "n" "t" node (by decide)).trans tableCell
  have header : resumedEntry.memory (table+40#64) = .word base := by
    change StoreWord.put source.memory (table+64#64) (node+1#64) (table+40#64) = _
    have away : table+40#64 ≠ table+64#64 := by simp
    simp only [StoreWord.put,if_neg away]
    exact nodesCell
  have baseRead := NewNode.field_read resumedEntry table base 40 ready.domain ready.arena ready.aligned (by decide) (by decide) callerTable header
  have enteredBase : (bind resumedEntry "nodes" base).locals.lookup (ofString "nodes") = some (.val (.word base)) := bind_lookup_same _ _ _
  have enteredNode : (bind resumedEntry "nodes" base).locals.lookup (ofString "n") = some (.val (.word node)) :=
    (bind_lookup_other _ "nodes" "n" base (by decide)).trans (bind_lookup_same _ _ _)
  have enteredBit : (bind resumedEntry "nodes" base).locals.lookup (ofString "bit") = some (.val (.word bit)) :=
    (bind_lookup_other _ "nodes" "bit" base (by decide)).trans ((bind_lookup_other _ "n" "bit" node (by decide)).trans bitCell)
  have tail := stores_execute (bind resumedEntry "nodes" base) base node cap bit ready.domain array aligned ready.room enteredBase enteredNode enteredBit
  have continuation : evaluateHOLFiniteState resumedEntry afterNode =
      (some (.returned (.val (.word node))),restore resumedEntry "nodes" (emptyLocalsHOLFinite (stored (bind resumedEntry "nodes" base) base node bit))) := by
    rw [shapes.2.1]
    exact ScalarScope.declare_execute _ _ "nodes" _ base stores _ baseRead tail
  rw [shapes.1,run,resumed,continuation]
  rfl

theorem returned_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table base node bit : BitVec 64) :
    LocalEffects.erase (returnedState source table base node bit) =
      LocalEffects.erase (stored (New.putField source table 64 (node+1#64)) base node bit) ∧
    (returnedState source table base node bit).clock = source.clock-1 := ⟨rfl,rfl⟩

theorem price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap base node bit : BitVec 64)
    (ready : NewNode.Context source table node cap) (installed : OriginalCode.Installed source.code)
    (array : AllocatedBytes.Arena base (32*(cap.toNat+1))) (aligned : base.toNat%8 = 0)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (bitCell : source.locals.lookup (ofString "bit") = some (.val (.word bit)))
    (nodesCell : source.memory (table+40#64) = .word base) :
    source.clock-(evaluateHOLFiniteState source body).2.clock ≤ 1 := by
  by_cases enough : 1 ≤ source.clock
  · rw [body_execute source table cap base node bit ready installed array aligned tableCell bitCell nodesCell enough,
      (returned_frame source table base node bit).2]
    omega
  · omega

end InitECandidate.Solver.Input.CurrentTable.NewInternal

#print axioms InitECandidate.Solver.Input.CurrentTable.NewInternal.stores_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.NewInternal.body_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.NewInternal.price
