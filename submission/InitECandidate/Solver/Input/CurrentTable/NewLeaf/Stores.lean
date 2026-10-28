import InitECandidate.Solver.Input.CurrentTable.NewLeaf.Program
import InitECandidate.Solver.Input.CurrentTable.CellGeometry

namespace InitECandidate.Solver.Input.CurrentTable.NewLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch
open Flapjack.Compiler.Encoders.Asm

structure Locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table base node value : BitVec 64) : Prop where
  tableCell : source.locals.lookup (ofString "t") = some (.val (.word table))
  baseCell : source.locals.lookup (ofString "nodes") = some (.val (.word base))
  nodeCell : source.locals.lookup (ofString "n") = some (.val (.word node))
  valueCell : source.locals.lookup (ofString "value") = some (.val (.word value))
  lengthCell : source.locals.lookup (ofString "klen") = some (.val (.word 32#64))

theorem Locals.with_memory {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table base node value : BitVec 64}
    (locals : Locals source table base node value) (memory : BitVec 64 → HolWordLab 64) :
    Locals {source with memory := memory} table base node value :=
  ⟨locals.tableCell,locals.baseCell,locals.nodeCell,locals.valueCell,locals.lengthCell⟩

theorem Locals.with_position {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table base node value : BitVec 64}
    (locals : Locals source table base node value) (pos : BitVec 64) : Locals (bind source "pos" pos) table base node value := by
  exact ⟨(bind_lookup_other _ "pos" "t" pos (by decide)).trans locals.tableCell,
    (bind_lookup_other _ "pos" "nodes" pos (by decide)).trans locals.baseCell,
    (bind_lookup_other _ "pos" "n" pos (by decide)).trans locals.nodeCell,
    (bind_lookup_other _ "pos" "value" pos (by decide)).trans locals.valueCell,
    (bind_lookup_other _ "pos" "klen" pos (by decide)).trans locals.lengthCell⟩

def putOrder (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap pos node : BitVec 64) :=
  {source with memory := StoreWord.put source.memory (slot (New.orderPointer table cap) pos 8) node}

def tailStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos : BitVec 64) :=
  New.putField (putOrder
    (putNode (putNode source (New.nodesPointer table cap) node 16 pos) (New.nodesPointer table cap) node 24 256#64)
    table cap pos node) table 24 (pos+1#64)

theorem order_address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap pos : BitVec 64)
    (domain : source.memaddrs = InitE.ordinaryDomain) (geometry : New.Geometry table cap) (aligned : table.toNat%8 = 0)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word pos)))
    (orderCell : source.memory (table+48#64) = .word (New.orderPointer table cap)) :
    eval source orderAddress = some (.val (.word (slot (New.orderPointer table cap) pos 8))) := by
  have orderRead := NewNode.field_read source table (New.orderPointer table cap) 48 domain geometry.table aligned
    (by decide) (by decide) tableCell orderCell
  simp only [eval] at orderRead ⊢
  rw [orderAddress,evalHOLExact]
  simp only [evalListHOLExact,orderRead]
  simp [evalHOLExact,evalListHOLExact,localVar,posCell,valueIsWord,valueWord,panOpHOL,wordOpHOL,wordOp,slot]

/-- The original leaf tail stores the insertion position, leaf marker,
order-array entry and incremented count, and returns the allocated index. -/
theorem tail_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos value : BitVec 64)
    (domain : source.memaddrs = InitE.ordinaryDomain) (geometry : New.Geometry table cap) (aligned : table.toNat%8 = 0)
    (inside : node.toNat ≤ cap.toNat) (posInside : pos.toNat ≤ cap.toNat)
    (locals : Locals source table (New.nodesPointer table cap) node value)
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word pos)))
    (orderCell : source.memory (table+48#64) = .word (New.orderPointer table cap)) :
    evaluateHOLFiniteState source afterPosition =
      (some (.returned (.val (.word node))),emptyLocalsHOLFinite (tailStored source table cap node pos)) := by
  let base := New.nodesPointer table cap
  let one := putNode source base node 16 pos
  let two := putNode one base node 24 256#64
  let three := putOrder two table cap pos node
  have first := store_node source base node cap pos 16 (localVar "pos") domain geometry.nodes geometry.nodesAligned inside
    (by decide) (by decide) locals.baseCell locals.nodeCell (Request.local_word source "pos" pos posCell)
  have marker : eval one (.panop .mul [localVar "klen",.const 8#64]) = some (.val (.word 256#64)) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,locals.lengthCell,panOpHOL,valueIsWord,valueWord,one,putNode]
  have second := store_node one base node cap 256#64 24 _ domain geometry.nodes geometry.nodesAligned inside
    (by decide) (by decide) locals.baseCell locals.nodeCell marker
  have header : two.memory (table+48#64) = .word (New.orderPointer table cap) := by
    have away16 := geometry.header_away node inside 16 48 (by decide) (by decide)
    have away24 := geometry.header_away node inside 24 48 (by decide) (by decide)
    change table+48#64 ≠ FindLeaf.cell base node 16 at away16
    change table+48#64 ≠ FindLeaf.cell base node 24 at away24
    change StoreWord.put (StoreWord.put source.memory (FindLeaf.cell base node 16) pos) (FindLeaf.cell base node 24) 256#64 (table+48#64) = _
    simp only [StoreWord.put,if_neg away16,if_neg away24]
    exact orderCell
  have orderRead := order_address_read two table cap pos domain geometry aligned locals.tableCell posCell header
  have mapped := AllocatedBytes.word_mapped two (slot (New.orderPointer table cap) pos 8) 8 0 domain
    (geometry.order_slot pos posInside) (by decide)
    (slot_aligned (New.orderPointer table cap) pos cap 8 geometry.order posInside geometry.orderAligned (by decide)) (by decide)
  have third := StoreWord.execute two orderAddress (localVar "n") (slot (New.orderPointer table cap) pos 8) node
    orderRead (Request.local_word two "n" node locals.nodeCell) (by simpa [byteAddress] using mapped)
  change evaluateHOLFiniteState two (.store orderAddress (localVar "n")) = (none,three) at third
  have countRead : eval three (.op .add [localVar "pos",.const 1#64]) = some (.val (.word (pos+1#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,three,putOrder,two,one,putNode,posCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have fourth := New.store_field three table (pos+1#64) 24 _ domain geometry.table aligned (by decide) (by decide) locals.tableCell countRead
  change evaluateHOLFiniteState three (.store (NewNode.address 24) (.op .add [localVar "pos",.const 1#64])) = _ at fourth
  rw [shapes.2.2.2.2.2.2.2.2.1,evaluateHOLFiniteState_seq_line780,first]
  simp only
  rw [shapes.2.2.2.2.2.2.2.2.2.1,evaluateHOLFiniteState_seq_line780,second]
  simp only
  rw [shapes.2.2.2.2.2.2.2.2.2.2.1,evaluateHOLFiniteState_seq_line780,third]
  simp only
  rw [shapes.2.2.2.2.2.2.2.2.2.2.2,evaluateHOLFiniteState_seq_line780,fourth]
  simp [evaluateHOLFiniteState_return,evalHOLExact,localVar,New.putField,putOrder,putNode,locals.nodeCell,
    tailStored,three,two,one,base,shapeOfHOLExact,sizeOfShapeWithContextHOL]

def stored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos value : BitVec 64) :=
  tailStored (putNode (putNode source (New.nodesPointer table cap) node 0 0#64) (New.nodesPointer table cap) node 8 value)
    table cap node pos

def storesReturned (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos value : BitVec 64) :=
  restore (putNode (putNode source (New.nodesPointer table cap) node 0 0#64) (New.nodesPointer table cap) node 8 value) "pos"
    (emptyLocalsHOLFinite (tailStored
      (bind (putNode (putNode source (New.nodesPointer table cap) node 0 0#64) (New.nodesPointer table cap) node 8 value) "pos" pos)
      table cap node pos))

theorem stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos value : BitVec 64)
    (domain : source.memaddrs = InitE.ordinaryDomain) (geometry : New.Geometry table cap) (aligned : table.toNat%8 = 0)
    (inside : node.toNat ≤ cap.toNat) (posInside : pos.toNat ≤ cap.toNat)
    (locals : Locals source table (New.nodesPointer table cap) node value)
    (countCell : source.memory (table+24#64) = .word pos)
    (orderCell : source.memory (table+48#64) = .word (New.orderPointer table cap)) :
    evaluateHOLFiniteState source stores =
      (some (.returned (.val (.word node))),storesReturned source table cap node pos value) := by
  let base := New.nodesPointer table cap
  let one := putNode source base node 0 0#64
  let two := putNode one base node 8 value
  have first := store_node source base node cap 0#64 0 (.const 0#64) domain geometry.nodes geometry.nodesAligned inside
    (by decide) (by decide) locals.baseCell locals.nodeCell rfl
  have second := store_node one base node cap value 8 (localVar "value") domain geometry.nodes geometry.nodesAligned inside
    (by decide) (by decide) locals.baseCell locals.nodeCell (Request.local_word one "value" value locals.valueCell)
  have fields (offset : Nat) (small : offset < 88) : two.memory (table+BitVec.ofNat 64 offset) = source.memory (table+BitVec.ofNat 64 offset) := by
    have away0 := geometry.header_away node inside 0 offset (by decide) small
    have away8 := geometry.header_away node inside 8 offset (by decide) small
    change table+BitVec.ofNat 64 offset ≠ FindLeaf.cell base node 0 at away0
    change table+BitVec.ofNat 64 offset ≠ FindLeaf.cell base node 8 at away8
    simp only [two,one,putNode,StoreWord.put,if_neg away0,if_neg away8]
  have countRead := NewNode.field_read two table pos 24 domain geometry.table aligned (by decide) (by decide) locals.tableCell
    ((fields 24 (by decide)).trans countCell)
  have enteredLocals : Locals (bind two "pos" pos) table base node value := (locals.with_memory two.memory).with_position pos
  have tail := tail_execute (bind two "pos" pos) table cap node pos value domain geometry aligned inside posInside enteredLocals
    (bind_lookup_same _ _ _) ((fields 48 (by decide)).trans orderCell)
  have last : evaluateHOLFiniteState two afterValue = (some (.returned (.val (.word node))),storesReturned source table cap node pos value) := by
    rw [shapes.2.2.2.2.2.2.2.1]
    exact ScalarScope.declare_execute _ _ "pos" _ pos afterPosition _ countRead tail
  rw [shapes.2.2.2.2.2.1,evaluateHOLFiniteState_seq_line780,first]
  simp only
  rw [shapes.2.2.2.2.2.2.1,evaluateHOLFiniteState_seq_line780,second]
  exact last

theorem stores_returned_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos value : BitVec 64) :
    LocalEffects.erase (storesReturned source table cap node pos value) = LocalEffects.erase (stored source table cap node pos value) ∧
      (storesReturned source table cap node pos value).clock = source.clock := ⟨rfl,rfl⟩

end InitECandidate.Solver.Input.CurrentTable.NewLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.tail_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.stores_execute
