import InitECandidate.Solver.Input.CurrentTable.NewLeaf.Stores
import InitECandidate.Solver.Input.CurrentTable.KeyCopyFrame

namespace InitECandidate.Solver.Input.CurrentTable.NewLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- Physical entry after the real fresh index has been allocated. No new
node contents or future successful copying/stores are supplied. -/
structure Fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer : BitVec 64) (key : KeyBits.Key) : Prop where
  geometry : New.Geometry table cap
  aligned : table.toNat%8 = 0
  inside : node.toNat ≤ cap.toNat
  posInside : pos.toNat ≤ cap.toNat
  lengthCell : source.memory (table+0#64) = .word 32#64
  strideCell : source.memory (table+8#64) = .word 32#64
  countCell : source.memory (table+24#64) = .word pos
  keysCell : source.memory (table+32#64) = .word (New.keysPointer table)
  nodesCell : source.memory (table+40#64) = .word (New.nodesPointer table cap)
  orderCell : source.memory (table+48#64) = .word (New.orderPointer table cap)
  copy : KeyCopy.Context source pointer (slot (New.keysPointer table) node 32) key

theorem Fields.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table cap node pos pointer : BitVec 64} {key : KeyBits.Key}
    (fields : Fields source table cap node pos pointer key) (frame : LocalEffects.erase target = LocalEffects.erase source) :
    Fields target table cap node pos pointer key := by
  have memory := LocalEffects.memory_of_erase source target frame
  exact ⟨fields.geometry,fields.aligned,fields.inside,fields.posInside,by rw [memory]; exact fields.lengthCell,
    by rw [memory]; exact fields.strideCell,by rw [memory]; exact fields.countCell,
    by rw [memory]; exact fields.keysCell,by rw [memory]; exact fields.nodesCell,
    by rw [memory]; exact fields.orderCell,fields.copy.of_frame frame⟩

structure EntryLocals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table node pointer value : BitVec 64) : Prop where
  tableCell : source.locals.lookup (ofString "t") = some (.val (.word table))
  nodeCell : source.locals.lookup (ofString "n") = some (.val (.word node))
  keyCell : source.locals.lookup (ofString "key") = some (.val (.word pointer))
  valueCell : source.locals.lookup (ofString "value") = some (.val (.word value))

def lengthEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) := bind source "klen" 32#64
def strideEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) := bind (lengthEntry source) "stride" 32#64
def copiedEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table node pointer : BitVec 64) :=
  KeyCopy.result (strideEntry source) pointer (slot (New.keysPointer table) node 32)
def afterNodeReturned (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64) :=
  restore source "klen" (restore (lengthEntry source) "stride" (restore (copiedEntry source table node pointer) "nodes"
    (storesReturned (bind (copiedEntry source table node pointer) "nodes" (New.nodesPointer table cap)) table cap node pos value)))

theorem copy_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64) (key : KeyBits.Key)
    (fields : Fields source table cap node pos pointer key) (locals : EntryLocals source table node pointer value) :
    evalListHOLFinite (strideEntry source) (h:=fun address => Classical.propDecidable ((strideEntry source).memaddrs address)) copyArguments =
      some [.val (.word (slot (New.keysPointer table) node 32)),.val (.word pointer),.val (.word 32#64)] := by
  classical
  let entered := strideEntry source
  have tableCell : entered.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp only [entered,strideEntry,lengthEntry,bind_lookup_other _ "stride" "t" 32#64 (by decide),bind_lookup_other _ "klen" "t" 32#64 (by decide)]
    exact locals.tableCell
  have keyRead := NewNode.field_read entered table (New.keysPointer table) 32 fields.copy.domain fields.geometry.table fields.aligned
    (by decide) (by decide) tableCell fields.keysCell
  have nodeCell : entered.locals.lookup (ofString "n") = some (.val (.word node)) := by
    simp only [entered,strideEntry,lengthEntry,bind_lookup_other _ "stride" "n" 32#64 (by decide),bind_lookup_other _ "klen" "n" 32#64 (by decide)]
    exact locals.nodeCell
  have pointerCell : entered.locals.lookup (ofString "key") = some (.val (.word pointer)) := by
    simp only [entered,strideEntry,lengthEntry,bind_lookup_other _ "stride" "key" 32#64 (by decide),bind_lookup_other _ "klen" "key" 32#64 (by decide)]
    exact locals.keyCell
  have strideCell : entered.locals.lookup (ofString "stride") = some (.val (.word 32#64)) := bind_lookup_same _ _ _
  have lengthCell : entered.locals.lookup (ofString "klen") = some (.val (.word 32#64)) :=
    (bind_lookup_other _ "stride" "klen" 32#64 (by decide)).trans (bind_lookup_same _ _ _)
  simp only [eval] at keyRead
  change evalListHOLExact entered.toExact copyArguments = _
  rw [copyArguments,evalListHOLExact,evalHOLExact]
  simp only [evalListHOLExact,keyRead]
  simp [evalHOLExact,evalListHOLExact,localVar,nodeCell,pointerCell,strideCell,lengthCell,
    valueIsWord,valueWord,panOpHOL,wordOpHOL,wordOp,slot]

/-- Actual post-allocation leaf continuation, including the real memcpy
and every node/order/count store. It pays exactly two source ticks. -/
theorem after_node_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64) (key : KeyBits.Key)
    (fields : Fields source table cap node pos pointer key) (locals : EntryLocals source table node pointer value)
    (installed : OriginalCode.Installed source.code) (enough : 2 ≤ source.clock) :
    evaluateHOLFiniteState source afterNode =
      (some (.returned (.val (.word node))),afterNodeReturned source table cap node pos pointer value) := by
  have tableLength : (lengthEntry source).locals.lookup (ofString "t") = some (.val (.word table)) :=
    (bind_lookup_other _ "klen" "t" 32#64 (by decide)).trans locals.tableCell
  have tableStride : (strideEntry source).locals.lookup (ofString "t") = some (.val (.word table)) :=
    (bind_lookup_other _ "stride" "t" 32#64 (by decide)).trans tableLength
  have readLength := NewNode.field_read source table 32#64 0 fields.copy.domain fields.geometry.table fields.aligned
    (by decide) (by decide) locals.tableCell fields.lengthCell
  have readStride := NewNode.field_read (lengthEntry source) table 32#64 8 fields.copy.domain fields.geometry.table fields.aligned
    (by decide) (by decide) tableLength fields.strideCell
  have copyReady : KeyCopy.Context (strideEntry source) pointer (slot (New.keysPointer table) node 32) key := fields.copy.of_frame rfl
  have copied := copyReady.execute installed copyArguments (copy_arguments source table cap node pos pointer value key fields locals) enough
  change evaluateHOLFiniteState (strideEntry source) (.call (some (none,none)) (ofString "memcpy") copyArguments) =
    (none,copiedEntry source table node pointer) at copied
  let next := copiedEntry source table node pointer
  have header (offset : Nat) (small : offset < 88) : next.memory (table+BitVec.ofNat 64 offset) = source.memory (table+BitVec.ofNat 64 offset) := by
    apply KeyCopy.memory_before
    · exact fields.copy.targetArena
    · have address := byteAddress_toNat table offset (by have := fields.geometry.table.upper; omega)
      change (table+BitVec.ofNat 64 offset).toNat = table.toNat+offset at address
      have target := slot_number (New.keysPointer table) node cap 32 fields.geometry.keys fields.inside
      rw [address,target]
      have := fields.geometry.tableBefore
      omega
  have readNodes := NewNode.field_read next table (New.nodesPointer table cap) 40 fields.copy.domain fields.geometry.table fields.aligned
    (by decide) (by decide) tableStride ((header 40 (by decide)).trans fields.nodesCell)
  have enteredLocals : Locals (bind next "nodes" (New.nodesPointer table cap)) table (New.nodesPointer table cap) node value := by
    constructor
    · exact (bind_lookup_other _ "nodes" "t" _ (by decide)).trans tableStride
    · exact bind_lookup_same _ _ _
    · exact (bind_lookup_other _ "nodes" "n" _ (by decide)).trans
        ((bind_lookup_other _ "stride" "n" 32#64 (by decide)).trans ((bind_lookup_other _ "klen" "n" 32#64 (by decide)).trans locals.nodeCell))
    · exact (bind_lookup_other _ "nodes" "value" _ (by decide)).trans
        ((bind_lookup_other _ "stride" "value" 32#64 (by decide)).trans ((bind_lookup_other _ "klen" "value" 32#64 (by decide)).trans locals.valueCell))
    · exact (bind_lookup_other _ "nodes" "klen" _ (by decide)).trans
        ((bind_lookup_other _ "stride" "klen" 32#64 (by decide)).trans (bind_lookup_same _ _ _))
  have tail := stores_execute (bind next "nodes" (New.nodesPointer table cap)) table cap node pos value fields.copy.domain
    fields.geometry fields.aligned fields.inside fields.posInside enteredLocals
    ((header 24 (by decide)).trans fields.countCell) ((header 48 (by decide)).trans fields.orderCell)
  have finish : evaluateHOLFiniteState next afterCopy =
      (some (.returned (.val (.word node))),restore next "nodes" (storesReturned (bind next "nodes" (New.nodesPointer table cap)) table cap node pos value)) := by
    rw [shapes.2.2.2.2.1]
    exact ScalarScope.declare_execute _ _ "nodes" _ (New.nodesPointer table cap) stores _ readNodes tail
  have copyTail : evaluateHOLFiniteState (strideEntry source) copyPhase =
      (some (.returned (.val (.word node))),restore next "nodes" (storesReturned (bind next "nodes" (New.nodesPointer table cap)) table cap node pos value)) := by
    rw [shapes.2.2.2.1,evaluateHOLFiniteState_seq_line780,copied]
    exact finish
  have middle : evaluateHOLFiniteState (lengthEntry source) afterLength =
      (some (.returned (.val (.word node))),restore (lengthEntry source) "stride"
        (restore next "nodes" (storesReturned (bind next "nodes" (New.nodesPointer table cap)) table cap node pos value))) := by
    rw [shapes.2.2.1]
    exact ScalarScope.declare_execute _ _ "stride" _ 32#64 copyPhase _ readStride copyTail
  rw [shapes.2.1]
  exact ScalarScope.declare_execute _ _ "klen" _ 32#64 afterLength _ readLength middle

theorem after_node_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64) :
    LocalEffects.erase (afterNodeReturned source table cap node pos pointer value) =
      LocalEffects.erase (stored (KeyCopy.result source pointer (slot (New.keysPointer table) node 32)) table cap node pos value) ∧
    (afterNodeReturned source table cap node pos pointer value).clock = source.clock-2 := ⟨rfl,rfl⟩

end InitECandidate.Solver.Input.CurrentTable.NewLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.copy_arguments
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.after_node_execute
