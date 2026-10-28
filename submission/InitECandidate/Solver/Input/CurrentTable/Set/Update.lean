import InitECandidate.Solver.Input.CurrentTable.Set.ComparisonEntry
import InitECandidate.Solver.Input.LocalWord

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch
open Flapjack.Compiler.Encoders.Asm

def updateAddress : ExpHOL 64 := .op .add [.load .one (.op .add [localVar "t",.const 40#64]),
  .panop .mul [localVar "leaf",.const 32#64],.const 8#64]

def updated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap leaf value : BitVec 64) :=
  {source with memory := StoreWord.put source.memory (FindLeaf.cell (New.nodesPointer table cap) leaf 8) value}

theorem update_shape : updateBody = .seq (.store updateAddress (localVar "value")) (.return (.const 0#64)) :=
  guard_shapes.2.2.2.2.1

theorem update_address_read {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root pointer value leaf : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (locals : LookupLocals source table pointer value leaf) :
    eval source updateAddress = some (.val (.word (FindLeaf.cell (New.nodesPointer table cap) leaf 8))) := by
  have nodesRead := FindLeaf.header_read source table (New.nodesPointer table cap) 40 image.domain image.geometry.table image.aligned
    (by decide) (by decide) locals.locals.tableCell image.nodesCell
  change eval source (.load .one (.op .add [localVar "t",.const 40#64])) = _ at nodesRead
  simp only [eval] at nodesRead ⊢
  rw [updateAddress,evalHOLExact]
  simp only [evalListHOLExact,nodesRead]
  simp [evalHOLExact,evalListHOLExact,localVar,locals.leafCell,valueIsWord,valueWord,panOpHOL,wordOpHOL,wordOp,
    FindLeaf.cell,BitVec.add_assoc]

/-- The actual existing-key branch writes only its real leaf value and
returns zero. All accesses are derived from this mapped current table. -/
theorem update_execute {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root pointer value leaf : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (locals : LookupLocals source table pointer value leaf) (member : valid leaf) :
    evaluateHOLFiniteState source updateBody = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite (updated source table cap leaf value)) := by
  have inside := image.node_inside leaf member
  have arena := image.geometry.node_slot leaf inside
  have aligned := slot_aligned (New.nodesPointer table cap) leaf cap 32 image.geometry.nodes inside image.geometry.nodesAligned (by decide)
  have mapped := AllocatedBytes.word_mapped source (slot (New.nodesPointer table cap) leaf 32) 32 8 image.domain arena (by decide) aligned (by decide)
  change source.memaddrs (FindLeaf.cell (New.nodesPointer table cap) leaf 8) at mapped
  have store := StoreWord.execute source updateAddress (localVar "value") (FindLeaf.cell (New.nodesPointer table cap) leaf 8) value
    (update_address_read image locals) (Request.local_word source "value" value locals.locals.valueCell) mapped
  rw [update_shape,evaluateHOLFiniteState_seq_line780,store]
  simp [evaluateHOLFiniteState_return,evalHOLExact,updated,shapeOfHOLExact,sizeOfShapeWithContextHOL]

/-- The real true-comparison continuation performs that same update and
cannot reach the later difference/search calls. It spends zero body ticks. -/
theorem after_compare_one {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root pointer value leaf : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (locals : LookupLocals source table pointer value leaf) (member : valid leaf)
    (eqCell : source.locals.lookup (ofString "eq") = some (.val (.word 1#64))) :
    evaluateHOLFiniteState source afterCompare = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite (updated source table cap leaf value)) := by
  have read : eval source (.cmp .notEqual (localVar "eq") (.const 0#64)) = some (.val (.word 1#64)) := by
    simp [eval,evalHOLExact,localVar,eqCell,wordCmpHOL]
  simp only [eval] at read
  rw [entry_shapes.2.2.2.2.2.1,guard_shapes.2.2.2.1,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,read]
  simp only [if_neg (show (1#64 : BitVec 64) ≠ 0 from by decide),update_execute image locals member]

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.update_address_read
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.update_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.after_compare_one
