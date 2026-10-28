import InitECandidate.Solver.Input.CurrentTable.Set.SpliceLocals
import InitECandidate.Solver.Input.CurrentTable.EarlierWrites

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch
open Flapjack.Compiler.Encoders.Asm

def attached (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent internal oldLeft : BitVec 64) :=
  if parent = 0#64 then New.putField source table 56 internal
  else if oldLeft = node then putNode source (New.nodesPointer table cap) parent 8 internal
  else putNode source (New.nodesPointer table cap) parent 16 internal

/-- The actual final branch attaches the fresh internal node at the root
or at the original selected parent edge, using its real left-cell read. -/
theorem attach_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap node parent leaf internal pointer oldLeft : BitVec 64) (difference : Nat)
    (domain : source.memaddrs = InitE.ordinaryDomain) (geometry : New.Geometry table cap) (aligned : table.toNat%8 = 0)
    (parentInside : parent.toNat ≤ cap.toNat)
    (locals : SpliceLocals source table (New.nodesPointer table cap) node parent leaf internal pointer difference)
    (leftCell : parent ≠ 0#64 → source.memory (FindLeaf.cell (New.nodesPointer table cap) parent 8) = .word oldLeft) :
    evaluateHOLFiniteState source attach = (none,attached source table cap node parent internal oldLeft) := by
  have parentRead : eval source (.cmp .equal (localVar "p") (.const 0#64)) =
      some (.val (.word (if parent = 0#64 then 1#64 else 0#64))) := by
    simp [eval,evalHOLExact,localVar,locals.parentCell,wordCmpHOL]
  simp only [eval] at parentRead
  rw [splice_shapes.2.2.2.2.2.2.2.2.2,evaluateHOLFiniteState_ite,parentRead]
  by_cases zero : parent = 0#64
  · simp only [if_pos zero,if_neg (show (1#64 : BitVec 64) ≠ 0 from by decide),attached]
    exact New.store_field source table internal 56 (localVar "ni") domain geometry.table aligned (by decide) (by decide) locals.tableCell
      (Request.local_word source "ni" internal locals.internalCell)
  · simp only [if_neg zero,if_pos (show (0#64 : BitVec 64) = 0 from rfl)]
    have mapped := AllocatedBytes.word_mapped source (slot (New.nodesPointer table cap) parent 32) 32 8 domain (geometry.node_slot parent parentInside) (by decide)
      (slot_aligned _ parent cap 32 geometry.nodes parentInside geometry.nodesAligned (by decide)) (by decide)
    have leftRead := Witness.load_word_read source (nodeFor "p" 8) (FindLeaf.cell (New.nodesPointer table cap) parent 8) oldLeft
      (named_node_read source _ parent "p" 8 locals.nodesCell locals.parentCell) mapped (leftCell zero)
    have equalRead : eval source (.cmp .equal (.load .one (nodeFor "p" 8)) (localVar "n")) =
        some (.val (.word (if oldLeft = node then 1#64 else 0#64))) := by
      simp only [eval] at leftRead ⊢
      rw [evalHOLExact]
      simp only [leftRead]
      simp [evalHOLExact,localVar,locals.nodeCell,wordCmpHOL]
    simp only [eval] at equalRead
    rw [evaluateHOLFiniteState_ite,equalRead]
    by_cases same : oldLeft = node
    · simp only [if_pos same,if_neg (show (1#64 : BitVec 64) ≠ 0 from by decide),attached,if_neg zero]
      exact store_named_node source table cap parent internal "p" 8 (localVar "ni") domain geometry parentInside (by decide) (by decide)
        locals.nodesCell locals.parentCell (Request.local_word source "ni" internal locals.internalCell)
    · simp only [if_neg same,if_pos (show (0#64 : BitVec 64) = 0 from rfl),attached,if_neg zero]
      exact store_named_node source table cap parent internal "p" 16 (localVar "ni") domain geometry parentInside (by decide) (by decide)
        locals.nodesCell locals.parentCell (Request.local_word source "ni" internal locals.internalCell)

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.attach_execute
