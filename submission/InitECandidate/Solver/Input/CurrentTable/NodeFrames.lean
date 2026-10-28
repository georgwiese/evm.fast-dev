import InitECandidate.Solver.Input.CurrentTable.NodeStores
import InitECandidate.Solver.Input.CurrentTable.FieldFrames

namespace InitECandidate.Solver.Input.CurrentTable
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem node_header (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node value : BitVec 64) (offset field : Nat)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (small : offset < 32) (fieldSmall : field < 88) :
    (putNode source (New.nodesPointer table cap) node offset value).memory (table+BitVec.ofNat 64 field) =
      source.memory (table+BitVec.ofNat 64 field) := by
  have away := geometry.header_away node inside offset field small fieldSmall
  simp only [putNode,StoreWord.put,if_neg away]

theorem node_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node other value : BitVec 64) (offset field : Nat)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (otherInside : other.toNat ≤ cap.toNat)
    (small : offset < 32) (fieldSmall : field < 32) (different : other ≠ node ∨ field ≠ offset) :
    (putNode source (New.nodesPointer table cap) node offset value).memory (FindLeaf.cell (New.nodesPointer table cap) other field) =
      source.memory (FindLeaf.cell (New.nodesPointer table cap) other field) := by
  have away : FindLeaf.cell (New.nodesPointer table cap) other field ≠ FindLeaf.cell (New.nodesPointer table cap) node offset := by
    intro same
    have pair := cell_injective _ other node cap field offset geometry.nodes otherInside inside fieldSmall small same
    rcases different with nodeNe | fieldNe
    · exact nodeNe pair.1
    · exact fieldNe pair.2
  simp only [putNode,StoreWord.put,if_neg away]

theorem node_key (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node keyNode value : BitVec 64) (offset : Nat) (key : KeyBits.Key)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (keyInside : keyNode.toNat ≤ cap.toNat)
    (small : offset < 32) (view : FirstDiff.ByteView source (slot (New.keysPointer table) keyNode 32) key) :
    FirstDiff.ByteView (putNode source (New.nodesPointer table cap) node offset value) (slot (New.keysPointer table) keyNode 32) key := by
  apply StoreWord.byteView_away source (FindLeaf.cell (New.nodesPointer table cap) node offset) value _ key _ view
  intro byte same
  have before := geometry.key_byte_before_node keyNode node keyInside inside byte.val offset byte.isLt small
  change (panByteAlignHOL (width:=64) (slot (New.keysPointer table) keyNode 32+BitVec.ofNat 64 byte.val)).toNat < _ at before
  have equal := congrArg BitVec.toNat same
  omega

theorem node_before (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node value query : BitVec 64) (offset : Nat)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (small : offset < 32) (before : query.toNat < table.toNat) :
    (putNode source (New.nodesPointer table cap) node offset value).memory query = source.memory query := by
  have lower := geometry.cell_after_table node inside offset small
  have away : query ≠ FindLeaf.cell (New.nodesPointer table cap) node offset := by
    intro same
    have equal := congrArg BitVec.toNat same
    omega
  simp only [putNode,StoreWord.put,if_neg away]

end InitECandidate.Solver.Input.CurrentTable

#print axioms InitECandidate.Solver.Input.CurrentTable.node_header
#print axioms InitECandidate.Solver.Input.CurrentTable.node_other
#print axioms InitECandidate.Solver.Input.CurrentTable.node_key
#print axioms InitECandidate.Solver.Input.CurrentTable.node_before
