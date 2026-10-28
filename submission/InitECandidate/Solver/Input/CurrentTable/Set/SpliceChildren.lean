import InitECandidate.Solver.Input.CurrentTable.Set.SpliceLocals
import InitECandidate.Solver.Input.CurrentTable.EarlierWrites

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch
open Flapjack.Compiler.Encoders.Asm

def childrenStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base node leaf internal : BitVec 64) (query : KeyBits.Key) (difference : Nat) :=
  putNode (putNode source base internal 8 (if KeyBits.bit query difference then node else leaf))
    base internal 16 (if KeyBits.bit query difference then leaf else node)

theorem split_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (query : KeyBits.Key) (difference : Nat)
    (inside : difference < 256) (keyCell : source.locals.lookup (ofString "key") = some (.val (.word pointer)))
    (differenceCell : source.locals.lookup (ofString "d") = some (.val (.word (BitVec.ofNat 64 difference))))
    (view : FirstDiff.ByteView source pointer query) :
    eval source (.cmp .equal (KeyRead.mask "key" "d") (.const 0#64)) =
      some (.val (.word (if KeyBits.bit query difference then 0#64 else 1#64))) := by
  have maskRead := KeyRead.mask_read source "key" "d" pointer query difference inside keyCell differenceCell view
  simp only [eval] at maskRead ⊢
  rw [evalHOLExact]
  simp only [maskRead]
  cases digit : KeyBits.bit query difference <;> simp [evalHOLExact,wordCmpHOL,digit]

/-- The actual post-constructor bit test writes the fresh leaf and stopped
subtree into the real internal node's two child cells, in the right order. -/
theorem split_children_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap node parent leaf internal pointer : BitVec 64) (difference : Nat) (query : KeyBits.Key)
    (domain : source.memaddrs = InitE.ordinaryDomain) (geometry : New.Geometry table cap) (inside : internal.toNat ≤ cap.toNat)
    (locals : SpliceLocals source table (New.nodesPointer table cap) node parent leaf internal pointer difference)
    (differenceInside : difference < 256) (view : FirstDiff.ByteView source pointer query) :
    evaluateHOLFiniteState source splitChildren = (none,childrenStored source (New.nodesPointer table cap) node leaf internal query difference) := by
  have test := split_test_read source pointer query difference differenceInside locals.keyCell locals.differenceCell view
  simp only [eval] at test
  rw [splice_shapes.2.2.2.2.2.2.2.1,evaluateHOLFiniteState_ite,test]
  cases digit : KeyBits.bit query difference
  · let one := putNode source (New.nodesPointer table cap) internal 8 leaf
    have first := store_named_node source table cap internal leaf "ni" 8 (localVar "nl") domain geometry inside (by decide) (by decide)
      locals.nodesCell locals.internalCell (Request.local_word source "nl" leaf locals.leafCell)
    have second := store_named_node one table cap internal node "ni" 16 (localVar "n") domain geometry inside (by decide) (by decide)
      locals.nodesCell locals.internalCell (Request.local_word one "n" node locals.nodeCell)
    simp only [childrenStored,digit,Bool.false_eq_true,if_false,if_neg (show (1#64 : BitVec 64) ≠ 0 from by decide)]
    rw [leftFresh,evaluateHOLFiniteState_seq_line780,first]
    exact second
  · let one := putNode source (New.nodesPointer table cap) internal 8 node
    have first := store_named_node source table cap internal node "ni" 8 (localVar "n") domain geometry inside (by decide) (by decide)
      locals.nodesCell locals.internalCell (Request.local_word source "n" node locals.nodeCell)
    have second := store_named_node one table cap internal leaf "ni" 16 (localVar "nl") domain geometry inside (by decide) (by decide)
      locals.nodesCell locals.internalCell (Request.local_word one "nl" leaf locals.leafCell)
    simp only [childrenStored,digit,if_true,if_pos (show (0#64 : BitVec 64) = 0 from rfl)]
    rw [rightFresh,evaluateHOLFiniteState_seq_line780,first]
    exact second

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.split_test_read
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.split_children_execute
