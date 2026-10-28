import InitECandidate.Solver.Input.CurrentTable.Set.SeekControl
import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Entry

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

def nodesEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) := bind source "nodes" base
def parentEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) := bind (nodesEntry source base) "p" 0#64
def rootEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base root : BitVec 64) := bind (parentEntry source base) "n" root

def restoreSeek (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (post : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restore source "nodes" (restore (nodesEntry source base) "p" (restore (parentEntry source base) "n" post))

set_option maxRecDepth 100000 in
theorem setup_shapes :
    afterDifference = .dec (ofString "nodes") .one (.load .one (FindLeaf.tableAddress 40)) afterNodes ∧
    afterNodes = .dec (ofString "p") .one (.const 0#64) afterParent ∧
    afterParent = .dec (ofString "n") .one (.load .one (FindLeaf.tableAddress 56)) afterNode := by
  simp only [afterDifference,differenceCall,afterCompare,compareCall,afterKeys,afterLeaf,afterStride,afterLength,body,
    afterNodes,afterParent,afterNode,FindLeaf.tableAddress,Scalar.plus,localVar,
    Guest.Software.guestFn_htab_set,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  trivial

/-- Actual current table-header reads and lexical declarations reach this
same insertion search; every outer restoration is retained. -/
theorem setup_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table base root : BitVec 64)
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : AllocatedBytes.Arena table 88) (aligned : table.toNat%8 = 0)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (nodesCell : source.memory (table+40#64) = .word base) (rootCell : source.memory (table+56#64) = .word root) :
    evaluateHOLFiniteState source afterDifference =
      let output := evaluateHOLFiniteState (rootEntry source base root) afterNode
      (output.1,restoreSeek source base output.2) := by
  have nodesRead := FindLeaf.header_read source table base 40 domain arena aligned (by decide) (by decide) tableCell nodesCell
  have firstTable := (bind_lookup_other source "nodes" "t" base (by decide)).trans tableCell
  have secondTable := (bind_lookup_other (nodesEntry source base) "p" "t" 0#64 (by decide)).trans firstTable
  have rootRead := FindLeaf.header_read (parentEntry source base) table root 56 domain arena aligned (by decide) (by decide) secondTable rootCell
  let output := evaluateHOLFiniteState (rootEntry source base root) afterNode
  have last : evaluateHOLFiniteState (parentEntry source base) afterParent =
      (output.1,restore (parentEntry source base) "n" output.2) := by
    rw [setup_shapes.2.2]
    exact ScalarScope.declare_execute _ _ "n" _ root afterNode output.1 rootRead rfl
  have middle : evaluateHOLFiniteState (nodesEntry source base) afterNodes =
      (output.1,restore (nodesEntry source base) "p" (restore (parentEntry source base) "n" output.2)) := by
    rw [setup_shapes.2.1]
    exact ScalarScope.declare_execute _ _ "p" (.const 0#64) 0#64 afterParent output.1 rfl last
  rw [setup_shapes.1]
  exact ScalarScope.declare_execute source _ "nodes" _ base afterNodes output.1 nodesRead middle

/-- The same real declaration bindings initialize p=0,n=root and retain
the d/query locals from the actual preceding first-difference caller. -/
theorem initial_state (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base root pointer : BitVec 64) (difference : Nat)
    (differenceCell : source.locals.lookup (ofString "d") = some (.val (.word (BitVec.ofNat 64 difference))))
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word pointer))) :
    SeekState source (rootEntry source base root) base root 0#64 pointer difference := by
  have other (key : String) (notNodes : ofString "nodes" ≠ ofString key) (notParent : ofString "p" ≠ ofString key) (notNode : ofString "n" ≠ ofString key) :
      (rootEntry source base root).locals.lookup (ofString key) = source.locals.lookup (ofString key) :=
    (bind_lookup_other (parentEntry source base) "n" key root notNode).trans
      ((bind_lookup_other (nodesEntry source base) "p" key 0#64 notParent).trans (bind_lookup_other source "nodes" key base notNodes))
  have baseCell : (rootEntry source base root).locals.lookup (ofString "nodes") = some (.val (.word base)) :=
    (bind_lookup_other (parentEntry source base) "n" "nodes" root (by decide)).trans
      ((bind_lookup_other (nodesEntry source base) "p" "nodes" 0#64 (by decide)).trans (bind_lookup_same _ _ _))
  have parentCell : (rootEntry source base root).locals.lookup (ofString "p") = some (.val (.word 0#64)) :=
    (bind_lookup_other (parentEntry source base) "n" "p" root (by decide)).trans (bind_lookup_same _ _ _)
  exact ⟨⟨rfl,bind_lookup_same _ _ _,baseCell⟩,parentCell,
    (other _ (by decide) (by decide) (by decide)).trans differenceCell,
    (other _ (by decide) (by decide) (by decide)).trans keyCell⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.setup_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.initial_state
