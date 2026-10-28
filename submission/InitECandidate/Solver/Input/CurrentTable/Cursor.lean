import InitECandidate.Solver.Input.LocalEffects
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.Input.CurrentTable
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Physical cursor shared by both actual Patricia traversals. Function-
specific guards and other locals remain in their own entry contracts. -/
structure Cursor (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (base node : BitVec 64) : Prop where
  frame : LocalEffects.erase source = LocalEffects.erase origin
  nodeCell : source.locals.lookup (ofString "n") = some (.val (.word node))
  baseCell : source.locals.lookup (ofString "nodes") = some (.val (.word base))

theorem Cursor.at_tick {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {base node : BitVec 64}
    (ready : Cursor origin source base node) : Cursor origin (decClockHOLFinite source) base node :=
  ⟨ready.frame,ready.nodeCell,ready.baseCell⟩

theorem Cursor.with_local {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {base node : BitVec 64}
    (ready : Cursor origin source base node) (name : String) (word : BitVec 64)
    (notNode : ofString name ≠ ofString "n") (notBase : ofString name ≠ ofString "nodes") :
    Cursor origin (bind source name word) base node :=
  ⟨ready.frame,(bind_lookup_other source name "n" word notNode).trans ready.nodeCell,
    (bind_lookup_other source name "nodes" word notBase).trans ready.baseCell⟩

theorem Cursor.with_node {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {base node : BitVec 64}
    (ready : Cursor origin source base node) (child : BitVec 64) : Cursor origin (bind source "n" child) base child :=
  ⟨ready.frame,bind_lookup_same _ _ _,(bind_lookup_other source "n" "nodes" child (by decide)).trans ready.baseCell⟩

end InitECandidate.Solver.Input.CurrentTable

#print axioms InitECandidate.Solver.Input.CurrentTable.Cursor.with_local
#print axioms InitECandidate.Solver.Input.CurrentTable.Cursor.with_node
