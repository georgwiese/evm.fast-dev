import InitECandidate.Solver.Input.CurrentTable.SlotGeometry
import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Model
import InitECandidate.Solver.Input.CurrentTable.NewStores

namespace InitECandidate.Solver.Input.CurrentTable
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch
open Flapjack.Compiler.Encoders.Asm

/-- The unchanged leaf/internal-node store address. -/
def nodeAddress (offset : Nat) : ExpHOL 64 :=
  .op .add [localVar "nodes",.panop .mul [localVar "n",.const 32#64],.const (BitVec.ofNat 64 offset)]

theorem node_address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base node : BitVec 64) (offset : Nat)
    (baseCell : source.locals.lookup (ofString "nodes") = some (.val (.word base)))
    (nodeCell : source.locals.lookup (ofString "n") = some (.val (.word node))) :
    eval source (nodeAddress offset) = some (.val (.word (FindLeaf.cell base node offset))) := by
  simp [eval,nodeAddress,evalHOLExact,evalListHOLExact,localVar,baseCell,nodeCell,
    valueIsWord,valueWord,panOpHOL,wordOpHOL,wordOp,FindLeaf.cell,BitVec.add_assoc]

def putNode (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base node : BitVec 64) (offset : Nat) (value : BitVec 64) :=
  {source with memory := StoreWord.put source.memory (FindLeaf.cell base node offset) value}

/-- Actual node stores need allocated slots, without initialized node contents. -/
theorem store_node (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base node cap value : BitVec 64)
    (offset : Nat) (expression : ExpHOL 64)
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (array : AllocatedBytes.Arena base (32*(cap.toNat+1))) (aligned : base.toNat%8 = 0)
    (inside : node.toNat ≤ cap.toNat) (small : offset < 32) (offsetAligned : offset%8 = 0)
    (baseCell : source.locals.lookup (ofString "nodes") = some (.val (.word base)))
    (nodeCell : source.locals.lookup (ofString "n") = some (.val (.word node)))
    (read : eval source expression = some (.val (.word value))) :
    evaluateHOLFiniteState source (.store (nodeAddress offset) expression) = (none,putNode source base node offset value) := by
  exact StoreWord.execute source _ _ _ _ (node_address_read source base node offset baseCell nodeCell) read
    (AllocatedBytes.word_mapped source (slot base node 32) 32 offset domain (slot_arena base node cap 32 array inside) small
      (slot_aligned base node cap 32 array inside aligned (by decide)) offsetAligned)

end InitECandidate.Solver.Input.CurrentTable

#print axioms InitECandidate.Solver.Input.CurrentTable.node_address_read
#print axioms InitECandidate.Solver.Input.CurrentTable.store_node
