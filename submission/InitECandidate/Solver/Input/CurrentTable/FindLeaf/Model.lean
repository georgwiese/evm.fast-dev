import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Program
import InitECandidate.Solver.Input.LoadWord

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Current Patricia nodes have a leaf marker256 and increasing bit
positions along every internal edge. Establishing this model from actual
insertions is a separate required proof, not an assumed global contract. -/
structure Nodes (origin : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64) : Prop where
  bitBound : ∀ node,valid node → bits node≤256
  bitMapped : ∀ node,valid node → origin.memaddrs (cell base node 24)
  bitCell : ∀ node,valid node → origin.memory (cell base node 24)=.word (BitVec.ofNat 64 (bits node))
  leftMapped : ∀ node,valid node → bits node<256 → origin.memaddrs (cell base node 8)
  rightMapped : ∀ node,valid node → bits node<256 → origin.memaddrs (cell base node 16)
  leftCell : ∀ node,valid node → bits node<256 → origin.memory (cell base node 8)=.word (left node)
  rightCell : ∀ node,valid node → bits node<256 → origin.memory (cell base node 16)=.word (right node)
  leftOrdered : ∀ node,valid node → bits node<256 → left node=0#64 ∨ valid (left node) ∧ bits node<bits (left node)
  rightOrdered : ∀ node,valid node → bits node<256 → right node=0#64 ∨ valid (right node) ∧ bits node<bits (right node)

/-- The node image is independent of caller/callee locals and clock. -/
theorem Nodes.of_frame {origin target : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (image : Nodes origin base valid bits left right) (same : LocalEffects.erase target=LocalEffects.erase origin) :
    Nodes target base valid bits left right := by
  have memory:=LocalEffects.memory_of_erase origin target same
  have domain:=congrArg PanSemStateFiniteExact.memaddrs same
  change target.memaddrs=origin.memaddrs at domain
  exact ⟨image.bitBound,by intro node member; rw [domain]; exact image.bitMapped node member,
    by intro node member; rw [memory]; exact image.bitCell node member,
    by intro node member internal; rw [domain]; exact image.leftMapped node member internal,
    by intro node member internal; rw [domain]; exact image.rightMapped node member internal,
    by intro node member internal; rw [memory]; exact image.leftCell node member internal,
    by intro node member internal; rw [memory]; exact image.rightCell node member internal,image.leftOrdered,image.rightOrdered⟩

structure State (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (base node : BitVec 64) : Prop where
  frame : LocalEffects.erase source=LocalEffects.erase origin
  nodeCell : source.locals.lookup (ofString "n")=some (.val (.word node))
  baseCell : source.locals.lookup (ofString "nodes")=some (.val (.word base))
  bitsCell : source.locals.lookup (ofString "keybits")=some (.val (.word 256#64))

theorem State.at_tick {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {base node : BitVec 64}
    (ready : State origin source base node) : State origin (decClockHOLFinite source) base node :=
  ⟨ready.frame,ready.nodeCell,ready.baseCell,ready.bitsCell⟩

theorem address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base node : BitVec 64) (offset : Nat)
    (baseCell : source.locals.lookup (ofString "nodes")=some (.val (.word base)))
    (nodeCell : source.locals.lookup (ofString "n")=some (.val (.word node))) :
    eval source (address offset)=some (.val (.word (cell base node offset))) := by
  simp [address,cell,eval,evalHOLExact,evalListHOLExact,toExact,localVar,baseCell,nodeCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.add_assoc]

theorem bit_read {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {base node : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (image : Nodes origin base valid bits left right) (ready : State origin source base node) (member : valid node) :
    eval source (.load .one (address 24))=some (.val (.word (BitVec.ofNat 64 (bits node)))) := by
  have domain:=congrArg PanSemStateFiniteExact.memaddrs ready.frame
  change source.memaddrs=origin.memaddrs at domain
  have memory:=LocalEffects.memory_of_erase origin source ready.frame
  exact Witness.load_word_read source (address 24) (cell base node 24) (BitVec.ofNat 64 (bits node))
    (address_read source base node 24 ready.baseCell ready.nodeCell) (by rw [domain]; exact image.bitMapped node member)
    (by rw [memory]; exact image.bitCell node member)

end InitECandidate.Solver.Input.CurrentTable.FindLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.address_read
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.bit_read

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.Nodes.of_frame
