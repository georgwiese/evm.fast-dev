import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Program
import InitECandidate.Solver.Input.LoadWord
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Current Patricia nodes have an explicit leaf marker and increasing bit
positions along every internal edge. Establishing this model from actual
insertions is a separate required proof, not an assumed global contract. -/
structure Nodes (origin : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64) (marker : Nat:=256) : Prop where
  bitBound : ∀ node,valid node → bits node≤marker
  bitMapped : ∀ node,valid node → origin.memaddrs (cell base node 24)
  bitCell : ∀ node,valid node → origin.memory (cell base node 24)=.word (BitVec.ofNat 64 (bits node))
  leftMapped : ∀ node,valid node → bits node<marker → origin.memaddrs (cell base node 8)
  rightMapped : ∀ node,valid node → bits node<marker → origin.memaddrs (cell base node 16)
  leftCell : ∀ node,valid node → bits node<marker → origin.memory (cell base node 8)=.word (left node)
  rightCell : ∀ node,valid node → bits node<marker → origin.memory (cell base node 16)=.word (right node)
  leftOrdered : ∀ node,valid node → bits node<marker → left node=0#64 ∨ valid (left node) ∧ bits node<bits (left node)
  rightOrdered : ∀ node,valid node → bits node<marker → right node=0#64 ∨ valid (right node) ∧ bits node<bits (right node)

/-- The node image is independent of caller/callee locals and clock. -/
theorem Nodes.of_frame {origin target : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64} {marker : Nat}
    (image : Nodes origin base valid bits left right marker) (same : LocalEffects.erase target=LocalEffects.erase origin) :
    Nodes target base valid bits left right marker := by
  have memory:=LocalEffects.memory_of_erase origin target same
  have domain:=congrArg PanSemStateFiniteExact.memaddrs same
  change target.memaddrs=origin.memaddrs at domain
  exact ⟨image.bitBound,by intro node member; rw [domain]; exact image.bitMapped node member,
    by intro node member; rw [memory]; exact image.bitCell node member,
    by intro node member internal; rw [domain]; exact image.leftMapped node member internal,
    by intro node member internal; rw [domain]; exact image.rightMapped node member internal,
    by intro node member internal; rw [memory]; exact image.leftCell node member internal,
    by intro node member internal; rw [memory]; exact image.rightCell node member internal,image.leftOrdered,image.rightOrdered⟩

structure State (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (base node : BitVec 64) (marker : BitVec 64:=256#64) : Prop where
  frame : LocalEffects.erase source=LocalEffects.erase origin
  nodeCell : source.locals.lookup (ofString "n")=some (.val (.word node))
  baseCell : source.locals.lookup (ofString "nodes")=some (.val (.word base))
  bitsCell : source.locals.lookup (ofString "keybits")=some (.val (.word marker))

/-- Numeric node image for a terminating traversal. Child indices are in
range, but bit positions need not increase. Actual table writes must still
establish this image before it can be used for a program bound. -/
structure RangeNodes (origin : PanSemStateFiniteExact 64 Guest.HostMemory)
    (base marker : BitVec 64) (limit : Nat)
    (bits left right : BitVec 64 → BitVec 64) : Prop where
  bitMapped : ∀ node, node ≠ 0#64 → node.toNat < limit → origin.memaddrs (cell base node 24)
  bitCell : ∀ node, node ≠ 0#64 → node.toNat < limit → origin.memory (cell base node 24) = .word (bits node)
  leftMapped : ∀ node, node ≠ 0#64 → node.toNat < limit → bits node ≠ marker → origin.memaddrs (cell base node 8)
  rightMapped : ∀ node, node ≠ 0#64 → node.toNat < limit → bits node ≠ marker → origin.memaddrs (cell base node 16)
  leftCell : ∀ node, node ≠ 0#64 → node.toNat < limit → bits node ≠ marker → origin.memory (cell base node 8) = .word (left node)
  rightCell : ∀ node, node ≠ 0#64 → node.toNat < limit → bits node ≠ marker → origin.memory (cell base node 16) = .word (right node)
  leftRange : ∀ node, node ≠ 0#64 → node.toNat < limit → bits node ≠ marker → (left node).toNat < limit
  rightRange : ∀ node, node ≠ 0#64 → node.toNat < limit → bits node ≠ marker → (right node).toNat < limit

theorem RangeNodes.of_cells {origin target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base marker : BitVec 64} {limit : Nat} {bits left right : BitVec 64 → BitVec 64}
    (image : RangeNodes origin base marker limit bits left right)
    (domain : target.memaddrs = origin.memaddrs)
    (memory : ∀ node, node ≠ 0#64 → node.toNat < limit → ∀ offset,
      (offset = 24 ∨ bits node ≠ marker ∧ (offset = 8 ∨ offset = 16)) →
      target.memory (cell base node offset) = origin.memory (cell base node offset)) :
    RangeNodes target base marker limit bits left right := by
  exact ⟨by intro node nonzero inside; rw [domain]; exact image.bitMapped node nonzero inside,
    by intro node nonzero inside
       exact (memory node nonzero inside 24 (Or.inl rfl)).trans (image.bitCell node nonzero inside),
    by intro node nonzero inside internal; rw [domain]; exact image.leftMapped node nonzero inside internal,
    by intro node nonzero inside internal; rw [domain]; exact image.rightMapped node nonzero inside internal,
    by intro node nonzero inside internal
       exact (memory node nonzero inside 8 (Or.inr ⟨internal, Or.inl rfl⟩)).trans (image.leftCell node nonzero inside internal),
    by intro node nonzero inside internal
       exact (memory node nonzero inside 16 (Or.inr ⟨internal, Or.inr rfl⟩)).trans (image.rightCell node nonzero inside internal),
    image.leftRange, image.rightRange⟩

theorem RangeNodes.of_frame {origin target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base marker : BitVec 64} {limit : Nat} {bits left right : BitVec 64 → BitVec 64}
    (image : RangeNodes origin base marker limit bits left right)
    (same : LocalEffects.erase target = LocalEffects.erase origin) :
    RangeNodes target base marker limit bits left right := by
  have domain := congrArg PanSemStateFiniteExact.memaddrs same
  change target.memaddrs = origin.memaddrs at domain
  exact image.of_cells domain
    (by intro node nonzero inside offset needed
        exact congrFun (LocalEffects.memory_of_erase origin target same) _)

/-- The original key-bit test evaluated in a fixed memory image. Only its
key and bit locals matter; a failed byte read is retained as a failed test. -/
noncomputable def keyProbe (origin : PanSemStateFiniteExact 64 Guest.HostMemory)
    (key bit : BitVec 64) : Option (ValueHOL 64) :=
  eval (bind (bind origin "key" key) "b" bit) keyTest

set_option maxRecDepth 100000 in
theorem key_test_probe {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {key bit : BitVec 64} (same : LocalEffects.erase source = LocalEffects.erase origin)
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word key)))
    (bitCell : source.locals.lookup (ofString "b") = some (.val (.word bit))) :
    eval source keyTest = keyProbe origin key bit := by
  have reset := congrArg (fun current : PanSemStateFiniteExact 64 Guest.HostMemory =>
    eval {current with locals := source.locals, clock := source.clock} keyTest) same
  change eval source keyTest = eval {origin with locals := source.locals, clock := source.clock} keyTest at reset
  rw [reset]
  have probeKey : (bind (bind origin "key" key) "b" bit).locals.lookup (ofString "key") = some (.val (.word key)) :=
    (bind_lookup_other _ "b" "key" bit (by decide)).trans (bind_lookup_same origin "key" key)
  have probeBit : (bind (bind origin "key" key) "b" bit).locals.lookup (ofString "b") = some (.val (.word bit)) :=
    bind_lookup_same _ "b" bit
  simp only [keyProbe, keyTest, branch, afterBit, step, loop, afterRoot, afterNodes,
    afterBits, body, Guest.Software.guestFn_htab_find_leaf, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil]
  simp only [eval, evalHOLExact, evalListHOLExact, keyCell, bitCell, probeKey, probeBit]
  rfl

theorem State.at_tick {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {base node : BitVec 64} {marker : BitVec 64}
    (ready : State origin source base node marker) : State origin (decClockHOLFinite source) base node marker :=
  ⟨ready.frame,ready.nodeCell,ready.baseCell,ready.bitsCell⟩

theorem address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base node : BitVec 64) (offset : Nat)
    (baseCell : source.locals.lookup (ofString "nodes")=some (.val (.word base)))
    (nodeCell : source.locals.lookup (ofString "n")=some (.val (.word node))) :
    eval source (address offset)=some (.val (.word (cell base node offset))) := by
  simp [address,cell,eval,evalHOLExact,evalListHOLExact,toExact,localVar,baseCell,nodeCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.add_assoc]

theorem bit_read {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {base node : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64} {marker : BitVec 64}
    (image : Nodes origin base valid bits left right marker.toNat) (ready : State origin source base node marker) (member : valid node) :
    eval source (.load .one (address 24))=some (.val (.word (BitVec.ofNat 64 (bits node)))) := by
  have domain:=congrArg PanSemStateFiniteExact.memaddrs ready.frame
  change source.memaddrs=origin.memaddrs at domain
  have memory:=LocalEffects.memory_of_erase origin source ready.frame
  exact Witness.load_word_read source (address 24) (cell base node 24) (BitVec.ofNat 64 (bits node))
    (address_read source base node 24 ready.baseCell ready.nodeCell) (by rw [domain]; exact image.bitMapped node member)
    (by rw [memory]; exact image.bitCell node member)

theorem State.word_read {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base node marker word : BitVec 64} (ready : State origin source base node marker)
    (offset : Nat) (mapped : origin.memaddrs (cell base node offset))
    (stored : origin.memory (cell base node offset) = .word word) :
    eval source (.load .one (address offset)) = some (.val (.word word)) := by
  have domain := congrArg PanSemStateFiniteExact.memaddrs ready.frame
  change source.memaddrs = origin.memaddrs at domain
  have memory := LocalEffects.memory_of_erase origin source ready.frame
  exact Witness.load_word_read source _ _ word
    (address_read source base node offset ready.baseCell ready.nodeCell)
    (by rw [domain]; exact mapped) (by rw [memory]; exact stored)

end InitECandidate.Solver.Input.CurrentTable.FindLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.address_read
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.bit_read

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.Nodes.of_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.RangeNodes.of_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.key_test_probe
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.State.word_read
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.RangeNodes.of_cells
