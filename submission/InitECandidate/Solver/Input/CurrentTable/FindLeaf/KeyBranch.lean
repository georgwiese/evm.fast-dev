import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Step
import InitECandidate.Solver.Input.CurrentTable.KeyRead

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- With real physical query bytes, the actual internal branch chooses its
zero/one child according to the current most-significant-first key bit. -/
theorem branch_execute {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {base node : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (image : Nodes origin base valid bits left right) (ready : State origin source base node)
    (member : valid node) (internal : bits node < 256) (pointer : BitVec 64) (query : KeyBits.Key)
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word pointer)))
    (bitCell : source.locals.lookup (ofString "b") = some (.val (.word (BitVec.ofNat 64 (bits node)))))
    (view : FirstDiff.ByteView source pointer query) :
    evaluateHOLFiniteState source branch =
      (none,bind source "n" (if KeyBits.bit query (bits node) then right node else left node)) := by
  have domain := congrArg PanSemStateFiniteExact.memaddrs ready.frame
  change source.memaddrs = origin.memaddrs at domain
  have memory := LocalEffects.memory_of_erase origin source ready.frame
  have leftRead : eval source (.load .one (address 8)) = some (.val (.word (left node))) :=
    Witness.load_word_read source (address 8) (cell base node 8) (left node)
      (address_read source base node 8 ready.baseCell ready.nodeCell)
      (by rw [domain]; exact image.leftMapped node member internal)
      (by rw [memory]; exact image.leftCell node member internal)
  have rightRead : eval source (.load .one (address 16)) = some (.val (.word (right node))) :=
    Witness.load_word_read source (address 16) (cell base node 16) (right node)
      (address_read source base node 16 ready.baseCell ready.nodeCell)
      (by rw [domain]; exact image.rightMapped node member internal)
      (by rw [memory]; exact image.rightCell node member internal)
  have leftRun := StateSteps.assign_execute source "n" (.load .one (address 8)) node (left node) ready.nodeCell leftRead
  have rightRun := StateSteps.assign_execute source "n" (.load .one (address 16)) node (right node) ready.nodeCell rightRead
  have testRead := KeyRead.find_test_read source pointer query (bits node) internal keyCell bitCell view
  simp only [eval] at testRead
  rw [shapes.2.2.2,evaluateHOLFiniteState_ite,testRead]
  cases digit : KeyBits.bit query (bits node)
  · simpa [digit] using leftRun
  · simpa [digit] using rightRun

/-- One real continuing traversal step uses that same query-directed child,
including exact restoration of its temporary b binding. -/
theorem step_execute {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {base node : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (image : Nodes origin base valid bits left right) (ready : State origin source base node)
    (member : valid node) (internal : bits node < 256) (pointer : BitVec 64) (query : KeyBits.Key)
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word pointer)))
    (view : FirstDiff.ByteView source pointer query) :
    evaluateHOLFiniteState source step =
      (none,bind source "n" (if KeyBits.bit query (bits node) then right node else left node)) := by
  let entered := bind source "b" (BitVec.ofNat 64 (bits node))
  let child := if KeyBits.bit query (bits node) then right node else left node
  have state := ready.with_bit (BitVec.ofNat 64 (bits node))
  have afterRun := after_bit_execute entered (bits node) (image.bitBound node member) (bind_lookup_same _ _ _) state.bitsCell
  rw [if_neg (show bits node ≠ 256 from by omega)] at afterRun
  have branchRun := branch_execute image state member internal pointer query
    ((bind_lookup_other source "b" "key" _ (by decide)).trans keyCell) (bind_lookup_same _ _ _) (view.of_frame rfl)
  have run : evaluateHOLFiniteState entered afterBit = (none,bind entered "n" child) := afterRun.trans branchRun
  have actual := ScalarScope.declare_execute source (bind entered "n" child) "b" (.load .one (address 24))
    (BitVec.ofNat 64 (bits node)) afterBit none (bit_read image ready member) run
  rw [shapes.2.1,actual,restore_bind_other source entered "b" "n" child (by decide),restore_bound]

end InitECandidate.Solver.Input.CurrentTable.FindLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.branch_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.step_execute
