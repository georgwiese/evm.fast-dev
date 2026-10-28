import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Model
import InitECandidate.Solver.Input.ConditionalNone
import InitECandidate.Solver.Input.LocalPrefix
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem State.with_bit {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {base node : BitVec 64}
    (ready : State origin source base node) (word : BitVec 64) : State origin (bind source "b" word) base node :=
  ⟨ready.frame,(bind_lookup_other source "b" "n" word (by decide)).trans ready.nodeCell,
    (bind_lookup_other source "b" "nodes" word (by decide)).trans ready.baseCell,
    (bind_lookup_other source "b" "keybits" word (by decide)).trans ready.bitsCell⟩

theorem State.with_node {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {base node : BitVec 64}
    (ready : State origin source base node) (child : BitVec 64) : State origin (bind source "n" child) base child :=
  ⟨ready.frame,bind_lookup_same _ _ _,(bind_lookup_other source "n" "nodes" child (by decide)).trans ready.baseCell,
    (bind_lookup_other source "n" "keybits" child (by decide)).trans ready.bitsCell⟩

theorem branch_safe : LocalPrefix (ofString "nodes") branch := by
  rw [shapes.2.2.2]
  exact .ite _ (.assign _ _ (by decide)) (.assign _ _ (by decide))

/-- Whichever actual key bit the real read selects, a normal internal step
loads that node's real child. Failed key reads need no future child state. -/
theorem branch_normal {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {base node : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (image : Nodes origin base valid bits left right) (ready : State origin source base node) (member : valid node) (internal : bits node<256)
    (normal : evaluateHOLFiniteState source branch=(none,post)) :
    ∃ child,post=bind source "n" child ∧ (child=0#64 ∨ valid child ∧ bits node<bits child) := by
  have domain:=congrArg PanSemStateFiniteExact.memaddrs ready.frame
  change source.memaddrs=origin.memaddrs at domain
  have memory:=LocalEffects.memory_of_erase origin source ready.frame
  have leftRead : eval source (.load .one (address 8))=some (.val (.word (left node))) :=
    Witness.load_word_read source (address 8) (cell base node 8) (left node)
      (address_read source base node 8 ready.baseCell ready.nodeCell) (by rw [domain]; exact image.leftMapped node member internal)
      (by rw [memory]; exact image.leftCell node member internal)
  have rightRead : eval source (.load .one (address 16))=some (.val (.word (right node))) :=
    Witness.load_word_read source (address 16) (cell base node 16) (right node)
      (address_read source base node 16 ready.baseCell ready.nodeCell) (by rw [domain]; exact image.rightMapped node member internal)
      (by rw [memory]; exact image.rightCell node member internal)
  have leftRun:=StateSteps.assign_execute source "n" (.load .one (address 8)) node (left node) ready.nodeCell leftRead
  have rightRun:=StateSteps.assign_execute source "n" (.load .one (address 16)) node (right node) ready.nodeCell rightRead
  rw [shapes.2.2.2] at normal
  rcases conditional_none source post _ _ _ normal with chosen|chosen
  · rw [leftRun] at chosen
    exact ⟨left node,(congrArg Prod.snd chosen).symm,image.leftOrdered node member internal⟩
  · rw [rightRun] at chosen
    exact ⟨right node,(congrArg Prod.snd chosen).symm,image.rightOrdered node member internal⟩

end InitECandidate.Solver.Input.CurrentTable.FindLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.State.with_bit
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.State.with_node
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.branch_normal
