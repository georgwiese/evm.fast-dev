import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Model
import InitECandidate.Solver.Input.CurrentTable.Cursor
import InitECandidate.Solver.Input.ConditionalNone
import InitECandidate.Solver.Input.LocalPrefix
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem State.with_bit {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {base node : BitVec 64} {marker : BitVec 64}
    (ready : State origin source base node marker) (word : BitVec 64) : State origin (bind source "b" word) base node marker :=
  ⟨ready.frame,(bind_lookup_other source "b" "n" word (by decide)).trans ready.nodeCell,
    (bind_lookup_other source "b" "nodes" word (by decide)).trans ready.baseCell,
    (bind_lookup_other source "b" "keybits" word (by decide)).trans ready.bitsCell⟩

theorem State.with_node {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {base node : BitVec 64} {marker : BitVec 64}
    (ready : State origin source base node marker) (child : BitVec 64) : State origin (bind source "n" child) base child marker :=
  ⟨ready.frame,bind_lookup_same _ _ _,(bind_lookup_other source "n" "nodes" child (by decide)).trans ready.baseCell,
    (bind_lookup_other source "n" "keybits" child (by decide)).trans ready.bitsCell⟩

theorem branch_safe : LocalPrefix (ofString "nodes") branch := by
  rw [shapes.2.2.2]
  exact .ite _ (.assign _ _ (by decide)) (.assign _ _ (by decide))

/-- Whichever actual key bit the real read selects, a normal internal step
loads that node's real child. Failed key reads need no future child state. -/
theorem branch_normal {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {base node : BitVec 64} {marker : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (image : Nodes origin base valid bits left right marker.toNat) (ready : State origin source base node marker) (member : valid node) (internal : bits node<marker.toNat)
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

namespace InitECandidate.Solver.Input.CurrentTable
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

theorem Cursor.word_read {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base node word : BitVec 64} (ready : Cursor origin source base node)
    (offset : Nat) (mapped : origin.memaddrs (FindLeaf.cell base node offset))
    (stored : origin.memory (FindLeaf.cell base node offset)=.word word) :
    eval source (.load .one (FindLeaf.address offset))=some (.val (.word word)) := by
  have domain:=congrArg PanSemStateFiniteExact.memaddrs ready.frame
  change source.memaddrs=origin.memaddrs at domain
  have memory:=LocalEffects.memory_of_erase origin source ready.frame
  exact Witness.load_word_read source _ _ word
    (FindLeaf.address_read source base node offset ready.baseCell ready.nodeCell)
    (by rw [domain]; exact mapped) (by rw [memory]; exact stored)

end InitECandidate.Solver.Input.CurrentTable

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The common original key-bit branch uses its actual query in fixed
memory. Failed key tests remain errors; no increasing-bit property is used. -/
theorem range_branch_execute {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base node marker key : BitVec 64} {limit : Nat} {bits left right : BitVec 64 → BitVec 64}
    (image : RangeNodes origin base marker limit bits left right) (ready : Cursor origin source base node)
    (nonzero : node≠0#64) (inside : node.toNat<limit) (internal : bits node≠marker)
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (bitCell : source.locals.lookup (ofString "b")=some (.val (.word (bits node)))) :
    evaluateHOLFiniteState source branch=
      match keyProbe origin key (bits node) with
      | some (.val (.word choice)) => (none,bind source "n" (if choice=0#64 then right node else left node))
      | _ => (some .error,source) := by
  have probe:=key_test_probe ready.frame keyCell bitCell
  have leftRead:=ready.word_read 8 (image.leftMapped node nonzero inside internal) (image.leftCell node nonzero inside internal)
  have rightRead:=ready.word_read 16 (image.rightMapped node nonzero inside internal) (image.rightCell node nonzero inside internal)
  have leftRun:=StateSteps.assign_execute source "n" (.load .one (address 8)) node (left node) ready.nodeCell leftRead
  have rightRun:=StateSteps.assign_execute source "n" (.load .one (address 16)) node (right node) ready.nodeCell rightRead
  rw [shapes.2.2.2,evaluateHOLFiniteState_ite]
  unfold eval at probe
  rw [probe]
  generalize observed : keyProbe origin key (bits node)=value
  cases value with
  | none=>rfl
  | some value=>
    cases value with
    | rStruct fields=>rfl
    | nStruct name fields=>rfl
    | val payload=>
      cases payload with
      | word choice=>
        by_cases zero : choice=0#64
        · simpa only [show (0 : BitVec 64)=0#64 from rfl,if_pos zero] using rightRun
        · simpa only [show (0 : BitVec 64)=0#64 from rfl,if_neg zero] using leftRun

end InitECandidate.Solver.Input.CurrentTable.FindLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.Cursor.word_read
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.range_branch_execute
