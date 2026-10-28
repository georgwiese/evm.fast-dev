import InitECandidate.Solver.Input.CurrentTable.Get.Program
import InitECandidate.Solver.Input.CurrentTable.ImageFacts
import InitECandidate.Solver.Input.CurrentTable.CellGeometry

namespace InitECandidate.Solver.Input.CurrentTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

theorem leaf_value_read {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root leaf : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word leaf)))
    (member : valid leaf) (marked : bits leaf=256) :
    ∃ value,eval source valueRead=some (.val (.word value)) ∧ ValueOf value := by
  obtain ⟨value,stored,validValue⟩ := image.leafValues leaf member marked
  have nodesRead := FindLeaf.header_read source table (New.nodesPointer table cap) 40 image.domain image.geometry.table image.aligned
    (by decide) (by decide) tableCell image.nodesCell
  have addressRead : eval source (.op .add [.load .one (header 40),.panop .mul [localVar "leaf",.const 32#64],.const 8#64])=
      some (.val (.word (FindLeaf.cell (New.nodesPointer table cap) leaf 8))) := by
    change eval source (.load .one (header 40))=some (.val (.word (New.nodesPointer table cap))) at nodesRead
    simp only [eval] at nodesRead ⊢
    rw [evalHOLExact]
    simp only [evalListHOLExact]
    rw [nodesRead]
    simp [evalHOLExact,evalListHOLExact,toExact,localVar,leafCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,FindLeaf.cell,BitVec.add_assoc]
  have inside := image.node_inside leaf member
  have arena := image.geometry.node_slot leaf inside
  have aligned := slot_aligned (New.nodesPointer table cap) leaf cap 32 image.geometry.nodes inside image.geometry.nodesAligned (by decide)
  have mapped := AllocatedBytes.word_mapped source (slot (New.nodesPointer table cap) leaf 32) 32 8 image.domain arena (by decide) aligned (by decide)
  change source.memaddrs (FindLeaf.cell (New.nodesPointer table cap) leaf 8) at mapped
  exact ⟨value,Witness.load_word_read source _ _ value addressRead mapped stored,validValue⟩

end InitECandidate.Solver.Input.CurrentTable.Get

#print axioms InitECandidate.Solver.Input.CurrentTable.Get.leaf_value_read
