import InitECandidate.Solver.WitnessRadix.ConstructorHashFrame

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact BackingLayout
open Flapjack.Basis.Pure.MlString QueryBranch

theorem hash_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (layout : Layout) (mapped : Mapped source layout)
    (sliceFor : BitVec 64 → Graph.Slice) (fixedData : FixedData source layout sliceFor) (index : Nat) (inside : index<layout.count)
    (locals : Locals source layout.keys layout.vals layout.primary layout.records (BitVec.ofNat 64 index)) (hashScratch : BitVec 64)
    (global : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hashScratch))) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) hashArguments=
      some (Keccak256.values (sliceFor (BitVec.ofNat 64 index)).1 hashScratch (sliceFor (BitVec.ofNat 64 index)).2.toNat) := by
  classical
  have firstCell : layout.records+BitVec.ofNat 64 index*16#64=cell layout .records (16*index) := by
    rw [record_cell]
    rfl
  have secondCell : layout.records+BitVec.ofNat 64 index*16#64+8#64=cell layout .records (16*index+8) := by
    rw [firstCell]
    simp [cell,base,byteAddress,BitVec.ofNat_add,BitVec.add_assoc]
  have pointerMapped : source.memaddrs (layout.records+BitVec.ofNat 64 index*16#64) := by
    rw [firstCell]
    exact mapped .records (16*index) (by omega) (by change 16*index+8≤16*layout.count; omega)
  have lengthMapped : source.memaddrs (layout.records+BitVec.ofNat 64 index*16#64+8#64) := by
    rw [secondCell]
    exact mapped .records (16*index+8) (by omega) (by change 16*index+8+8≤16*layout.count; omega)
  have pointerWord : source.memory (layout.records+BitVec.ofNat 64 index*16#64)=.word (sliceFor (BitVec.ofNat 64 index)).1 := by
    rw [firstCell]; exact fixedData.pointers index inside
  have lengthWord : source.memory (layout.records+BitVec.ofNat 64 index*16#64+8#64)=.word (sliceFor (BitVec.ofNat 64 index)).2 := by
    rw [secondCell]; exact fixedData.lengths index inside
  have pointerRead : eval source (.load .one (scaled "slice_arr" 16#64))=some (.val (.word (sliceFor (BitVec.ofNat 64 index)).1)) := by
    simp [eval,scaled,localVar,evalHOLExact,evalListHOLExact,toExact,locals.recordsLocal,locals.indexLocal,
      valueIsWord,valueWord,panOpHOL,wordOpHOL,wordOp,memLoadHOLExact,pointerMapped,pointerWord]
  have lengthRead : eval source (.load .one (.op .add [localVar "slice_arr",.panop .mul [localVar "i",.const 16#64],.const 8#64]))=
      some (.val (.word (sliceFor (BitVec.ofNat 64 index)).2)) := by
    simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,locals.recordsLocal,locals.indexLocal,
      valueIsWord,valueWord,panOpHOL,wordOpHOL,wordOp,memLoadHOLExact,BitVec.add_assoc] at lengthMapped lengthWord ⊢
    simp [lengthMapped,lengthWord]
  have scratchRead : eval source scratch=some (.val (.word hashScratch)) := global
  simp only [eval] at pointerRead lengthRead scratchRead
  simp [hashArguments,evalListHOLFinite,evalListHOLExact,pointerRead,lengthRead,scratchRead,Keccak256.values]

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.hash_arguments
