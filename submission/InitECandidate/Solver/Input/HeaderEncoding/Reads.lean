import InitECandidate.Solver.Input.HeaderEncoding.Context

namespace InitECandidate.Solver.Input.HeaderEncoding
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem Context.load_one (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64)
    (context : Context source original header buffer) (offset : Nat) (inside : offset≤240) (aligned : offset%8=0) :
    eval source (loadOne offset)=some (.val (.word (wordAt original (address header offset)))) := by
  classical
  obtain ⟨mapped,stored⟩:=context.cell source original header buffer offset inside aligned
  change source.memaddrs (header+BitVec.ofNat 64 offset) at mapped
  change source.memory (header+BitVec.ofNat 64 offset)=.word (wordAt original (header+BitVec.ofNat 64 offset)) at stored
  simp [eval,loadOne,localVar,evalHOLExact,evalListHOLExact,toExact,context.headerLocal,valueIsWord,valueWord,wordOpHOL,wordOp,
    memLoadHOLExact,isWfShapeExactHOL,address,mapped,stored]

def wideWords (original : Memory) (header : BitVec 64) (offset : Nat) : RlpWrite.U256Value.Words :=
  fun index=>wordAt original (address header (offset+8*index.val))

theorem Context.load_wide (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64)
    (context : Context source original header buffer) (offset : Nat) (inside : offset≤216) (aligned : offset%8=0) :
    eval source (loadWide offset)=some (RlpWrite.U256Value.tuple (wideWords original header offset)) := by
  classical
  have cells : ∀ index : Fin 4,source.memaddrs (address header (offset+8*index.val)) ∧
      source.memory (address header (offset+8*index.val))=.word (wordAt original (address header (offset+8*index.val))) := by
    intro index
    have indexBound:=index.isLt
    exact context.cell source original header buffer (offset+8*index.val) (by omega) (by omega)
  have v3 : (3 : Fin 4).val=3:=rfl
  have m0 : source.memaddrs (header+BitVec.ofNat 64 offset) := by simpa [address] using (cells 0).1
  have m1 : source.memaddrs (header+BitVec.ofNat 64 offset+8#64) := by simpa [address,BitVec.ofNat_add,BitVec.add_assoc] using (cells 1).1
  have m2 : source.memaddrs (header+BitVec.ofNat 64 offset+8#64+8#64) := by simpa [address,BitVec.ofNat_add,BitVec.add_assoc] using (cells 2).1
  have m3 : source.memaddrs (header+BitVec.ofNat 64 offset+8#64+8#64+8#64) := by simpa [address,BitVec.ofNat_add,BitVec.add_assoc,v3] using (cells 3).1
  have s0 : source.memory (header+BitVec.ofNat 64 offset)=.word (wideWords original header offset 0) := by simpa [address,wideWords] using (cells 0).2
  have s1 : source.memory (header+BitVec.ofNat 64 offset+8#64)=.word (wideWords original header offset 1) := by simpa [address,wideWords,BitVec.ofNat_add,BitVec.add_assoc] using (cells 1).2
  have s2 : source.memory (header+BitVec.ofNat 64 offset+8#64+8#64)=.word (wideWords original header offset 2) := by simpa [address,wideWords,BitVec.ofNat_add,BitVec.add_assoc] using (cells 2).2
  have s3 : source.memory (header+BitVec.ofNat 64 offset+8#64+8#64+8#64)=.word (wideWords original header offset 3) := by simpa [address,wideWords,BitVec.ofNat_add,BitVec.add_assoc,v3] using (cells 3).2
  simp [eval,loadWide,localVar,evalHOLExact,evalListHOLExact,toExact,context.headerLocal,valueIsWord,valueWord,wordOpHOL,wordOp,
    RlpWrite.U256Value.tupleShape,RlpWrite.U256Value.tuple,isWfShapeExactHOL,isWfShapesExactHOL,memLoadHOLExact,memLoadsHOLExact,
    bytesInWordHOL,sizeOfShapeWithContextHOL,m0,m1,m2,m3,s0,s1,s2,s3]

end InitECandidate.Solver.Input.HeaderEncoding

#print axioms InitECandidate.Solver.Input.HeaderEncoding.Context.load_one
#print axioms InitECandidate.Solver.Input.HeaderEncoding.Context.load_wide
