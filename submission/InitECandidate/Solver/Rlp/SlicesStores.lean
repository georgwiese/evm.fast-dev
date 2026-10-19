import InitECandidate.Solver.Rlp.SlicesProgram
import InitECandidate.Solver.Input.WordStoreNormal
import InitECandidate.Solver.Input.AssignNormal

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def row (array index : BitVec 64) : BitVec 64 := array+index*16#64
def written (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer array index offset size : BitVec 64) :=
  {source with memory:=(WitnessRadix.StoreWord.put
    (WitnessRadix.StoreWord.put source.memory (row array index) (pointer+offset)) (row array index+8#64) size)}
def storesPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer array index offset size : BitVec 64) :=
  bind (bind (written source pointer array index offset size) "off" (offset+size)) "i" (index+1#64)

structure Locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer array index offset count : BitVec 64) : Prop where
  pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer))
  arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array))
  indexCell : source.locals.lookup (ofString "i")=some (.val (.word index))
  offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset))
  countCell : source.locals.lookup (ofString "count")=some (.val (.word count))

theorem Locals.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer array index offset count : BitVec 64)
    (view : Locals source pointer array index offset count) (locals : target.locals=source.locals) : Locals target pointer array index offset count := by
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals rw [locals]
  · exact view.pointerCell
  · exact view.arrayCell
  · exact view.indexCell
  · exact view.offsetCell
  · exact view.countCell

theorem stores_post_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer array index offset count size : BitVec 64)
    (view : Locals source pointer array index offset count) :
    Locals (storesPost source pointer array index offset size) pointer array (index+1#64) (offset+size) count := by
  refine ⟨?_,?_,bind_lookup_same _ _ _,?_,?_⟩
  · exact (bind_lookup_other _ "i" "p" _ (by decide)).trans ((bind_lookup_other _ "off" "p" _ (by decide)).trans view.pointerCell)
  · exact (bind_lookup_other _ "i" "arr" _ (by decide)).trans ((bind_lookup_other _ "off" "arr" _ (by decide)).trans view.arrayCell)
  · exact (bind_lookup_other _ "i" "off" _ (by decide)).trans (bind_lookup_same _ _ _)
  · exact (bind_lookup_other _ "i" "count" _ (by decide)).trans ((bind_lookup_other _ "off" "count" _ (by decide)).trans view.countCell)

/-- Actual normal execution of the two literal array stores and both local
updates determines the complete reached state. Mapping is derived by the
normal stores; no ready-made array result is supplied. -/
theorem stores_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer array index offset count size : BitVec 64)
    (view : Locals source pointer array index offset count)
    (sizeCell : source.locals.lookup (ofString "total")=some (.val (.word size)))
    (normal : evaluateHOLFiniteState source stores=(none,target)) :
    source.memaddrs (row array index) ∧ source.memaddrs (row array index+8#64) ∧
      target=storesPost source pointer array index offset size := by
  rw [stores] at normal
  obtain ⟨firstPost,firstRun,tailRun⟩ := Input.sequence_none source target _ _ normal
  have addressRead : eval source cell=some (.val (.word (row array index))) := by
    simp [cell,row,eval,evalHOLExact,evalListHOLExact,localVar,toExact,view.arrayCell,view.indexCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]
  have pointerRead : eval source (.op .add [localVar "p",localVar "off"])=some (.val (.word (pointer+offset))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,view.pointerCell,view.offsetCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨firstMapped,firstEq⟩ := Input.word_store_normal source firstPost _ _ (row array index) (pointer+offset) addressRead pointerRead firstRun
  have firstLocals : firstPost.locals=source.locals := by rw [firstEq]
  have firstView := Locals.of_fields source firstPost pointer array index offset count view firstLocals
  have firstSize : firstPost.locals.lookup (ofString "total")=some (.val (.word size)) := by rw [firstLocals]; exact sizeCell
  obtain ⟨secondPost,secondRun,advanceRun⟩ := Input.sequence_none firstPost target _ _ tailRun
  have lengthAddress : eval firstPost (.op .add [localVar "arr",.panop .mul [localVar "i",.const 16#64],.const 8#64])=
      some (.val (.word (row array index+8#64))) := by
    simp [row,eval,evalHOLExact,evalListHOLExact,localVar,toExact,firstView.arrayCell,firstView.indexCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.add_assoc]
  have sizeRead : eval firstPost (localVar "total")=some (.val (.word size)) := by simp [eval,evalHOLExact,localVar,toExact,firstSize]
  obtain ⟨secondMapped,secondEq⟩ := Input.word_store_normal firstPost secondPost _ _ (row array index+8#64) size lengthAddress sizeRead secondRun
  have secondLocals : secondPost.locals=source.locals := by rw [secondEq,firstLocals]
  have secondView := Locals.of_fields source secondPost pointer array index offset count view secondLocals
  have secondSize : secondPost.locals.lookup (ofString "total")=some (.val (.word size)) := by rw [secondLocals]; exact sizeCell
  rw [advances] at advanceRun
  obtain ⟨offsetPost,offsetRun,indexRun⟩ := Input.sequence_none secondPost target _ _ advanceRun
  have offsetRead : eval secondPost (.op .add [localVar "off",localVar "total"])=some (.val (.word (offset+size))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,secondView.offsetCell,secondSize,valueIsWord,valueWord,wordOpHOL,wordOp]
  have offsetEq := Input.assign_none secondPost offsetPost "off" _ (offset+size) offsetRead offsetRun
  have offsetIndex : offsetPost.locals.lookup (ofString "i")=some (.val (.word index)) := by
    rw [offsetEq]
    exact (bind_lookup_other _ "off" "i" _ (by decide)).trans secondView.indexCell
  have indexRead : eval offsetPost (.op .add [localVar "i",.const 1#64])=some (.val (.word (index+1#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,offsetIndex,valueIsWord,valueWord,wordOpHOL,wordOp]
  have targetEq := Input.assign_none offsetPost target "i" _ (index+1#64) indexRead indexRun
  refine ⟨firstMapped,?_,?_⟩
  · simpa only [firstEq] using secondMapped
  · rw [targetEq,offsetEq,secondEq,firstEq]
    rfl

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.Locals.of_fields
#print axioms InitECandidate.Solver.Rlp.Slices.stores_post_locals
#print axioms InitECandidate.Solver.Rlp.Slices.stores_none
