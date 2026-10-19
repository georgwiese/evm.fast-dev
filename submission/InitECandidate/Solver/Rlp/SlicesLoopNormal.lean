import InitECandidate.Solver.Rlp.SlicesBodyNormal
import InitECandidate.Solver.Rlp.SliceArrayModel
import InitECandidate.Solver.Rlp.ListItemsData
import InitECandidate.Solver.Rlp.ByteAgreementSubspan

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem condition_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index count : BitVec 64)
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (countCell : source.locals.lookup (ofString "count")=some (.val (.word count))) :
    eval source condition=some (.val (.word (if index.toNat<count.toNat then 1#64 else 0#64))) := by
  simp [condition,eval,evalHOLExact,localVar,toExact,indexCell,countCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]

/-- Actual normal second-pass execution fills every real pointer/length
record from the first pass's derived item sequence, ends at the exact input
extent, and preserves every ordinary word outside its fresh array suffix. -/
theorem loop_records (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length array index offset count : BitVec 64) (items : List ListItem)
    (view : Locals source pointer array index offset count)
    (model : ListItems source (pointer+offset) (length.toNat-offset.toNat) items)
    (offsetBound : offset.toNat≤length.toNat) (countEq : count.toNat=index.toNat+items.length)
    (before : pointer.toNat+length.toNat≤array.toNat) (arrayFits : array.toNat+16*count.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source loop=(none,target)) :
    Records target.memory (row array index) (pointer+offset) items ∧
      Locals target pointer array count length count ∧ target.globals=source.globals ∧
      Window source target (array.toNat+16*index.toNat) (array.toNat+16*count.toNat) := by
  classical
  induction items generalizing source target index offset with
  | nil =>
    have indexEq : index=count := BitVec.eq_of_toNat_eq (by simpa using countEq.symm)
    have empty := ListItems.nil_extent source (pointer+offset) (length.toNat-offset.toNat) model
    have offsetEq : offset=length := BitVec.eq_of_toNat_eq (by omega)
    have read := condition_read source index count view.indexCell view.countCell
    have inactive : ¬index.toNat<count.toNat := by rw [indexEq]; omega
    rw [if_neg inactive] at read
    rw [loop_shape,evaluateHOLFiniteState_while_total] at normal
    change evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) condition=some (.val (.word 0#64)) at read
    rw [read] at normal
    have same : target=source := by simpa using (congrArg Prod.snd normal).symm
    subst target
    exact ⟨True.intro,by simpa only [indexEq,offsetEq] using view,rfl,Window.refl source _ _⟩
  | cons item items ih =>
    obtain ⟨remaining,extent,encoding,itemValid,rest⟩ := ListItems.cons_data source (pointer+offset) (length.toNat-offset.toNat) item items model
    have itemPositive := item.positive itemValid
    have totalNumber : item.total.toNat=item.size := BitVec.toNat_add_of_lt (by change item.size<2^64; have := length.isLt; omega)
    have offsetNumber : (offset+item.total).toNat=offset.toNat+item.size := by
      rw [BitVec.toNat_add_of_lt (by rw [totalNumber]; have := length.isLt; omega),totalNumber]
    have nextOffsetBound : (offset+item.total).toNat≤length.toNat := by rw [offsetNumber]; omega
    have restExtent : remaining=length.toNat-(offset+item.total).toNat := by rw [offsetNumber]; omega
    have active : index.toNat<count.toNat := by simp only [List.length_cons] at countEq; omega
    have indexNumber : (index+1#64).toNat=index.toNat+1 := by
      rw [BitVec.toNat_add_of_lt (by change index.toNat+1<2^64; have := count.isLt; omega)]
      rfl
    have read := condition_read source index count view.indexCell view.countCell
    rw [if_pos active] at read
    have loopRun := normal
    rw [loop_shape] at loopRun
    obtain ⟨positive,middle,bodyRun,tailRun,clock⟩ :=
      Input.while_none_step source target (ofString "count") condition loopBody loop_body_safe read loopRun
    have entryView := Locals.of_fields source (decClockHOLFinite source) pointer array index offset count view rfl
    obtain ⟨paid,minimum,maximum,funded,middleEq⟩ := loop_body_none (decClockHOLFinite source) middle pointer array index offset count item entryView encoding installed bodyRun
    have middleView : Locals middle pointer array (index+1#64) (offset+item.total) count := by
      rw [middleEq]
      exact body_post_locals (decClockHOLFinite source) pointer array index offset count item.total paid entryView
    have byteFrame : ReadLength.BytesAgree source middle pointer length := by
      rw [middleEq]
      exact stores_input_bytes source pointer length array index count offset item.total before active arrayFits
    have currentRest : ListItems source (pointer+(offset+item.total))
        (length.toNat-(offset+item.total).toNat) items := by
      rw [←restExtent]
      simpa only [BitVec.add_assoc] using rest
    have middleItems := ListItems.transport source middle (pointer+(offset+item.total))
      (length.toNat-(offset+item.total).toNat) items currentRest (by have := length.isLt; omega)
      (ReadLength.BytesAgree.subspan source middle pointer length (offset+item.total)
        (length.toNat-(offset+item.total).toNat) byteFrame (by omega))
    have nextCount : count.toNat=(index+1#64).toNat+items.length := by
      rw [indexNumber]
      simp only [List.length_cons] at countEq
      omega
    have middleInstalled : Input.OriginalCode.Installed middle.code := by rw [middleEq]; exact installed
    rw [←loop_shape] at tailRun
    obtain ⟨tailRecords,finalView,finalGlobals,tailFrame⟩ := ih middle target (index+1#64) (offset+item.total)
      middleView middleItems nextOffsetBound nextCount middleInstalled tailRun
    have firstNumber := row_number array index (by omega)
    have secondNumber := row_length_number array index count active arrayFits
    have separate : row array index≠row array index+8#64 := by
      intro same
      have number := congrArg BitVec.toNat same
      rw [firstNumber,secondNumber] at number
      omega
    have middleHead : middle.memory (row array index)=.word (pointer+offset) ∧
        middle.memory (row array index+8#64)=.word item.total := by
      rw [middleEq]
      exact written_head source pointer array index offset item.total separate
    have headPreserved := tailFrame (row array index) (Or.inl (by rw [firstNumber,indexNumber]; omega))
    have lengthPreserved := tailFrame (row array index+8#64) (Or.inl (by rw [secondNumber,indexNumber]; omega))
    have tailRecordsAt : Records target.memory (row array index+16#64) ((pointer+offset)+item.total) items := by
      simpa only [row_next,BitVec.add_assoc] using tailRecords
    have fullRecords : Records target.memory (row array index) (pointer+offset) (item::items) :=
      ⟨headPreserved.trans middleHead.1,lengthPreserved.trans middleHead.2,tailRecordsAt⟩
    have middleGlobals : middle.globals=source.globals := by rw [middleEq]; rfl
    have bodyFrame : Window source middle (array.toNat+16*index.toNat) (array.toNat+16*(index.toNat+1)) := by
      rw [middleEq]
      exact stores_window source pointer array index offset item.total count active arrayFits
    have firstFrame := Window.mono source middle _ _ (array.toNat+16*index.toNat) (array.toNat+16*count.toNat)
      bodyFrame (Nat.le_refl _) (by omega)
    have restFrame := Window.mono middle target _ _ (array.toNat+16*index.toNat) (array.toNat+16*count.toNat)
      tailFrame (by rw [indexNumber]; omega) (Nat.le_refl _)
    exact ⟨fullRecords,finalView,finalGlobals.trans middleGlobals,Window.trans source middle target _ _ firstFrame restFrame⟩

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.condition_read
#print axioms InitECandidate.Solver.Rlp.Slices.loop_records
