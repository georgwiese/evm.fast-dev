import InitECandidate.Solver.Rlp.ListCountBodyEncoding
import InitECandidate.Solver.Rlp.ByteAgreementFrame

namespace InitECandidate.Solver.Rlp.ListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem condition_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length offset : BitVec 64)
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length))) :
    eval source condition=some (.val (.word (if offset.toNat<length.toNat then 1#64 else 0#64))) := by
  simp [condition,eval,evalHOLExact,localVar,toExact,offsetCell,lengthCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]

/-- The actual first pass derives an ordered sequence covering precisely
the remaining input, and its actual final count. The common aligned cutoff
places scratch writes below all input bytes; no later item models are given. -/
theorem loop_items (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length cursor limit offset count : BitVec 64) (cutoff : Nat)
    (view : View source pointer length cursor limit offset count)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source loop=(none,target)) :
    ∃ items : List ListItem,∃ finalCount : BitVec 64,
      ListItems source (pointer+offset) (length.toNat-offset.toNat) items ∧
      View target pointer length cursor limit length finalCount ∧ finalCount.toNat=count.toNat+items.length ∧
      Validation.Above source target cursor.toNat := by
  classical
  have auxiliary : ∀ remaining (current post : PanSemStateFiniteExact 64 Guest.HostMemory) (offset count : BitVec 64),
      length.toNat-offset.toNat=remaining → View current pointer length cursor limit offset count →
      Input.OriginalCode.Installed current.code → evaluateHOLFiniteState current loop=(none,post) →
      ∃ items : List ListItem,∃ finalCount : BitVec 64,
        ListItems current (pointer+offset) (length.toNat-offset.toNat) items ∧
        View post pointer length cursor limit length finalCount ∧ finalCount.toNat=count.toNat+items.length ∧
        Validation.Above current post cursor.toNat := by
    intro remaining
    induction remaining using Nat.strong_induction_on with
    | h remaining ih =>
      intro current post offset count remainingEq view installed run
      have read := condition_read current length offset view.offsetCell view.lengthCell
      by_cases active : offset.toNat<length.toNat
      · rw [if_pos active] at read
        have loopRun := run
        rw [loop_shape] at loopRun
        obtain ⟨positive,middle,bodyRun,tailRun,clock⟩ :=
          Input.while_none_step current post (ofString "p") condition loopBody loop_body_safe read loopRun
        have entryView := View.clock current pointer length cursor limit offset count view (current.clock-1)
        obtain ⟨item,itemValid,encoding,sizeBound,nextView,offsetNumber,countNumber,above,price⟩ :=
          loop_body_encoding (decClockHOLFinite current) middle pointer length cursor limit offset count entryView installed bodyRun
        have itemPositive := item.positive itemValid
        have remainingNumber : (length-offset).toNat=length.toNat-offset.toNat := BitVec.toNat_sub_of_le view.bounded
        rw [remainingNumber] at sizeBound
        have smaller : length.toNat-(offset+item.total).toNat<remaining := by omega
        have fields := Input.evaluation_fields (decClockHOLFinite current) middle loopBody none bodyRun
        have middleInstalled : Input.OriginalCode.Installed middle.code := by rw [fields.2.2.2]; exact installed
        rw [←loop_shape] at tailRun
        obtain ⟨items,finalCount,tailItems,finalView,finalNumber,tailAbove⟩ :=
          ih (length.toNat-(offset+item.total).toNat) smaller middle post (offset+item.total) (count+1#64) rfl nextView middleInstalled tailRun
        have startNumber : (pointer+(offset+item.total)).toNat=pointer.toNat+(offset+item.total).toNat :=
          BitVec.toNat_add_of_lt (by have := view.fits; have := nextView.bounded; omega)
        have restNumber : (length-(offset+item.total)).toNat=length.toNat-(offset+item.total).toNat := BitVec.toNat_sub_of_le nextView.bounded
        have inputFits : (pointer+(offset+item.total)).toNat+(length-(offset+item.total)).toNat<2^64 := by
          rw [startNumber,restNumber]; have := view.fits; omega
        have wordFrame : Validation.Above current middle cutoff :=
          Validation.Above.mono current middle cursor.toNat cutoff above scratchBelow
        have byteFrame := Validation.Above.bytes_agree current middle cutoff (pointer+(offset+item.total))
          (length-(offset+item.total)) wordFrame aligned (by rw [startNumber]; omega) inputFits fields.1 fields.2.1
        have restoredItems := ListItems.transport middle current (pointer+(offset+item.total))
          (length.toNat-(offset+item.total).toNat) items tailItems (by have := length.isLt; omega)
          (fun next inside=>(byteFrame next (by rw [restNumber]; exact inside)).symm)
        have tailModel : ListItems current ((pointer+offset)+item.total)
            (length.toNat-(offset+item.total).toNat) items := by simpa only [BitVec.add_assoc] using restoredItems
        have currentEncoding : Header.Encoded current (pointer+offset) item.header item.payload item.flag := encoding
        have allItems := ListItems.cons (pointer+offset) item (length.toNat-(offset+item.total).toNat) items currentEncoding itemValid tailModel
        have extent : item.size+(length.toNat-(offset+item.total).toNat)=length.toNat-offset.toNat := by have := nextView.bounded; omega
        rw [extent] at allItems
        refine ⟨item::items,finalCount,allItems,finalView,?_,?_⟩
        · simp only [List.length_cons]
          omega
        · exact Validation.Above.trans current middle post cursor.toNat above tailAbove
      · rw [if_neg active] at read
        rw [loop_shape,evaluateHOLFiniteState_while_total] at run
        change evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) condition=some (.val (.word 0#64)) at read
        rw [read] at run
        have same : post=current := by simpa using (congrArg Prod.snd run).symm
        subst post
        have offsetEq : offset=length := BitVec.eq_of_toNat_eq (by have := view.bounded; omega)
        refine ⟨[],count,?_,?_,by simp,Validation.Above.refl current cursor.toNat⟩
        · have empty : length.toNat-offset.toNat=0 := by rw [offsetEq]; omega
          rw [empty]
          exact .nil _
        · simpa only [offsetEq] using view
  exact auxiliary (length.toNat-offset.toNat) source target offset count rfl view installed normal

end InitECandidate.Solver.Rlp.ListCount

#print axioms InitECandidate.Solver.Rlp.ListCount.condition_read
#print axioms InitECandidate.Solver.Rlp.ListCount.loop_items
