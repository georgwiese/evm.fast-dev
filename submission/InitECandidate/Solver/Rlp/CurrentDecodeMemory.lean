import InitECandidate.Solver.Rlp.DecodeNormalFrame
import InitECandidate.Solver.Rlp.CurrentDecodeCost
import InitECandidate.Solver.Rlp.CurrentItem.Memory

namespace InitECandidate.Solver.Rlp.CurrentDecode
open Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

abbrev Complete := Decode.Complete

theorem after_item_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (answer : ValueHOL 64) (valid : Item.Valid pointer length.toNat answer)
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (itemCell : source.locals.lookup (ofString "it")=some answer)
    (arena : LiveArena source) (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterItem=(some (.returned value),post)) :
    Complete pointer length value ∧ Input.LocalEffects.erase post=Input.LocalEffects.erase source := by
  obtain ⟨header,payload,flag,same,small,positive,bounded,binary,listHeader⟩ := valid
  rw [same] at itemCell
  obtain ⟨guardRun,returnRun⟩ := Fail.guard_return source post _ [.const 6#64] (.return (localVar "it")) value installed normal
  have passed := (Fail.guard_normal source source _ [.const 6#64] installed guardRun).1
  have testRead : eval source (.cmp .notEqual (.rfield 3 (localVar "it")) (localVar "len"))=
      some (.val (.word (if header+payload≠length then 1#64 else 0#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,itemCell,lengthCell,Item.result,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have totalEq : header+payload=length := by
    by_contra different
    rw [if_pos different] at testRead
    have impossible : (1#64 : BitVec 64)=0#64 := by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using testRead.symm.trans passed
    exact (by decide : (1#64 : BitVec 64)≠0#64) impossible
  have totalNumber : (header+payload).toNat=header.toNat+payload.toNat := BitVec.toNat_add_of_lt (by have := length.isLt; omega)
  have totalExtent : header.toNat+payload.toNat=length.toNat := by rw [←totalNumber,totalEq]
  obtain ⟨read,returned⟩ := Input.return_normal source post (localVar "it") value returnRun
  have itemRead : eval source (localVar "it")=some (Item.result pointer header payload flag) := by simp [eval,evalHOLExact,localVar,toExact,itemCell]
  have valueEq : value=Item.result pointer header payload flag := Option.some.inj (read.symm.trans itemRead)
  refine ⟨⟨header,payload,flag,valueEq,small,positive,totalExtent,binary,listHeader⟩,
    ?_⟩
  · rw [returned]; rfl

/-- A real full decode checks that the positive total occupies exactly its
input extent, retains the actual payload/kind words and the original arena. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : LiveArena source) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    Complete pointer length value ∧ CurrentItem.Frame source post ∧ source.clock-post.clock≤60*length.toNat+12 := by
  have priced := body_cost source pointer length pointerCell lengthCell arena fits installed
  rw [normal] at priced
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_item") Item.body Item.resultShape pointer length (Item.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length) := by
    simp [arguments,Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,lengthCell]
  rw [body_shape] at normal
  obtain ⟨positive,calleePost,answer,inner,bodyRun,checked,continuation,restored⟩ := Input.CallNormal.scoped_normal source post "it" Item.resultShape (ofString "rlp_item") arguments _ Item.body afterItem callee Item.resultShape args called value normal
  obtain ⟨valid,nextArena,itemPrice⟩ := CurrentItem.body_normal (callEntryStateHOLFinite source callee) calleePost pointer length pointerLocal lengthLocal
    (arena.of_frame rfl) fits installed answer bodyRun
  let ready := Input.CallNormal.continuationEntry source calleePost "it" answer
  have currentLength : ready.locals.lookup (ofString "len")=some (.val (.word length)) := by
    simpa [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      show ofString "it"≠ofString "len" from by decide] using lengthCell
  have currentItem : ready.locals.lookup (ofString "it")=some answer := by
    simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have codeEq := (Input.evaluation_fields (callEntryStateHOLFinite source callee) calleePost Item.body (some (.returned answer)) bodyRun).2.2.2
  obtain ⟨complete,returnedArena⟩ := after_item_normal ready inner pointer length answer valid currentLength currentItem
    (arena.of_metadata nextArena.metadata) (by change Input.OriginalCode.Installed calleePost.code; rw [codeEq]; exact installed) value continuation
  refine ⟨complete,?_,priced⟩
  · rw [restored]
    exact ((CurrentItem.Frame.of_readonly returnedArena).trans (nextArena.of_erase rfl rfl)).of_erase rfl rfl

/-- Complete nested decoding keeps live records above its actual entering
scratch cursor as well as the original persistent input below scratch. -/
theorem body_normal_above (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : LiveArena source) (physical : Validation.Arena source cursor limit)
    (fits : pointer.toNat+length.toNat<2^64) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source Decode.body=(some (.returned value),post)) :
    Decode.Complete pointer length value ∧ CurrentItem.Frame source post ∧ Validation.Above source post cursor.toNat ∧
      source.clock-post.clock≤60*length.toNat+12 := by
  obtain ⟨complete,frame,price⟩:=body_normal source post pointer length pointerCell lengthCell arena fits installed value normal
  obtain ⟨actual,next,above,oldPrice⟩:=Decode.body_normal_above source post pointer length cursor limit
    pointerCell lengthCell physical fits installed value normal
  exact ⟨complete,frame,above,price⟩

end InitECandidate.Solver.Rlp.CurrentDecode

#print axioms InitECandidate.Solver.Rlp.CurrentDecode.after_item_normal
#print axioms InitECandidate.Solver.Rlp.CurrentDecode.body_normal

#print axioms InitECandidate.Solver.Rlp.CurrentDecode.body_normal_above
