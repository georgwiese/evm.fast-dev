import InitECandidate.Solver.Mpt.KeyToNibblesAnyFlow
import InitECandidate.Solver.Input.ByteStoreFrame
import InitECandidate.Solver.Input.ContinuingDeclarationEntry
import InitECandidate.Solver.Input.AssignNormal

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def writeMetadata (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  emptyLocalsHOLFinite {source with clock:=0,memory:=fun _=>.word 0#64}

/-- Only the backing words of the actual byte output may change. -/
structure SpanFrame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (out : BitVec 64) (length : Nat) : Prop where
  fields : writeMetadata target=writeMetadata source
  memory : ∀ query : BitVec 64,(∀ offset<length,query≠panByteAlignHOL (width:=64) (byteAddress out offset))→target.memory query=source.memory query

theorem SpanFrame.refl (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out : BitVec 64) (length : Nat) : SpanFrame source source out length:=⟨rfl,by intro query away; rfl⟩
theorem SpanFrame.trans (source middle target : PanSemStateFiniteExact 64 Guest.HostMemory) (out : BitVec 64) (length : Nat)
    (first : SpanFrame source middle out length) (second : SpanFrame middle target out length) : SpanFrame source target out length:=
  ⟨second.fields.trans first.fields,fun query away=>(second.memory query away).trans (first.memory query away)⟩

inductive Writes (size : Nat) : ProgHOL 64→Prop where
  | finish (amount : Nat) : Writes size (increment (BitVec.ofNat 64 amount))
  | store (offset : Nat) (inside : offset<size) (value : ExpHOL 64) {rest : ProgHOL 64} (tail : Writes size rest) :
      Writes size (.seq (.storeByte (outputAddress offset) value) rest)
  | declare (name : String) (expression : ExpHOL 64) (notOut : ofString "out"≠ofString name) (notIndex : ofString "i"≠ofString name)
      {rest : ProgHOL 64} (tail : Writes size rest) : Writes size (.dec (ofString name) .one expression rest)

theorem Writes.pair {size : Nat} (name : String) (offset : Nat) (inside : 2*offset+1<size) {rest : ProgHOL 64}
    (tail : Writes size rest) : Writes size (pair name offset rest):=
  .store _ (by omega) _ (.store _ inside _ tail)

theorem output_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out index : BitVec 64) (offset : Nat)
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index))) :
    eval source (outputAddress offset)=some (.val (.word (byteAddress out (2*index.toNat+offset)))) := by
  have read : eval source (outputAddress offset)=some (.val (.word (out+2#64*index+BitVec.ofNat 64 offset))):=by
    by_cases zero : offset=0
    · subst offset
      simp [eval,outputAddress,evalHOLExact,evalListHOLExact,localVar,toExact,outCell,indexCell,panOpHOL,valueIsWord,valueWord,wordOpHOL,wordOp]
    · simp [eval,outputAddress,zero,evalHOLExact,evalListHOLExact,localVar,toExact,outCell,indexCell,panOpHOL,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.add_assoc]
  simpa only [byteAddress,BitVec.ofNat_add,BitVec.ofNat_mul,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc] using read

/-- Literal byte-write blocks preserve all words outside their real output
span on normal passage. Reads and mapping are inferred from that passage;
temporary byte locals and the final counter update retain all metadata. -/
theorem Writes.normal {size : Nat} {program : ProgHOL 64} (writes : Writes size program)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (out index : BitVec 64) (length : Nat)
    (inside : 2*index.toNat+size≤length)
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (normal : evaluateHOLFiniteState source program=(none,target)) :
    SpanFrame source target out length ∧ target.locals.lookup (ofString "out")=some (.val (.word out)) := by
  induction writes generalizing source target with
  | finish amount=>
    have read : eval source (.op .add [localVar "i",.const (BitVec.ofNat 64 amount)])=some (.val (.word (index+BitVec.ofNat 64 amount))):=by
      simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,indexCell,valueIsWord,valueWord,wordOpHOL,wordOp]
    have same:=Input.assign_none source target "i" _ _ read normal
    rw [same]
    exact ⟨⟨rfl,by intro query away; rfl⟩,(bind_lookup_other source "i" "out" _ (by decide)).trans outCell⟩
  | store offset offsetInside value tail ih=>
    obtain ⟨middle,storeRun,continued⟩:=Input.sequence_none source target _ _ normal
    obtain ⟨same,away⟩:=Input.byte_store_normal_frame source middle (outputAddress offset) value _ (output_read source out index offset outCell indexCell) storeRun
    have middleOut : middle.locals.lookup (ofString "out")=some (.val (.word out)):=by rw [same]; exact outCell
    have middleIndex : middle.locals.lookup (ofString "i")=some (.val (.word index)):=by rw [same]; exact indexCell
    have first : SpanFrame source middle out length:=⟨by have fields:=congrArg writeMetadata same; exact fields,
      fun query outside=>away query (outside _ (by omega))⟩
    obtain ⟨second,nextOut⟩:=ih middle target middleOut middleIndex continued
    exact ⟨first.trans source middle target out length second,nextOut⟩
  | declare name expression notOut notIndex tail ih=>
    obtain ⟨declared,inner,read,checked,continued,endpoint⟩:=Input.CallNormal.declaration_continuing_entry source target name .one expression _ normal
    let entered:=setVarHOLFinite (ofString name) declared source
    have enteredOut : entered.locals.lookup (ofString "out")=some (.val (.word out)):=by
      simpa [entered,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notOut,Ne.symm notOut] using outCell
    have enteredIndex : entered.locals.lookup (ofString "i")=some (.val (.word index)):=by
      simpa [entered,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notIndex,Ne.symm notIndex] using indexCell
    obtain ⟨frame,innerOut⟩:=ih entered inner enteredOut enteredIndex continued
    refine ⟨⟨?_,?_⟩,?_⟩
    · rw [endpoint]
      exact frame.fields
    · intro query outside
      rw [endpoint]
      exact frame.memory query outside
    · rw [endpoint]
      change (inner.locals.resVarEq (ofString name,source.locals.lookup (ofString name))).lookup (ofString "out")=some (.val (.word out))
      rw [lookup_resVarEq_toExact]
      cases saved : source.locals.lookup (ofString name) <;> simpa [resVarHOLExact,FUPDATE,FDOMSUB,notOut] using innerOut

theorem bodies_write_span : Writes 8 blockBody ∧ Writes 2 tailBody := by
  rw [block_body_shape,tail_body_shape]
  constructor
  all_goals repeat first
    | apply Writes.declare <;> (try decide)
    | apply Writes.pair <;> (try decide)
    | exact Writes.finish _

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.SpanFrame.refl
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.SpanFrame.trans
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.Writes.pair
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.output_read
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.Writes.normal
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.bodies_write_span
