import InitECandidate.Solver.Input.Copy32Flow
import InitECandidate.Solver.Input.ByteStoreFrame
import InitECandidate.Solver.Input.WordStoreNormal
import InitECandidate.Solver.Input.LoadOneWord
import InitECandidate.Solver.Input.AssignNormal
import InitECandidate.Solver.WitnessRadix.CopyGeneralMemory

namespace InitECandidate.Solver.Input.Copy32Span
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def metadata (source : PanSemStateFiniteExact 64 Guest.HostMemory):=
  emptyLocalsHOLFinite {source with clock:=0,memory:=fun _=>.word 0#64}

structure Frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64) (length : Nat) : Prop where
  fields : metadata target=metadata source
  memory : ∀ query : BitVec 64,CopyGeneral.Away dst query length→target.memory query=source.memory query

theorem Frame.refl (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64) (length : Nat) : Frame source source dst length:=⟨rfl,by intro query away; rfl⟩
theorem Frame.trans (source middle target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64) (length : Nat)
    (first : Frame source middle dst length) (second : Frame middle target dst length) : Frame source target dst length:=
  ⟨second.fields.trans first.fields,fun query away=>(second.memory query away).trans (first.memory query away)⟩

inductive Writes (size : Nat) : ProgHOL 64→Prop where
  | finish (amount : Nat) : Writes size (CopyBytes.increment (BitVec.ofNat 64 amount))
  | word (offset : Nat) (inside : offset<size) {rest : ProgHOL 64} (tail : Writes size rest) :
      Writes size (.seq (Copy32.wordStore offset) rest)
  | byte (offset : Nat) (inside : offset<size) {rest : ProgHOL 64} (tail : Writes size rest) :
      Writes size (.seq (CopyBytes.store offset) rest)

theorem address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst index : BitVec 64) (offset : Nat)
    (dstCell : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index))) :
    eval source (Copy32.address "dst" offset)=some (.val (.word (byteAddress dst (index.toNat+offset)))):=by
  have read:=CopyBytes.address_read source "dst" dst index offset dstCell indexCell
  simpa only [byteAddress,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc] using read

/-- The normal copy blocks write only inside their actual destination
span. Source reads, value types and mapping are derived from the run. -/
theorem Writes.normal {size : Nat} {program : ProgHOL 64} (writes : Writes size program)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst index : BitVec 64) (length : Nat)
    (inside : index.toNat+size≤length)
    (dstCell : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (normal : evaluateHOLFiniteState source program=(none,target)) :
    Frame source target dst length ∧ target.locals.lookup (ofString "dst")=some (.val (.word dst)):=by
  induction writes generalizing source target with
  | finish amount=>
    have read : eval source (.op .add [localVar "i",.const (BitVec.ofNat 64 amount)])=some (.val (.word (index+BitVec.ofNat 64 amount))):=by
      simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,indexCell,valueIsWord,valueWord,wordOpHOL,wordOp]
    have same:=assign_none source target "i" _ _ read normal
    rw [same]
    exact ⟨⟨rfl,by intro query away; rfl⟩,(bind_lookup_other source "i" "dst" _ (by decide)).trans dstCell⟩
  | word offset offsetInside tail ih=>
    obtain ⟨middle,storeRun,continued⟩:=sequence_none source target _ _ normal
    have destination:=address_read source dst index offset dstCell indexCell
    obtain ⟨value,memory,valueRead,stores,changed⟩:=store_at_normal source middle (Copy32.address "dst" offset) (.load .one (Copy32.address "src" offset)) _ destination storeRun
    obtain ⟨word,rfl⟩:=load_one_word source (Copy32.address "src" offset) value valueRead
    have actual:=word_store_normal source middle _ _ _ word destination valueRead storeRun
    have middleDst : middle.locals.lookup (ofString "dst")=some (.val (.word dst)):=by rw [actual.2]; exact dstCell
    have middleIndex : middle.locals.lookup (ofString "i")=some (.val (.word index)):=by rw [actual.2]; exact indexCell
    have first : Frame source middle dst length:=⟨by rw [actual.2]; rfl,by
      intro query away
      rw [actual.2]
      exact if_neg (away _ (by omega)).1⟩
    obtain ⟨second,nextDst⟩:=ih middle target middleDst middleIndex continued
    exact ⟨first.trans source middle target dst length second,nextDst⟩
  | byte offset offsetInside tail ih=>
    obtain ⟨middle,storeRun,continued⟩:=sequence_none source target _ _ normal
    obtain ⟨same,away⟩:=byte_store_normal_frame source middle (Copy32.address "dst" offset) (.loadByte (Copy32.address "src" offset)) _
      (address_read source dst index offset dstCell indexCell) storeRun
    have middleDst : middle.locals.lookup (ofString "dst")=some (.val (.word dst)):=by rw [same]; exact dstCell
    have middleIndex : middle.locals.lookup (ofString "i")=some (.val (.word index)):=by rw [same]; exact indexCell
    have first : Frame source middle dst length:=⟨by have fields:=congrArg metadata same; exact fields,fun query outside=>away query (outside _ (by omega)).2⟩
    obtain ⟨second,nextDst⟩:=ih middle target middleDst middleIndex continued
    exact ⟨first.trans source middle target dst length second,nextDst⟩

theorem Writes.words {size : Nat} (offsets : List Nat) (inside : ∀ offset∈offsets,offset<size) (amount : Nat) :
    Writes size (CopyWords.stores offsets (CopyBytes.increment (BitVec.ofNat 64 amount))):=by
  induction offsets with
  | nil=>exact .finish amount
  | cons offset rest ih=>exact .word offset (inside offset List.mem_cons_self) (ih (fun later member=>inside later (List.mem_cons_of_mem _ member)))

theorem Writes.bytes {size : Nat} (offsets : List Nat) (inside : ∀ offset∈offsets,offset<size) (amount : Nat) :
    Writes size (CopyBytes.stores offsets (CopyBytes.increment (BitVec.ofNat 64 amount))):=by
  induction offsets with
  | nil=>exact .finish amount
  | cons offset rest ih=>exact .byte offset (inside offset List.mem_cons_self) (ih (fun later member=>inside later (List.mem_cons_of_mem _ member)))

end InitECandidate.Solver.Input.Copy32Span

#print axioms InitECandidate.Solver.Input.Copy32Span.address_read
#print axioms InitECandidate.Solver.Input.Copy32Span.Writes.normal
#print axioms InitECandidate.Solver.Input.Copy32Span.Writes.words
#print axioms InitECandidate.Solver.Input.Copy32Span.Writes.bytes
