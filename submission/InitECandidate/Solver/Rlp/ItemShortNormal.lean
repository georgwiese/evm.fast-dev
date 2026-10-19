import InitECandidate.Solver.Rlp.ItemValue
import InitECandidate.Solver.Rlp.CanonicalReturn
import InitECandidate.Solver.Rlp.ListCountIgnored

namespace InitECandidate.Solver.Rlp.Item
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem valid_short (pointer length payload flag : BitVec 64) (binary : flag=0#64 ∨ flag=1#64)
    (bounded : 1+payload.toNat≤length.toNat) : Valid pointer length.toNat (result pointer 1#64 payload flag) :=
  ⟨1#64,payload,flag,rfl,by decide,by change 1≤1+payload.toNat; omega,bounded,binary,by intro flag; decide⟩

theorem short_return_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer payload flag cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (payloadCell : source.locals.lookup (ofString "n")=some (.val (.word payload)))
    (arena : Validation.Arena source cursor limit) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (shortReturn flag)=(some (.returned value),post)) :
    value=result pointer 1#64 payload flag ∧ Validation.Arena post cursor limit := by
  have read : eval source (.rstruct [.const flag,.op .add [localVar "p",.const 1#64],localVar "n",.op .add [.const 1#64,localVar "n"]])=
      some (result pointer 1#64 payload flag) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,pointerCell,payloadCell,result,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨actual,returned⟩ := Input.return_normal source post _ value normal
  refine ⟨Option.some.inj (actual.symm.trans read),Validation.Arena.of_fields source post cursor limit arena ?_ ?_⟩
  · rw [returned]; rfl
  · rw [returned]; rfl

theorem single_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (entry : Entry source pointer length cursor limit) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source single=(some (.returned value),post)) :
    Valid pointer length.toNat value ∧ Validation.Arena post cursor limit := by
  rw [single_shape] at normal
  obtain ⟨actual,returned⟩ := Input.return_normal source post _ value normal
  have read : eval source (.rstruct [.const 0#64,localVar "p",.const 1#64,.const 1#64])=some (result pointer 0#64 1#64 0#64) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,entry.pointerCell,result]
  have same : value=result pointer 0#64 1#64 0#64 := Option.some.inj (actual.symm.trans read)
  refine ⟨⟨0#64,1#64,0#64,same,by decide,by decide,entry.nonempty,Or.inl rfl,?_⟩,
    Validation.Arena.of_fields source post cursor limit entry.arena ?_ ?_⟩
  · intro impossible; exact ((by decide : (0#64 : BitVec 64)≠1#64) impossible).elim
  · rw [returned]; rfl
  · rw [returned]; rfl

theorem short_string_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit byte : BitVec 64)
    (entry : Entry source pointer length cursor limit)
    (byteCell : source.locals.lookup (ofString "b")=some (.val (.word byte)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source shortString=(some (.returned value),post)) :
    Valid pointer length.toNat value ∧ Validation.Arena post cursor limit := by
  have read : eval source (.op .sub [localVar "b",.const 128#64])=some (.val (.word (byte-128#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,byteCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [short_string_shape] at normal
  obtain ⟨inner,innerRun,restored⟩ := Input.declaration_return_word source post "n" _ (byte-128#64) _ value read normal
  let entered := bind source "n" (byte-128#64)
  have enteredEntry : Entry entered pointer length cursor limit := Entry.bound_word source pointer length cursor limit (byte-128#64) "n" entry (by decide) (by decide)
  have payloadCell : entered.locals.lookup (ofString "n")=some (.val (.word (byte-128#64))) := bind_lookup_same _ _ _
  obtain ⟨bounded,tailRun⟩ := Header.short_guard_extent entered inner length (byte-128#64) entry.nonempty enteredEntry.lengthCell payloadCell _ value installed innerRun
  have returnRun := Header.canonical_return entered inner (byte-128#64) payloadCell (shortReturn 0#64) value installed tailRun
  obtain ⟨same,nextArena⟩ := short_return_normal entered inner pointer (byte-128#64) 0#64 cursor limit enteredEntry.pointerCell payloadCell enteredEntry.arena value returnRun
  refine ⟨by rw [same]; exact valid_short pointer length (byte-128#64) 0#64 (Or.inl rfl) bounded,
    Validation.Arena.of_fields inner post cursor limit nextArena ?_ ?_⟩
  · rw [restored]; rfl
  · rw [restored]; rfl

theorem short_list_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit byte : BitVec 64)
    (entry : Entry source pointer length cursor limit)
    (byteCell : source.locals.lookup (ofString "b")=some (.val (.word byte)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source shortList=(some (.returned value),post)) :
    Valid pointer length.toNat value ∧ Validation.Arena post cursor limit := by
  have read : eval source (.op .sub [localVar "b",.const 192#64])=some (.val (.word (byte-192#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,byteCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [short_list_shape] at normal
  obtain ⟨inner,innerRun,restored⟩ := Input.declaration_return_word source post "n" _ (byte-192#64) _ value read normal
  let entered := bind source "n" (byte-192#64)
  have enteredEntry : Entry entered pointer length cursor limit := Entry.bound_word source pointer length cursor limit (byte-192#64) "n" entry (by decide) (by decide)
  have payloadCell : entered.locals.lookup (ofString "n")=some (.val (.word (byte-192#64))) := bind_lookup_same _ _ _
  obtain ⟨bounded,tailRun⟩ := Header.short_guard_extent entered inner length (byte-192#64) entry.nonempty enteredEntry.lengthCell payloadCell _ value installed innerRun
  obtain ⟨middle,countRun,returnRun⟩ := Input.sequence_returned entered inner shortCount (shortReturn 1#64) value (Input.NoReturn.ignored_call _ _ entered) tailRun
  have args : evalListHOLFinite entered (h:=fun address=>Classical.propDecidable (entered.memaddrs address)) [.op .add [localVar "p",.const 1#64],localVar "n"]=some (Header.values (pointer+1#64) (byte-192#64)) := by
    simp [Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,enteredEntry.pointerCell,payloadCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have number : (pointer+1#64).toNat=pointer.toNat+1 := BitVec.toNat_add_of_lt (by change pointer.toNat+1<2^64; have := entry.fits; have := entry.nonempty; omega)
  have fits : (pointer+1#64).toNat+(byte-192#64).toNat<2^64 := by rw [number]; have := entry.fits; omega
  obtain ⟨locals,nextArena⟩ := ListCount.ignored_normal entered middle (pointer+1#64) (byte-192#64) cursor limit _ args enteredEntry.arena fits installed countRun
  have nextPointer : middle.locals.lookup (ofString "p")=some (.val (.word pointer)) := by rw [locals]; exact enteredEntry.pointerCell
  have nextPayload : middle.locals.lookup (ofString "n")=some (.val (.word (byte-192#64))) := by rw [locals]; exact payloadCell
  obtain ⟨same,returnedArena⟩ := short_return_normal middle inner pointer (byte-192#64) 1#64 cursor limit nextPointer nextPayload nextArena value returnRun
  refine ⟨by rw [same]; exact valid_short pointer length (byte-192#64) 1#64 (Or.inr rfl) bounded,
    Validation.Arena.of_fields inner post cursor limit returnedArena ?_ ?_⟩
  · rw [restored]; rfl
  · rw [restored]; rfl

end InitECandidate.Solver.Rlp.Item

#print axioms InitECandidate.Solver.Rlp.Item.valid_short
#print axioms InitECandidate.Solver.Rlp.Item.short_return_normal
#print axioms InitECandidate.Solver.Rlp.Item.single_normal
#print axioms InitECandidate.Solver.Rlp.Item.short_string_normal
#print axioms InitECandidate.Solver.Rlp.Item.short_list_normal
