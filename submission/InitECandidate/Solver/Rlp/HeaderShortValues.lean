import InitECandidate.Solver.Rlp.HeaderValue
import InitECandidate.Solver.Rlp.FailGuardReturn
import InitECandidate.Solver.Input.ReturnFactsScalar

namespace InitECandidate.Solver.Rlp.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.ReturnFacts

theorem short_return_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (payload flag : BitVec 64) (returned : ValueHOL 64)
    (cell : source.locals.lookup (ofString "n")=some (.val (.word payload)))
    (normal : evaluateHOLFiniteState source (shortReturn flag)=(some (.returned returned),post)) :
    returned=result 1#64 payload flag := by
  have read : eval source (.rstruct [.const 1#64,localVar "n",.const flag])=some (result 1#64 payload flag) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,cell,result]
  have actual := (Input.return_normal source post _ returned normal).1
  exact (Option.some.inj (read.symm.trans actual)).symm

theorem short_guard_extent (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (length payload : BitVec 64)
    (positive : 0<length.toNat)
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (payloadCell : source.locals.lookup (ofString "n")=some (.val (.word payload)))
    (continuation : ProgHOL 64) (returned : ValueHOL 64) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.seq shortGuard continuation)=(some (.returned returned),post)) :
    1+payload.toNat≤length.toNat ∧ evaluateHOLFiniteState source continuation=(some (.returned returned),post) := by
  have leftRead : eval source (.op .sub [localVar "len",.const 1#64])=some (.val (.word (length-1#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,lengthCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have rightRead : eval source (localVar "n")=some (.val (.word payload)) := by simp [eval,evalHOLExact,localVar,toExact,payloadCell]
  obtain ⟨bound,tailRun⟩ := Fail.lower_guard_return source post _ _ (length-1#64) payload [.const 3#64] continuation returned leftRead rightRead installed normal
  have number : (length-1#64).toNat=length.toNat-1 := by
    rw [BitVec.toNat_sub_of_le (show 1#64≤length from by change 1≤length.toNat; omega)]
    rfl
  rw [number] at bound
  exact ⟨by omega,tailRun⟩

theorem single_returns (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64) (positive : 0<length.toNat) :
    Returns source single (Valid length.toNat) := by
  rw [single_shape]
  refine Input.ReturnFacts.returned source _ (result 0#64 1#64 0#64) _ ?_ ?_
  · simp [eval,evalHOLExact,evalListHOLExact,result]
  · exact ⟨0#64,1#64,0#64,rfl,by decide,by decide,by change 0+1≤length.toNat; omega,Or.inl rfl,
      by intro impossible; exact ((by decide : (0#64 : BitVec 64)≠1#64) impossible).elim⟩

theorem short_list_returns (source : PanSemStateFiniteExact 64 Guest.HostMemory) (byte length : BitVec 64)
    (positive : 0<length.toNat)
    (byteCell : source.locals.lookup (ofString "b")=some (.val (.word byte)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (installed : Input.OriginalCode.Installed source.code) : Returns source shortList (Valid length.toNat) := by
  have read : eval source (.op .sub [localVar "b",.const 192#64])=some (.val (.word (byte-192#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,byteCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [short_list_shape]
  refine Input.ReturnFacts.declared_word source "n" _ (byte-192#64) _ (Valid length.toNat) read ?_
  let entered := bind source "n" (byte-192#64)
  have currentLength : entered.locals.lookup (ofString "len")=some (.val (.word length)) :=
    (bind_lookup_other _ "n" "len" _ (by decide)).trans lengthCell
  have currentPayload : entered.locals.lookup (ofString "n")=some (.val (.word (byte-192#64))) := bind_lookup_same _ _ _
  intro post returned normal
  obtain ⟨extent,tailRun⟩ := short_guard_extent entered post length (byte-192#64) positive currentLength currentPayload _ returned installed normal
  have answer := short_return_value entered post (byte-192#64) 1#64 returned currentPayload tailRun
  exact ⟨1#64,byte-192#64,1#64,answer,by decide,by change 1≤1+(byte-192#64).toNat; omega,extent,Or.inr rfl,by intro flag; decide⟩

theorem short_string_returns (source : PanSemStateFiniteExact 64 Guest.HostMemory) (byte length : BitVec 64)
    (positive : 0<length.toNat)
    (byteCell : source.locals.lookup (ofString "b")=some (.val (.word byte)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (installed : Input.OriginalCode.Installed source.code) : Returns source shortString (Valid length.toNat) := by
  have read : eval source (.op .sub [localVar "b",.const 128#64])=some (.val (.word (byte-128#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,byteCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [short_string_shape]
  refine Input.ReturnFacts.declared_word source "n" _ (byte-128#64) _ (Valid length.toNat) read ?_
  let entered := bind source "n" (byte-128#64)
  have currentLength : entered.locals.lookup (ofString "len")=some (.val (.word length)) :=
    (bind_lookup_other _ "n" "len" _ (by decide)).trans lengthCell
  have currentPayload : entered.locals.lookup (ofString "n")=some (.val (.word (byte-128#64))) := bind_lookup_same _ _ _
  intro post returned normal
  obtain ⟨extent,tailRun⟩ := short_guard_extent entered post length (byte-128#64) positive currentLength currentPayload _ returned installed normal
  have safe : Input.LocalPrefix (ofString "n") canonicalGuard :=
    .ite _ (.ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip) .skip
  obtain ⟨middle,guardRun,returnRun,payloadEq⟩ := safe.normal_continue entered post (shortReturn 0#64) returned tailRun
  have nextPayload := payloadEq.trans currentPayload
  have answer := short_return_value middle post (byte-128#64) 0#64 returned nextPayload returnRun
  exact ⟨1#64,byte-128#64,0#64,answer,by decide,by change 1≤1+(byte-128#64).toNat; omega,extent,Or.inl rfl,by intro flag; decide⟩

end InitECandidate.Solver.Rlp.Header

#print axioms InitECandidate.Solver.Rlp.Header.short_return_value
#print axioms InitECandidate.Solver.Rlp.Header.short_guard_extent
#print axioms InitECandidate.Solver.Rlp.Header.single_returns
#print axioms InitECandidate.Solver.Rlp.Header.short_list_returns
#print axioms InitECandidate.Solver.Rlp.Header.short_string_returns
