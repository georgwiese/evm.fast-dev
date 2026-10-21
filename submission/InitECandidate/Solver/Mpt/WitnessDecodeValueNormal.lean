import InitECandidate.Solver.Mpt.WitnessDecodeRows
import InitECandidate.Solver.Mpt.FailGuardReturn
import InitECandidate.Solver.Rlp.ItemCallEncoding
import InitECandidate.Solver.Rlp.ItemFrameTrace
import InitECandidate.Solver.Rlp.ItemCallGlobalsNormal
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine original leaf return parses the actual row1 value string.
Its real item, retained rows, unchanged heap and scratch-protected memory
are available at the actual leaf allocation, with the original vi scope. -/
theorem value_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array listPointer cursor limit : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) (valueItem : Rlp.ListItem)
    (rows : Rows source array listPointer bytes items) (selected : items[1]?=some valueItem)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (scratchBelow : cursor.toNat≤array.toNat) (arena : Rlp.Validation.Arena source cursor limit)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source leafBody=(some (.returned value),post)) :
    ∃ target header payload inner,
      let ready:=Input.CallNormal.continuationEntry source target "vi" (Rlp.Item.result (Rlp.Slices.itemPointer listPointer items 1) header payload 0#64)
      Rlp.Item.Valid (Rlp.Slices.itemPointer listPointer items 1) valueItem.total.toNat (Rlp.Item.result (Rlp.Slices.itemPointer listPointer items 1) header payload 0#64) ∧
      payload.toNat≤bytes ∧ Rows ready array listPointer bytes items ∧ Rlp.Validation.Arena ready cursor limit ∧
      Rlp.Validation.Above source ready cursor.toNat ∧ ready.code=source.code ∧
      ready.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr") ∧
      ready.memaddrs=source.memaddrs ∧ ready.be=source.be ∧
      (∀ key,ready.globals.lookup key=source.globals.lookup key) ∧
      ready.locals.lookup (ofString "arr")=some (.val (.word array)) ∧
      ready.locals.lookup (ofString "vi")=some (Rlp.Item.result (Rlp.Slices.itemPointer listPointer items 1) header payload 0#64) ∧
      evaluateHOLFiniteState ready leafAllocate=(some (.returned value),inner) ∧ post=restore source "vi" inner := by
  obtain ⟨args,positive,valueBound,lower,upper⟩:=rows.arguments source array listPointer bytes 1 items valueItem selected arrayCell
  have fits : (Rlp.Slices.itemPointer listPointer items 1).toNat+valueItem.total.toNat<2^64:=upper.trans_lt rows.fits
  rw [value_shape] at normal
  obtain ⟨funded,target,header,payload,flag,inner,valid,nextArena,above,domain,endian,codeEq,heapEq,globalCells,price,continued,endpoint⟩:=
    Rlp.Item.scoped_normal_globals source post (Rlp.Slices.itemPointer listPointer items 1) valueItem.total cursor limit "vi" (recordArguments 1) afterValue args arena fits installed value normal
  let ready:=Input.CallNormal.continuationEntry source target "vi" (Rlp.Item.result (Rlp.Slices.itemPointer listPointer items 1) header payload flag)
  have currentInstalled : Input.OriginalCode.Installed ready.code:=by
    change Input.OriginalCode.Installed target.code
    rw [codeEq]
    exact installed
  rw [after_value_shape] at continued
  obtain ⟨guardRun,allocationRun⟩:=Fail.guard_return ready inner (.cmp .notEqual (field "vi" 0) (.const 0#64)) [.const 6#64] leafAllocate value currentInstalled continued
  have passed:=(Fail.guard_normal ready ready _ [.const 6#64] currentInstalled guardRun).1
  have valueCell : ready.locals.lookup (ofString "vi")=some (Rlp.Item.result (Rlp.Slices.itemPointer listPointer items 1) header payload flag):=
    Input.CallNormal.continuation_lookup_same _ _ _ _
  have flagZero : flag=0#64:=by
    by_contra different
    have test : eval ready (.cmp .notEqual (field "vi" 0) (.const 0#64))=some (.val (.word 1#64)):=by
      simp [eval,field,evalHOLExact,localVar,toExact,valueCell,Rlp.Item.result,different,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have impossible : (1#64 : BitVec 64)=0#64:=by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using test.symm.trans passed
    exact (by decide : (1#64 : BitVec 64)≠0#64) impossible
  have currentRows : Rows ready array listPointer bytes items:=rows.above source ready array listPointer bytes items cursor.toNat scratchBelow domain above
  have currentArena:=Rlp.Validation.Arena.of_fields target ready cursor limit nextArena rfl rfl
  have currentArray : ready.locals.lookup (ofString "arr")=some (.val (.word array)):=
    (Input.CallNormal.continuation_lookup_other source target "vi" "arr" _ (by decide)).trans arrayCell
  have actualFields:=Rlp.Item.Valid.result_fields (Rlp.Slices.itemPointer listPointer items 1) header payload flag valueItem.total.toNat valid
  subst flag
  exact ⟨target,header,payload,inner,valid,by omega,currentRows,currentArena,above,codeEq,heapEq,domain,endian,globalCells,currentArray,valueCell,allocationRun,endpoint⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.value_normal
