import InitECandidate.Solver.Mpt.NibbleKeyProgram
import InitECandidate.Solver.Input.ScalarWordShape
import InitECandidate.Solver.Input.ClockCostScopedReached

namespace InitECandidate.Solver.Mpt.NibbleKey
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem tail_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key out : BitVec 64) (length : Nat)
    (small : length+4<2^64) (installed : Input.OriginalCode.Installed source.code)
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 length))))
    (outCell : source.locals.lookup (ofString "nb2")=some (.val (.word out))) :
    source.clock-(evaluateHOLFiniteState source tail).2.clock≤length/4+4 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) convertArguments=
      some (KeyToNibbles.anyValues key (BitVec.ofNat 64 length) out):=by
    simp [convertArguments,KeyToNibbles.anyValues,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,keyCell,lengthCell,outCell]
  have cost:=KeyToNibbles.call_any_cost source key out length small (some none) convertArguments args installed
  rw [tail]
  exact Input.ClockCost.sequence_current source convert (.return result) (length/4+4) 0 cost (Input.ClockCost.returned source.code _)

/-- Every outcome of the original unsecured key helper is bounded, even
failed allocations, short clocks and unmapped converter reads or writes.
Only current scalar operands and the actual unsecured branch are needed. -/
theorem unsecured_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (m key : BitVec 64) (length : Nat)
    (small : length+4<2^64) (installed : Input.OriginalCode.Installed source.code)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 length))))
    (mapped : source.memaddrs (m+8#64)) (cell : source.memory (m+8#64)=.word 0#64) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤length/4+6 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [amount]=
      some (PersistentAlloc.values (BitVec.ofNat 64 (2*length))):=by
    simp [amount,PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,lengthCell,panOpHOL,
      valueIsWord,valueWord,BitVec.ofNat_mul]
  obtain ⟨callee,called,amountLocal⟩:=PersistentAlloc.environment source.code.lookup (BitVec.ofNat 64 (2*length))
    (PersistentAlloc.original_code source.code installed)
  have cost:=Input.ClockCost.scoped_reached_current source "nb2" .one (ofString "alloc") [amount] _ PersistentAlloc.body tail callee .one
    1 (length/4+4) args called (PersistentAlloc.body_price source.code installed (callEntryStateHOLFinite source callee) rfl) (by
      intro target returned normal checked
      have scalar : shapeEqHOL (shapeOfHOLExact returned) .one=true:=by simpa only [Bool.and_self] using checked
      have shape : shapeOfHOLExact returned=.one:=
        (shapeEqHOL_eq_true _ _).mp scalar
      obtain ⟨out,valueEq⟩:=Input.scalar_word_of_shape returned shape
      let ready:=Input.CallNormal.continuationEntry source target "nb2" returned
      have keyLocal : ready.locals.lookup (ofString "key")=some (.val (.word key)):=by
        simpa [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
          show ofString "nb2"≠ofString "key" from by decide] using keyCell
      have lengthLocal : ready.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 length))):=by
        simpa [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
          show ofString "nb2"≠ofString "klen" from by decide] using lengthCell
      have outLocal : ready.locals.lookup (ofString "nb2")=some (.val (.word out)):=by
        simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,valueEq]
      have codeEq:=(Input.evaluation_fields (callEntryStateHOLFinite source callee) target PersistentAlloc.body (some (.returned returned)) normal).2.2.2
      have readyInstalled : Input.OriginalCode.Installed ready.code:=by
        change Input.OriginalCode.Installed target.code
        rw [codeEq]
        exact installed
      exact tail_cost ready key out length small readyInstalled keyLocal lengthLocal outLocal)
  rw [unsecured_run source m mCell mapped cell,unsecured_shape]
  omega

end InitECandidate.Solver.Mpt.NibbleKey

#print axioms InitECandidate.Solver.Mpt.NibbleKey.tail_cost
#print axioms InitECandidate.Solver.Mpt.NibbleKey.unsecured_cost
