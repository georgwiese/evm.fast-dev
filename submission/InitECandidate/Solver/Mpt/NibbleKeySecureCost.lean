import InitECandidate.Solver.Mpt.NibbleKeySecureNormal
import InitECandidate.Solver.Mpt.NibbleKeyCost
import InitECandidate.Solver.WitnessRadix.AllocationGlobals
import InitECandidate.Solver.Input.ClockCostSequenceReached

namespace InitECandidate.Solver.Mpt.NibbleKey
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem secure_tail_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (hash out : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (hashCell : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hash)))
    (outCell : source.locals.lookup (ofString "nb")=some (.val (.word out))) :
    source.clock-(evaluateHOLFiniteState source secureTail).2.clock≤12 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) secureConvertArguments=some (KeyToNibbles.anyValues hash 32#64 out):=by
    simp [secureConvertArguments,KeyToNibbles.anyValues,evalListHOLFinite,evalListHOLExact,localVar,evalHOLExact,toExact,hashCell,outCell]
  have cost:=KeyToNibbles.call_any_cost source hash out 32 (by decide) (some none) secureConvertArguments args installed
  rw [secure_shapes.2.2]
  exact Input.ClockCost.sequence_current source secureConvert (.return secureResult) 12 0 cost (Input.ClockCost.returned source.code secureResult)

/-- All allocator outcomes, including traps. Only an actual allocator
return derives the scalar and retained global used by the converter. -/
theorem secure_allocation_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (hash : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (hashCell : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hash))) :
    source.clock-(evaluateHOLFiniteState source secureAllocation).2.clock≤14 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [.const 64#64]=some (PersistentAlloc.values 64#64):=rfl
  obtain ⟨callee,called,_amountLocal⟩:=PersistentAlloc.environment source.code.lookup 64#64 (PersistentAlloc.original_code source.code installed)
  have back (target : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
      (normal : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) PersistentAlloc.body=(some (.returned returned),target))
      (checked : (shapeEqHOL (shapeOfHOLExact returned) .one && shapeEqHOL (shapeOfHOLExact returned) .one)=true) :
      target.clock-(evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target "nb" returned) secureTail).2.clock≤12:=by
    have scalar : shapeEqHOL (shapeOfHOLExact returned) .one=true:=by simpa only [Bool.and_self] using checked
    have shape : shapeOfHOLExact returned=.one:=(shapeEqHOL_eq_true _ _).mp scalar
    obtain ⟨out,valueEq⟩:=Input.RlpWrite.U256Value.scalar_word returned shape
    let ready:=Input.CallNormal.continuationEntry source target "nb" returned
    have globalFrame:=PersistentAlloc.globals (ofString "mpt_hash_scratch") source.code installed (by decide) (callEntryStateHOLFinite source callee) rfl
    rw [normal] at globalFrame
    have globalLookup:=congrArg Prod.snd globalFrame
    change target.globals.lookup (ofString "mpt_hash_scratch")=source.globals.lookup (ofString "mpt_hash_scratch") at globalLookup
    have currentHash : ready.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hash)):=globalLookup.trans hashCell
    have currentOut : ready.locals.lookup (ofString "nb")=some (.val (.word out)):=by
      simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,valueEq]
    have codeEq:=(Input.evaluation_fields (callEntryStateHOLFinite source callee) target PersistentAlloc.body (some (.returned returned)) normal).2.2.2
    have currentInstalled : Input.OriginalCode.Installed ready.code:=by change Input.OriginalCode.Installed target.code; rw [codeEq]; exact installed
    exact secure_tail_cost ready hash out currentInstalled currentHash currentOut
  rw [secure_shapes.2.1]
  exact Input.ClockCost.scoped_reached_current source "nb" .one (ofString "alloc") [.const 64#64] _ PersistentAlloc.body secureTail callee .one 1 12 args called
    (PersistentAlloc.body_price source.code installed (callEntryStateHOLFinite source callee) rfl) back

/-- Every outcome of the whole original secure helper. Hashing uses
its current real mapping/oracle context; a normal hash return alone
supplies the retained hash scratch global at the allocation suffix. -/
theorem secured_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (m flag key stp pad hash : BitVec 64) (length : Nat)
    (small : length+136<2^64) (installed : Input.OriginalCode.Installed source.code)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 length))))
    (mapped : source.memaddrs (m+8#64)) (cell : source.memory (m+8#64)=.word flag) (nonzero : flag≠0#64)
    (hashCell : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hash)))
    (data : Keccak256.EntryData source stp key pad hash length) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤Keccak256.price length+15 := by
  have args:=secure_hash_arguments source key hash length keyCell lengthCell hashCell
  have front:=Keccak256.call_cost source hashArguments (some none) stp key pad hash length args (Keccak256.original_code source.code installed) data small
  have back (target : PanSemStateFiniteExact 64 Guest.HostMemory) (normal : evaluateHOLFiniteState source hashCall=(none,target)) :
      target.clock-(evaluateHOLFiniteState target secureAllocation).2.clock≤14:=by
    obtain ⟨_locals,_upper,_lower,control,_memory⟩:=Keccak256.call_normal source target hashArguments stp key pad hash length args (Keccak256.original_code source.code installed) data small normal
    have globals : target.globals=source.globals:=by have projected:=congrArg PanSemStateFiniteExact.globals control; exact projected
    have codeEq : target.code=source.code:=by have projected:=congrArg PanSemStateFiniteExact.code control; exact projected
    exact secure_allocation_cost target hash (by rw [codeEq]; exact installed) (by rw [globals]; exact hashCell)
  rw [secured_run source m flag mCell mapped cell nonzero,secure_shapes.1]
  exact Input.ClockCost.sequence_reached_current source hashCall secureAllocation (Keccak256.price length+1) 14 front back

end InitECandidate.Solver.Mpt.NibbleKey

#print axioms InitECandidate.Solver.Mpt.NibbleKey.secure_tail_cost
#print axioms InitECandidate.Solver.Mpt.NibbleKey.secure_allocation_cost
#print axioms InitECandidate.Solver.Mpt.NibbleKey.secured_cost
