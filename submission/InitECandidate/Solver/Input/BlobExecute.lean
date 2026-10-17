import InitECandidate.Solver.Input.CopyScopes
import InitECandidate.Solver.Input.LengthGuard
import InitECandidate.Solver.WitnessRadix.AllocationCall

namespace InitECandidate.Solver.Input.Blob
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete literal input_blob on the passing size/allocation path. The input
list is arbitrary: only its encoded length is checked, exactly as in the guest.
All host reads and heap stores follow from the challenge's real domains. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (lower : 2701131776≤pointer.toNat) (upper : pointer.toNat+input.length%2^64+8≤33806089496)
    (aligned : pointer.toNat%8=0)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (oracleEq : source.ffi.oracle=InitE.sourceOracle) (host : source.ffi.ffiState=Guest.guestHostMemory input)
    (ordinary : source.memaddrs=InitE.ordinaryDomain) (shared : source.shMemaddrs=InitE.sharedDomain)
    (enough : copyRounds (input.length%2^64)+1≤source.clock) :
    ∃ target : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source body=(some (.returned (pair pointer (input.length%2^64))),target) ∧
      target.clock=source.clock-(copyRounds (input.length%2^64)+1) ∧
      target.globals=(WitnessRadix.PersistentAlloc.post source pointer (BitVec.ofNat 64 (input.length%2^64+8))).globals ∧
      target.ffi.ffiState=source.ffi.ffiState ∧ target.ffi.oracle=source.ffi.oracle := by
  classical
  let length:=input.length%2^64
  have lengthBound : length≤134217712 := bounded
  have clockEnough : copyRounds length+1≤source.clock := enough
  have lengthWord : BitVec.ofNat 64 input.length=BitVec.ofNat 64 length := by
    apply BitVec.eq_of_toNat_eq
    simp [length,BitVec.toNat_ofNat,Nat.mod_mod]
  let loaded:=lengthPost (WitnessRadix.QueryBranch.bind source "len" 0#64) input
  let allocated:=WitnessRadix.PersistentAlloc.post {loaded with clock:=loaded.clock-1} pointer (BitVec.ofNat 64 (length+8))
  let entered:=WitnessRadix.QueryBranch.bind allocated "p" pointer
  have loadedLen : loaded.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))) := by
    rw [←lengthWord]
    exact bind_lookup_same _ _ _
  have args : evalListHOLFinite loaded (h:=fun address=>Classical.propDecidable (loaded.memaddrs address))
      [addConst (localVar "len") 8#64]=some (WitnessRadix.PersistentAlloc.values (BitVec.ofNat 64 (length+8))) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,addConst,localVar,loadedLen,
      valueIsWord,valueWord,wordOpHOL,wordOp,WitnessRadix.PersistentAlloc.values,BitVec.ofNat_add]
  have allocation:=WitnessRadix.PersistentAlloc.call_execute loaded "p" [addConst (localVar "len") 8#64]
    copySuffix pointer (BitVec.ofNat 64 (length+8)) args allocCode heapGlobal
    (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]; exact upper) (by change 1≤source.clock; omega)
  have enteredLen : entered.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))) := by
    rw [bind_lookup_other allocated "p" "len" pointer (by decide)]
    exact loadedLen
  obtain ⟨target,run,frame⟩:=copy_scopes entered input pointer length bounded lower upper aligned
    (bind_lookup_same _ _ _) enteredLen oracleEq host ordinary shared (by change copyRounds length≤source.clock-1; omega)
  rw [run] at allocation
  have allocationRun : evaluateHOLFiniteState loaded afterGuard=
      (some (.returned (pair pointer length)),restore loaded "p" target) := by
    rw [after_guard_shape]
    exact allocation
  have entry:=bounded_entry source input oracleEq host shared bounded
  rw [allocationRun] at entry
  let result:=restore source "len" (restore loaded "p" target)
  have targetClock:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.clock) frame
  have targetGlobals:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals) frame
  have targetHost:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.ffi.ffiState) frame
  have targetOracle:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.ffi.oracle) frame
  have fields:=walk_frame (copyEntry entered) pointer 0 (copyRounds length)
  refine ⟨result,entry,?_,?_,?_,?_⟩
  · change target.clock=source.clock-(copyRounds length+1)
    change target.clock=(walk (copyEntry entered) pointer 0 (copyRounds length)).clock at targetClock
    rw [targetClock,walk_clock]
    change source.clock-1-copyRounds length=source.clock-(copyRounds length+1)
    omega
  · change target.globals=_
    change target.globals=(walk (copyEntry entered) pointer 0 (copyRounds length)).globals at targetGlobals
    rw [targetGlobals,fields.1]
    rfl
  · change target.ffi.ffiState=source.ffi.ffiState
    change target.ffi.ffiState=(walk (copyEntry entered) pointer 0 (copyRounds length)).ffi.ffiState at targetHost
    rw [targetHost,fields.2.2.2.2.1]
    rfl
  · change target.ffi.oracle=source.ffi.oracle
    change target.ffi.oracle=(walk (copyEntry entered) pointer 0 (copyRounds length)).ffi.oracle at targetOracle
    rw [targetOracle,fields.2.2.2.2.2]
    rfl

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.execute
