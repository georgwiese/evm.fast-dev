import InitECandidate.Solver.Input.CopyTailReached
import InitECandidate.Solver.Input.HostLengthCurrent
import InitECandidate.Solver.WitnessRadix.AllocationCallNormal

namespace InitECandidate.Solver.Input.Blob
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Flapjack.Compiler.Encoders.Asm

/-- Actual successful copy image, allocation frontier and protected-word
frame. The caller must derive its entry heap invariant, not future room. -/
def Copied (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (input : Guest.InputBlob) (pointer : BitVec 64) (length : Nat) (returned : ValueHOL 64) : Prop :=
  pointer.toNat + length + 8 ≤ 2952790016 ∧
  returned = .rStruct [.val (.word pointer), .val (.word (BitVec.ofNat 64 length))] ∧
  InputBytes target input pointer length ∧
  target.clock = source.clock - (copyRounds length + 1) ∧
  target.globals = (WitnessRadix.PersistentAlloc.post source pointer (BitVec.ofNat 64 (length + 8))).globals ∧
  target.code = source.code ∧ target.memaddrs = source.memaddrs ∧
  target.shMemaddrs = source.shMemaddrs ∧
  target.ffi.ffiState = source.ffi.ffiState ∧ target.ffi.oracle = source.ffi.oracle ∧
  ∀ query, (∀ slot < copyRounds length, query ≠ pointer + BitVec.ofNat 64 (8 * slot)) →
    target.memory query = source.memory query

theorem after_guard_reached (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (input : Guest.InputBlob) (pointer : BitVec 64) (length : Nat) (returned : ValueHOL 64)
    (bounded : length ≤ Guest.maxInputBytes) (pointerBound : pointer.toNat ≤ 2952790016)
    (aligned : pointer.toNat % 8 = 0) (little : source.be = false)
    (installed : OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (limit : source.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle)
    (host : source.ffi.ffiState = Guest.guestHostMemory input)
    (normal : evaluateHOLFiniteState source afterGuard = (some (.returned returned), target)) :
    Copied source target input pointer length returned := by
  let amount := BitVec.ofNat 64 (length + 8)
  have amountNum : amount.toNat = length + 8 := by
    change (BitVec.ofNat 64 (length + 8)).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp [Guest.maxInputBytes] at bounded; omega)]
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [addConst (localVar "len") 8#64] = some (WitnessRadix.PersistentAlloc.values amount) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, addConst, localVar, limit,
      valueWord, valueIsWord, wordOpHOL, wordOp, WitnessRadix.PersistentAlloc.values, amount, BitVec.ofNat_add]
  rw [after_guard_tail_shape] at normal
  obtain ⟨room, positive, inner, tailRun, restored⟩ := WitnessRadix.PersistentAlloc.call_normal source target
    "p" _ copyTail pointer amount args (WitnessRadix.PersistentAlloc.original_code source.code installed)
    (Trap.original_code source.code installed) heap pointerBound returned normal
  have naturalRoom : pointer.toNat + length + 8 ≤ 2952790016 := by rw [amountNum] at room; omega
  let ready := bind (WitnessRadix.PersistentAlloc.post {source with clock := source.clock - 1} pointer amount) "p" pointer
  have readyP : ready.locals.lookup (ofString "p") = some (.val (.word pointer)) := bind_lookup_same _ _ _
  have readyL : ready.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))) :=
    (bind_lookup_other _ "p" "len" pointer (by decide)).trans limit
  have facts := copy_tail_reached ready inner input pointer length returned bounded (by omega)
    aligned little readyP readyL oracleEq host tailRun
  rw [restored]
  unfold Copied
  refine ⟨naturalRoom, facts.1, facts.2.1, ?_, facts.2.2.2⟩
  have clock := facts.2.2.1
  change inner.clock = source.clock - 1 - copyRounds length at clock
  change inner.clock = source.clock - (copyRounds length + 1)
  omega

theorem guard_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (limit : source.locals.lookup (ofString "len") = some (.val (.word word)))
    (normal : evaluateHOLFiniteState source guard = (none, target)) :
    target = source ∧ word.toNat ≤ Guest.maxInputBytes := by
  have read : eval source oversized =
      some (.val (.word (if 1073741808 < word.toNat then 1#64 else 0#64))) := by
    simp [eval, oversized, localVar, evalHOLExact, limit, wordCmpHOL, BitVec.lt_def]
  simp only [eval] at read
  rw [guard, evaluateHOLFiniteState_ite, read] at normal
  by_cases bad : 1073741808 < word.toNat
  · simp only [if_pos bad, show (1#64) ≠ 0 from by decide, ↓reduceIte] at normal
    have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
        [.const 8#64] = some (Trap.values 8#64) := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, Trap.values]
    exact (Trap.call_not_normal source target _ 8#64 (Trap.original_code source.code installed) args normal).elim
  · simp only [if_neg bad, ↓reduceIte, evaluateHOLFiniteState_skip] at normal
    exact ⟨(congrArg Prod.snd normal).symm, by dsimp [Guest.maxInputBytes]; omega⟩

/-- Complete actual input_blob return. The scalar length, passing guard,
allocation room, copied bytes and exact memory frame come from that execution.
Only the caller's current heap/oracle/endian invariants are entry assumptions. -/
theorem body_reached (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (input : Guest.InputBlob) (pointer : BitVec 64) (returned : ValueHOL 64)
    (pointerBound : pointer.toNat ≤ 2952790016) (aligned : pointer.toNat % 8 = 0)
    (little : source.be = false) (installed : OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle)
    (host : source.ffi.ffiState = Guest.guestHostMemory input)
    (normal : evaluateHOLFiniteState source body = (some (.returned returned), target)) :
    input.length % 2^64 ≤ Guest.maxInputBytes ∧
    Copied source target input pointer (input.length % 2^64) returned := by
  let ready := bind source "len" 0#64
  rw [body_shape] at normal
  obtain ⟨inner, actual, restored⟩ := declaration_return_word source target "len" (.const 0#64) 0#64
    (.seq loadLength (.seq guard afterGuard)) returned rfl normal
  have loadSummary := shared_load_local (ofString "i") (ofString "len") .opW (.const 1073741832#64)
    (by decide) ready
  obtain ⟨loaded, readRun, suffix⟩ := sequence_returned ready inner loadLength (.seq guard afterGuard)
    returned loadSummary.2.1 actual
  have same := SharedRead.normal_post ready loaded "len" (.const 1073741832#64) Guest.inputLenAddr 0#64
    rfl (bind_lookup_same _ _ _) oracleEq readRun
  have cell := CurrentHostLength.reached_word ready loaded input "len" (.const 1073741832#64) 0#64
    rfl (bind_lookup_same _ _ _) oracleEq host readRun
  have currentInstalled : OriginalCode.Installed loaded.code := by rw [same]; exact installed
  have guardSummary : LocalPrefix (ofString "len") guard :=
    .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip
  obtain ⟨guarded, guardRun, remaining, saved⟩ := guardSummary.normal_continue loaded inner afterGuard returned suffix
  obtain ⟨unchanged, bound⟩ := guard_normal loaded guarded (BitVec.ofNat 64 input.length) currentInstalled cell guardRun
  rw [unchanged] at remaining
  have lengthBound : input.length % 2^64 ≤ Guest.maxInputBytes := by
    rw [BitVec.toNat_ofNat] at bound
    exact bound
  have naturalCell : loaded.locals.lookup (ofString "len") =
      some (.val (.word (BitVec.ofNat 64 (input.length % 2^64)))) := by
    simpa only [← BitVec.toNat_ofNat input.length 64, BitVec.ofNat_toNat, BitVec.setWidth_eq] using cell
  have copied := after_guard_reached loaded inner input pointer (input.length % 2^64) returned
    lengthBound pointerBound aligned (by rw [same]; exact little) currentInstalled
    (by rw [same]; exact heap) naturalCell (by rw [same]; exact oracleEq) (by rw [same]; exact host) remaining
  refine ⟨lengthBound, ?_⟩
  rw [restored]
  rw [same] at copied
  exact copied

/-- A real returning input_blob caller reaches its actual continuation with
the derived pointer/length tuple and copied byte image. The extra caller tick
is explicit in the saved source clock. No callee return is supplied as a premise. -/
theorem call_reached (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (input : Guest.InputBlob) (pointer : BitVec 64) (name : String)
    (continuation : ProgHOL 64) (value : ValueHOL 64)
    (pointerBound : pointer.toNat ≤ 2952790016) (aligned : pointer.toNat % 8 = 0)
    (little : source.be = false) (installed : OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle)
    (host : source.ffi.ffiState = Guest.guestHostMemory input)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) returnShape (ofString "input_blob") [] continuation) =
      (some (.returned value), post)) :
    input.length % 2^64 ≤ Guest.maxInputBytes ∧ ∃ ready inner,
      ready.locals.lookup (ofString name) = some (.rStruct [.val (.word pointer),
        .val (.word (BitVec.ofNat 64 (input.length % 2^64)))]) ∧
      Copied {source with clock := source.clock - 1} ready input pointer (input.length % 2^64)
        (.rStruct [.val (.word pointer), .val (.word (BitVec.ofNat 64 (input.length % 2^64)))]) ∧
      evaluateHOLFiniteState ready continuation = (some (.returned value), inner) ∧
      post = restore source name inner := by
  obtain ⟨callee, called⟩ := environment source.code.lookup (original_code source.code installed)
  have positive := CallNormal.normal_clock source post _ returnShape (ofString "input_blob") [] continuation value normal
  obtain ⟨target, returned, actual⟩ := CallNormal.callee_return source post (ofString name) returnShape
    (ofString "input_blob") [] [] body continuation callee returnShape rfl called positive value normal
  obtain ⟨bound, copied⟩ := body_reached (callEntryStateHOLFinite source callee) target input pointer returned
    pointerBound aligned little installed heap oracleEq host actual
  have returnedEq := copied.2.1
  rw [returnedEq] at actual copied
  let pair : ValueHOL 64 := .rStruct [.val (.word pointer), .val (.word (BitVec.ofNat 64 (input.length % 2^64)))]
  let ready := CallNormal.continuationEntry source target name pair
  have resumed := CallNormal.return_execute source target name returnShape (ofString "input_blob") [] [] body continuation
    callee returnShape pair rfl called positive actual
    (by simp [pair, returnShape, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL])
  rw [resumed] at normal
  let output := evaluateHOLFiniteState ready continuation
  have resultEq : output.1 = some (.returned value) := congrArg Prod.fst normal
  have postEq : post = restore source name output.2 := (congrArg Prod.snd normal).symm
  refine ⟨bound, ready, output.2, ?_, copied, Prod.ext resultEq rfl, postEq⟩
  simp [ready, pair, CallNormal.continuationEntry, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.after_guard_reached
#print axioms InitECandidate.Solver.Input.Blob.guard_normal
#print axioms InitECandidate.Solver.Input.Blob.body_reached
#print axioms InitECandidate.Solver.Input.Blob.call_reached
