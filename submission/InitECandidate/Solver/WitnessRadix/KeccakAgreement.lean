import InitECandidate.Solver.WitnessRadix.ByteArrayAgreement
import InitECandidate.Solver.WitnessRadix.KeccakCall

namespace InitECandidate.Solver.WitnessRadix.Keccak
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 10000

/-- Retain the exact successful input read through the real permutation ABI.
Only the permutation's code entry is constrained. -/
theorem call_with_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arguments : List (ExpHOL 64)) (pointer : BitVec 64) (bytes : List (BitVec 8))
    (args : evalListHOLFinite source
      (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments = some (values pointer))
    (code : source.code.lookup (ofString "keccak_f1600") = some (formals, f1600Body, .one))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle)
    (readArray : readBytearrayWordHOL (byteWidth := 8) pointer 200
      (@panMemLoadByteWord8HOL 64 _ source.memory source.memaddrs
        (fun query => Classical.propDecidable (source.memaddrs query)) source.be) = some bytes)
    (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source
      (.call (some (none, none)) (ofString "keccak_f1600") arguments) =
      (none, { post source pointer bytes with clock := source.clock - 1 }) := by
  classical
  obtain ⟨callee, lookup, stpLocal⟩ := environment source.code.lookup pointer code
  let entry := callEntryStateHOLFinite source callee
  have bodyRun := f1600_execute entry pointer bytes stpLocal oracleEq readArray
  have callRun := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "keccak_f1600")
    arguments (values pointer) f1600Body callee .one (.val (.word 0#64))
    (emptyLocalsHOLFinite (post entry pointer bytes)) args lookup (by omega) bodyRun
    (by simp [shapeEqHOL, shapeOfHOLExact])
  exact callRun

theorem post_memory_agrees (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (domain : source.memaddrs = target.memaddrs) (endian : source.be = target.be)
    (region : BitVec 64 → Prop)
    (same : ∀ query, region query → source.memory query = target.memory query)
    (pointer : BitVec 64) (bytes : List (BitVec 8)) :
    ∀ query, region query →
      (post source pointer bytes).memory query = (post target pointer bytes).memory query :=
  by
    have agreement := ByteArray.write_of_cells source target domain endian region same pointer (answer bytes)
    exact agreement

theorem post_ffi_agrees (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (ffi : source.ffi = target.ffi) (pointer : BitVec 64) (bytes : List (BitVec 8)) :
    (post source pointer bytes).ffi = (post target pointer bytes).ffi :=
  congrArg (fun state => nextFfi state bytes) ffi

/-- Two actual calls read the same 200 bytes and perform the same observable
permutation when their state-buffer words agree. Private memory and all
unrelated code entries may differ. -/
theorem paired_call (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (sourceArguments targetArguments : List (ExpHOL 64)) (pointer : BitVec 64)
    (sourceArgs : evalListHOLFinite source
      (h := fun query => Classical.propDecidable (source.memaddrs query)) sourceArguments = some (values pointer))
    (targetArgs : evalListHOLFinite target
      (h := fun query => Classical.propDecidable (target.memaddrs query)) targetArguments = some (values pointer))
    (sourceCode : source.code.lookup (ofString "keccak_f1600") = some (formals, f1600Body, .one))
    (targetCode : target.code.lookup (ofString "keccak_f1600") = some (formals, f1600Body, .one))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle)
    (ffi : source.ffi = target.ffi)
    (domain : source.memaddrs = target.memaddrs) (endian : source.be = target.be)
    (region : BitVec 64 → Prop)
    (same : ∀ query, region query → source.memory query = target.memory query)
    (reads : ∀ offset < 200,
      region (panByteAlignHOL (width := 64) (byteAddress pointer offset)))
    (aligned : pointer.toNat % 8 = 0) (fits : pointer.toNat + 200 < 2^64)
    (mapped : ∀ word : Fin 25, source.memaddrs (byteAddress pointer (8 * word.val)))
    (sourceClock : 1 ≤ source.clock) (targetClock : 1 ≤ target.clock) :
    ∃ bytes : List (BitVec 8), bytes.length = 200 ∧
      evaluateHOLFiniteState source
        (.call (some (none, none)) (ofString "keccak_f1600") sourceArguments) =
        (none, { post source pointer bytes with clock := source.clock - 1 }) ∧
      evaluateHOLFiniteState target
        (.call (some (none, none)) (ofString "keccak_f1600") targetArguments) =
        (none, { post target pointer bytes with clock := target.clock - 1 }) ∧
      (post source pointer bytes).ffi = (post target pointer bytes).ffi ∧
      ∀ query, region query →
        (post source pointer bytes).memory query = (post target pointer bytes).memory query := by
  obtain ⟨bytes, sourceRead, length⟩ := ByteArray.read200 source pointer aligned fits mapped
  have equalRead := ByteArray.read_of_cells source target domain endian pointer 200
    (by intro offset inside; exact same _ (reads offset inside))
  have targetRead := equalRead.symm.trans sourceRead
  have targetOracle : target.ffi.oracle = InitE.sourceOracle := by rw [← ffi]; exact oracleEq
  exact ⟨bytes, length,
    call_with_read source sourceArguments pointer bytes sourceArgs sourceCode oracleEq sourceRead sourceClock,
    call_with_read target targetArguments pointer bytes targetArgs targetCode targetOracle targetRead targetClock,
    post_ffi_agrees source target ffi pointer bytes,
    post_memory_agrees source target domain endian region same pointer bytes⟩

end InitECandidate.Solver.WitnessRadix.Keccak

#print axioms InitECandidate.Solver.WitnessRadix.Keccak.call_with_read
#print axioms InitECandidate.Solver.WitnessRadix.Keccak.post_memory_agrees
#print axioms InitECandidate.Solver.WitnessRadix.Keccak.post_ffi_agrees
#print axioms InitECandidate.Solver.WitnessRadix.Keccak.paired_call
