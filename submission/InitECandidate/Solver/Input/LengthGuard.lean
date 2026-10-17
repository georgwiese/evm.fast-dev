import InitECandidate.Solver.Input.LengthLoad

namespace InitECandidate.Solver.Input.Blob
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem oversized_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64)
    (localPresent : source.locals.lookup (ofString "len")=some (.val (.word length))) :
    eval source oversized=some (.val (.word (if 134217712<length.toNat then 1#64 else 0#64))) := by
  classical
  simp [eval,oversized,localVar,evalHOLExact,toExact,localPresent,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rfl

theorem guard_pass (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64)
    (localPresent : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (bounded : length.toNat≤Guest.maxInputBytes) : evaluateHOLFiniteState source guard=(none,source) := by
  have notOversized : ¬134217712<length.toNat := by change length.toNat≤134217712 at bounded; omega
  have condition := oversized_read source length localPresent
  simp only [notOversized,↓reduceIte] at condition
  simp only [eval] at condition
  rw [guard,evaluateHOLFiniteState_ite,condition]
  simp [evaluateHOLFiniteState_skip]

/-- The actual guest length declaration, host load and passing guard expose the
allocator/copy suffix, with no clock payment and exact lexical restoration. -/
theorem bounded_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (oracleEq : source.ffi.oracle=InitE.sourceOracle) (host : source.ffi.ffiState=Guest.guestHostMemory input)
    (domain : source.shMemaddrs=InitE.sharedDomain) (bounded : input.length%2^64≤Guest.maxInputBytes) :
    evaluateHOLFiniteState source body=
      (let output:=evaluateHOLFiniteState (lengthPost (WitnessRadix.QueryBranch.bind source "len" 0#64) input)
        afterGuard; (output.1,restore source "len" output.2)) := by
  let entered:=lengthPost (WitnessRadix.QueryBranch.bind source "len" 0#64) input
  have lenLocal : entered.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 input.length))) :=
    bind_lookup_same _ _ _
  have passed:=guard_pass entered (BitVec.ofNat 64 input.length) lenLocal bounded
  have sequence:=WitnessRadix.StateSteps.next_sequence entered entered guard afterGuard passed (Nat.le_refl _)
  rw [length_entry source input oracleEq host domain,sequence]

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.oversized_read
#print axioms InitECandidate.Solver.Input.Blob.guard_pass
#print axioms InitECandidate.Solver.Input.Blob.bounded_entry
