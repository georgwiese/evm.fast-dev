import InitECandidate.Solver.Input.BlobProgram

namespace InitECandidate.Solver.Input.Blob
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem length_mapped : InitE.sharedDomain Guest.inputLenAddr := by
  refine ⟨?_, Or.inl (by decide)⟩
  change holAligned (holLOG2 8) Guest.inputLenAddr=true
  rw [holLOG2_eq_log2 (by decide)]
  change holAligned 3 Guest.inputLenAddr=true
  rw [holAligned_iff]
  decide

def lengthPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  {WitnessRadix.QueryBranch.bind source "len" (BitVec.ofNat 64 input.length) with
    ffi := SharedRead.nextFfi source.ffi Guest.inputLenAddr}

/-- The literal guest load returns the low 64 bits of the mathematical list
length. Neither a size bound nor a decoding assumption is used. -/
theorem load_length (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (old : BitVec 64)
    (localPresent : source.locals.lookup (ofString "len")=some (.val (.word old)))
    (oracleEq : source.ffi.oracle=InitE.sourceOracle) (host : source.ffi.ffiState=Guest.guestHostMemory input)
    (domain : source.shMemaddrs=InitE.sharedDomain) :
    evaluateHOLFiniteState source loadLength=(none,lengthPost source input) := by
  have mapped : source.shMemaddrs Guest.inputLenAddr := by rw [domain]; exact length_mapped
  have present := HostLength.present input
  rw [←host] at present
  have run := SharedRead.execute source "len" (.const 1073741832#64) Guest.inputLenAddr old rfl
    localPresent oracleEq mapped present
  simpa only [loadLength,SharedRead.post,host,HostLength.bytes,WordCodec.guest_roundtrip,lengthPost] using run

/-- Expose the actual post-load continuation, retaining the len declaration's
lexical restoration and the unchanged source clock. -/
theorem length_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (oracleEq : source.ffi.oracle=InitE.sourceOracle) (host : source.ffi.ffiState=Guest.guestHostMemory input)
    (domain : source.shMemaddrs=InitE.sharedDomain) :
    evaluateHOLFiniteState source body=
      (let output:=evaluateHOLFiniteState (lengthPost (WitnessRadix.QueryBranch.bind source "len" 0#64) input)
        (.seq guard afterGuard); (output.1,restore source "len" output.2)) := by
  let entered:=WitnessRadix.QueryBranch.bind source "len" 0#64
  have setup : WitnessRadix.BuildEntry.Initializes source [("len",.const 0#64)] entered
      (fun output=>restore source "len" output) := .step 0#64 rfl (.done _)
  have run := load_length entered input 0#64 (WitnessRadix.QueryBranch.bind_lookup_same _ _ _) oracleEq host domain
  have sequence := WitnessRadix.StateSteps.next_sequence entered (lengthPost entered input)
    loadLength (.seq guard afterGuard) run (Nat.le_refl _)
  have scopeRun:=WitnessRadix.BuildEntry.declarations_execute setup (.seq loadLength (.seq guard afterGuard))
  rw [sequence] at scopeRun
  rw [body_shape]
  exact scopeRun

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.length_mapped
#print axioms InitECandidate.Solver.Input.Blob.load_length
#print axioms InitECandidate.Solver.Input.Blob.length_entry
