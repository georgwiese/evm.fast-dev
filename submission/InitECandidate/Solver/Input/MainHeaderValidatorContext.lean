import InitECandidate.Solver.Input.MainHeaderValidatorRows
import InitECandidate.Solver.Input.MainKeccakWorkspace
import InitECandidate.Solver.Headers.ValidateCallTrace

namespace InitECandidate.Solver.Input.Main.HeaderSlices
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Main's genuine copied/decoded/hashed state satisfies every physical
precondition of the unchanged validator, with one whole-input byte budget.
The SI row pointer/count cells remain the actual decoded cells. -/
theorem validator_context_after_hash (input : Guest.InputBlob) (before copiedSource origin current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root : BitVec 64) (counts : Nat→BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (prepared : RequestRootHashData.Prepared input origin root counts) (returned : RequestHash.Returned input origin current root) :
    ∃ headerArray,Headers.Validate.Context current (VarList.decodedArray headerArray (bytes input)) (PersistentAlloc.rounded root 32#64)
        (BitVec.ofNat 64 (count input)) 2713714688#64 2701135872#64 2713714976#64 2713715176#64
        (pointer input) (length input) inputPointer.toNat (PersistentAlloc.rounded root 32#64).toNat (input.length%2^64) ∧
      current.memory (byteAddress (RequestPrefix.cursor input) 72)=.word (VarList.decodedArray headerArray (bytes input)) ∧
      current.memory (byteAddress (RequestPrefix.cursor input) 80)=.word (BitVec.ofNat 64 (count input)) := by
  obtain ⟨small,arena,headerArray,rows,pointerCell,countCell,budget⟩ := validator_rows_after_hash input before copiedSource origin current root counts copied actual bounded prepared returned
  have number : (BitVec.ofNat 64 (count input)).toNat=count input := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have environment:=KeccakWorkspace.after_hash_environment input before copiedSource origin current root copied actual returned
  have setup:=DecoderSetup.entered_context copiedSource input
  have setupExceptions:=congrArg PanSemStateFiniteExact.eshapes setup
  change (DecoderSetup.entered copiedSource input).eshapes=copiedSource.eshapes at setupExceptions
  have shape : current.eshapes.lookup (ofString "HdrErr")=some .one := by
    rw [returned.exceptions,actual.exceptions,setupExceptions]
    exact copied.shapes .HdrErr
  have guards:=PersistentAlloc.guards root 32#64 prepared.output.arena.upper
  have lower : 2701131776≤(PersistentAlloc.rounded root 32#64).toNat := by
    have h:=prepared.output.arena.lower
    have after:=prepared.before
    omega
  refine ⟨headerArray,⟨returned.workspace.sha.installed,shape,arena,environment,?_,returned.heap,lower,
    guards.2.2.2.1,guards.2.2.2.2,Nat.le_refl _,⟨by decide,by decide⟩,by decide,⟨by decide,by decide⟩,by decide,
    by decide,by decide,by decide,by decide,by decide,?_⟩,pointerCell,countCell⟩
  · simpa only [number] using rows
  · simpa only [number] using (show VarList.sumPrefix (fun index=>(length input index).toNat) (count input)≤input.length%2^64 by omega)

end InitECandidate.Solver.Input.Main.HeaderSlices

#print axioms InitECandidate.Solver.Input.Main.HeaderSlices.validator_context_after_hash
