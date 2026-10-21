import InitECandidate.Solver.Input.MainScratchArena

namespace InitECandidate.Solver.Input.Main.KeccakWorkspace
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

inductive Field where | state | pad
  deriving DecidableEq

def Field.name : Field→MlS
  | .state=>ofString "keccak_st" | .pad=>ofString "keccak_pad"
def Field.pointer : Field→BitVec 64
  | .state=>2713714976#64 | .pad=>2713715176#64

theorem Field.not_heap (field : Field) : field.name≠ofString "heap_ptr" := by cases field <;> decide

private def afterSszWrites := postSszNames ++ EvmInitialization.symbols ++ ForkInitialization.symbols
open scoped InitE.MetadataComputation InitE.NameComputation in
private theorem fresh (field : Field) : afterSszWrites.all (fun name=>decide (field.name≠ofString name))=true := by
  cases field <;> decide_cbv
private theorem different (field : Field) (name : String) (member : name∈afterSszWrites) : field.name≠ofString name :=
  of_decide_eq_true (List.all_eq_true.mp (fresh field) name member)

/-- Actual Keccak initializer bindings survive the real SSZ writes. -/
theorem ssz_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (field : Field) :
    (sszState source).globals.lookup field.name=some (.val (.word field.pointer)) := by
  have ssz:=SszInitialization.template_other (keccakState source) 2713715312 field.name field.not_heap
    (by cases field <;> decide) (by cases field <;> decide) (by cases field <;> decide)
  change (SszInitialization.template (keccakState source) 2713715312).globals.lookup field.name=_
  rw [ssz]
  cases field
  · exact (KeccakInitialization.template_bindings (shaState source) 2713714976).1
  · exact (KeccakInitialization.template_bindings (shaState source) 2713714976).2

/-- The unchanged remaining startup retains both actual hash pointers. -/
theorem startup_value (input : Guest.InputBlob) (current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (history : StartupHistory input current) (field : Field) :
    current.globals.lookup field.name=some (.val (.word field.pointer)) := by
  obtain ⟨source,mptMiddle,bnMiddle,evmMiddle,_,mpt,bn,evm,fork⟩ := history
  have forkLookup := congrArg (fun state=>state.globals.lookup field.name) fork.control
  have forkOther := ForkInitialization.template_other evmMiddle 2713730840 field.name field.not_heap
    (by intro name member; exact different field name (by simp [afterSszWrites,member]))
  have evmLookup := congrArg (fun state=>state.globals.lookup field.name) evm.control
  have evmOther := EvmInitialization.template_other (headerState bnMiddle) 2713730624 field.name field.not_heap
    (by intro name member; exact different field name (by simp [afterSszWrites,member]))
  have headerOther := header_from_ssz source mptMiddle bnMiddle mpt bn field.name
    (by intro name member; exact different field name (by simp [afterSszWrites,member]))
  exact forkLookup.trans (forkOther.trans (evmLookup.trans (evmOther.trans (headerOther.trans (ssz_value source field)))))

theorem copied_value (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (copied : InputCopied input source current) (field : Field) :
    current.globals.lookup field.name=some (.val (.word field.pointer)) :=
  (copied.other_global input source current field.name field.not_heap).trans (startup_value input source copied.history field)

theorem decoded_value (input : Guest.InputBlob) (before copiedSource current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) current) (field : Field) :
    current.globals.lookup field.name=some (.val (.word field.pointer)) :=
  (actual.globals field.name field.not_heap).trans ((DecoderSetup.entered_other_global copiedSource input field.name field.not_heap).trans
    (copied_value input before copiedSource copied field))

theorem after_hash_value (input : Guest.InputBlob) (before copiedSource origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (returned : RequestHash.Returned input origin current root) (field : Field) :
    current.globals.lookup field.name=some (.val (.word field.pointer)) :=
  (returned.globals field.name field.not_heap).trans (decoded_value input before copiedSource origin copied actual field)

/-- The genuine post-hash main state supplies the original Keccak runtime
context; the oracle function is retained through the real hash execution. -/
theorem after_hash_environment (input : Guest.InputBlob) (before copiedSource origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (returned : RequestHash.Returned input origin current root) :
    Keccak256.Environment current 2713714976#64 2713715176#64 := by
  have setup:=DecoderSetup.entered_context copiedSource input
  have setupOracle:=congrArg (fun state=>state.ffi.oracle) setup
  change (DecoderSetup.entered copiedSource input).ffi.oracle=copiedSource.ffi.oracle at setupOracle
  have oracle : current.ffi.oracle=InitE.sourceOracle :=
    returned.oracle.trans ((congrArg (fun ffi=>ffi.oracle) actual.ffi).trans (setupOracle.trans copied.oracle))
  exact Keccak256.original_environment current _ _ returned.workspace.sha.installed returned.workspace.sha.domain oracle
    (after_hash_value input before copiedSource origin current root copied actual returned .state)
    (after_hash_value input before copiedSource origin current root copied actual returned .pad)

end InitECandidate.Solver.Input.Main.KeccakWorkspace

#print axioms InitECandidate.Solver.Input.Main.KeccakWorkspace.ssz_value
#print axioms InitECandidate.Solver.Input.Main.KeccakWorkspace.startup_value
#print axioms InitECandidate.Solver.Input.Main.KeccakWorkspace.after_hash_value
#print axioms InitECandidate.Solver.Input.Main.KeccakWorkspace.after_hash_environment
