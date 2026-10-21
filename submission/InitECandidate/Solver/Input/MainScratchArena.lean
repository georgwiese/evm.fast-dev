import InitECandidate.Solver.Input.MainCryptoWorkspace
import InitECandidate.Solver.Input.MainRequestRootHashTrace
import InitECandidate.Solver.Rlp.ValidationArena

namespace InitECandidate.Solver.Input.Main.ScratchArena
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

inductive Field where | scratch | frame
  deriving DecidableEq

def Field.name : Field→MlS
  | .scratch=>ofString "scratch_ptr" | .frame=>ofString "frame_mem_ptr"
def Field.pointer : Field→BitVec 64
  | .scratch=>2713714688#64 | .frame=>2701135872#64

theorem Field.not_heap (field : Field) : field.name≠ofString "heap_ptr" := by cases field <;> decide

private def afterSszWrites := postSszNames ++ EvmInitialization.symbols ++ ForkInitialization.symbols
open scoped InitE.MetadataComputation InitE.NameComputation in
private theorem fresh (field : Field) : afterSszWrites.all (fun name=>decide (field.name≠ofString name))=true := by
  cases field <;> decide_cbv
private theorem different (field : Field) (name : String) (member : name∈afterSszWrites) : field.name≠ofString name :=
  of_decide_eq_true (List.all_eq_true.mp (fresh field) name member)

/-- Both real downward/upward temporary cursors retain mem_init's values
through the original SHA, Keccak and SSZ initialization. -/
theorem ssz_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (field : Field) :
    (sszState source).globals.lookup field.name=some (.val (.word field.pointer)) := by
  have ssz := SszInitialization.template_other (keccakState source) 2713715312 field.name field.not_heap
    (by cases field <;> decide) (by cases field <;> decide) (by cases field <;> decide)
  have keccak := KeccakInitialization.template_other (shaState source) 2713714976 field.name field.not_heap
    (by cases field <;> decide) (by cases field <;> decide)
  have sha := ShaInitialization.template_other (memoryState source) 2713714688 field.name field.not_heap
    (by cases field <;> decide) (by cases field <;> decide) (by cases field <;> decide)
  change (SszInitialization.template (keccakState source) 2713715312).globals.lookup field.name=_
  rw [ssz]
  change (KeccakInitialization.template (shaState source) 2713714976).globals.lookup field.name=_
  rw [keccak]
  change (ShaInitialization.template (memoryState source) 2713714688).globals.lookup field.name=_
  rw [sha]
  cases field
  · exact (memory_globals source).2.1
  · exact (memory_globals source).2.2

/-- Original remaining startup preserves both temporary cursors. No arena
address is substituted for a current runtime global. -/
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

/-- At the actual post-hash main continuation, RLP's original scratch arena
is below the copied input. Its existing upper memory frame therefore applies. -/
theorem after_hash_arena (input : Guest.InputBlob) (before copiedSource origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (returned : RequestHash.Returned input origin current root) :
    Rlp.Validation.Arena current 2713714688#64 2701135872#64 ∧ (2713714688#64 : BitVec 64).toNat≤inputPointer.toNat := by
  have callerDomain := congrArg PanSemStateFiniteExact.memaddrs (DecoderSetup.entered_context copiedSource input)
  refine ⟨⟨returned.domain.trans (actual.domain.trans (callerDomain.trans copied.domain)),
    after_hash_value input before copiedSource origin current root copied actual returned .scratch,
    after_hash_value input before copiedSource origin current root copied actual returned .frame,
    by decide,by decide,by decide,by decide⟩,by decide⟩

end InitECandidate.Solver.Input.Main.ScratchArena

#print axioms InitECandidate.Solver.Input.Main.ScratchArena.Field.not_heap
#print axioms InitECandidate.Solver.Input.Main.ScratchArena.ssz_value
#print axioms InitECandidate.Solver.Input.Main.ScratchArena.startup_value
#print axioms InitECandidate.Solver.Input.Main.ScratchArena.copied_value
#print axioms InitECandidate.Solver.Input.Main.ScratchArena.decoded_value
#print axioms InitECandidate.Solver.Input.Main.ScratchArena.after_hash_value
#print axioms InitECandidate.Solver.Input.Main.ScratchArena.after_hash_arena
