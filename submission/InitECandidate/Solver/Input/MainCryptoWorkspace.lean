import InitECandidate.Solver.Input.MainRootHashEntry
import InitECandidate.Solver.Input.MainSszWorkspace

namespace InitECandidate.Solver.Input.Main.CryptoWorkspace
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

inductive Field where | shaState | shaPadding | shaAccel | lengthChunk | offsets | zeroHashes
  deriving DecidableEq

def Field.name : Field→MlS
  | .shaState=>ofString "sha_st" | .shaPadding=>ofString "sha_pad" | .shaAccel=>ofString "sha_accel"
  | .lengthChunk=>ofString "ssz_len_chunk" | .offsets=>ofString "ssz_offs" | .zeroHashes=>ofString "zero_hashes"
def Field.pointer : Field→Nat
  | .shaState=>2713714688 | .shaPadding=>2713714752 | .shaAccel=>2713714880
  | .lengthChunk=>2713715312 | .offsets=>2713715344 | .zeroHashes=>2713715408
def Field.bytes : Field→Nat
  | .shaState=>64 | .shaPadding=>128 | .shaAccel=>96 | .lengthChunk=>32 | .offsets=>64 | .zeroHashes=>2048

theorem Field.not_heap (field : Field) : field.name≠ofString "heap_ptr" := by cases field <;> decide

theorem Field.geometry (field : Field) : AllocatedBytes.Arena (BitVec.ofNat 64 field.pointer) field.bytes ∧
    (BitVec.ofNat 64 field.pointer).toNat%8=0 ∧ (BitVec.ofNat 64 field.pointer).toNat+field.bytes≤inputPointer.toNat := by
  cases field <;> exact ⟨⟨by decide,by decide⟩,by decide,by decide⟩

private def afterSszWrites := postSszNames ++ EvmInitialization.symbols ++ ForkInitialization.symbols
open scoped InitE.MetadataComputation InitE.NameComputation in
private theorem fresh (field : Field) : afterSszWrites.all (fun name=>decide (field.name≠ofString name))=true := by
  cases field <;> decide_cbv
private theorem different (field : Field) (name : String) (member : name∈afterSszWrites) : field.name≠ofString name :=
  of_decide_eq_true (List.all_eq_true.mp (fresh field) name member)

theorem ssz_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (field : Field) :
    (sszState source).globals.lookup field.name=some (.val (.word (BitVec.ofNat 64 field.pointer))) := by
  cases field
  case shaState=>
    have ssz := SszInitialization.template_other (keccakState source) 2713715312 (ofString "sha_st") (by decide) (by decide) (by decide) (by decide)
    have keccak := KeccakInitialization.template_other (shaState source) 2713714976 (ofString "sha_st") (by decide) (by decide) (by decide)
    change (SszInitialization.template (keccakState source) 2713715312).globals.lookup (ofString "sha_st")=_
    rw [ssz]
    change (KeccakInitialization.template (shaState source) 2713714976).globals.lookup (ofString "sha_st")=_
    rw [keccak]
    simp [shaState,ShaInitialization.template,ShaInitialization.step,putGlobal,HolFiniteMapExact.update,FUPDATE,Field.pointer,show ofString "sha_accel"≠ofString "sha_st" from by decide,show ofString "heap_ptr"≠ofString "sha_st" from by decide,show ofString "sha_pad"≠ofString "sha_st" from by decide]
  case shaPadding=>
    have ssz := SszInitialization.template_other (keccakState source) 2713715312 (ofString "sha_pad") (by decide) (by decide) (by decide) (by decide)
    have keccak := KeccakInitialization.template_other (shaState source) 2713714976 (ofString "sha_pad") (by decide) (by decide) (by decide)
    change (SszInitialization.template (keccakState source) 2713715312).globals.lookup (ofString "sha_pad")=_
    rw [ssz]
    change (KeccakInitialization.template (shaState source) 2713714976).globals.lookup (ofString "sha_pad")=_
    rw [keccak]
    simp [shaState,ShaInitialization.template,ShaInitialization.step,putGlobal,HolFiniteMapExact.update,FUPDATE,Field.pointer,show ofString "sha_accel"≠ofString "sha_pad" from by decide,show ofString "heap_ptr"≠ofString "sha_pad" from by decide]
  case shaAccel=>
    have ssz := SszInitialization.template_other (keccakState source) 2713715312 (ofString "sha_accel") (by decide) (by decide) (by decide) (by decide)
    have keccak := KeccakInitialization.template_other (shaState source) 2713714976 (ofString "sha_accel") (by decide) (by decide) (by decide)
    change (SszInitialization.template (keccakState source) 2713715312).globals.lookup (ofString "sha_accel")=_
    rw [ssz]
    change (KeccakInitialization.template (shaState source) 2713714976).globals.lookup (ofString "sha_accel")=_
    rw [keccak]
    simp [shaState,ShaInitialization.template,ShaInitialization.step,putGlobal,HolFiniteMapExact.update,FUPDATE,Field.pointer]
  case lengthChunk=>
    simp [sszState,Field.name,Field.pointer,SszInitialization.template,SszInitialization.allocated,InitializerWords.written,
      InitializerAllocations.template,InitializerAllocations.reserve,SszInitialization.actions,InitializerAllocations.constant,putGlobal,HolFiniteMapExact.update,FUPDATE,show ofString "zero_hashes"≠ofString "ssz_len_chunk" from by decide,show ofString "heap_ptr"≠ofString "ssz_len_chunk" from by decide,show ofString "ssz_offs"≠ofString "ssz_len_chunk" from by decide]
  case offsets=>
    simp [sszState,Field.name,Field.pointer,SszInitialization.template,SszInitialization.allocated,InitializerWords.written,
      InitializerAllocations.template,InitializerAllocations.reserve,SszInitialization.actions,InitializerAllocations.constant,putGlobal,HolFiniteMapExact.update,FUPDATE,show ofString "zero_hashes"≠ofString "ssz_offs" from by decide,show ofString "heap_ptr"≠ofString "ssz_offs" from by decide]
  case zeroHashes=>
    simp [sszState,Field.name,Field.pointer,SszInitialization.template,SszInitialization.allocated,InitializerWords.written,
      InitializerAllocations.template,InitializerAllocations.reserve,SszInitialization.actions,InitializerAllocations.constant,putGlobal,HolFiniteMapExact.update,FUPDATE]

private theorem globals_of_hash (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl source) : target.globals=source.globals := congrArg (fun state=>state.globals) same

/-- All six original initialized crypto/SSZ pointers survive the actual
remaining startup, derived from its retained concrete provenance. -/
theorem startup_value (input : Guest.InputBlob) (current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (history : StartupHistory input current) (field : Field) :
    current.globals.lookup field.name=some (.val (.word (BitVec.ofNat 64 field.pointer))) := by
  obtain ⟨source,mptMiddle,bnMiddle,evmMiddle,_,mpt,bn,evm,fork⟩ := history
  have forkLookup := congrArg (fun globals : HolFiniteMapExact MlS (ValueHOL 64)=>globals.lookup field.name) (globals_of_hash _ current fork.control)
  have forkOther := ForkInitialization.template_other evmMiddle 2713730840 field.name field.not_heap
    (by intro name member; exact different field name (by simp [afterSszWrites,member]))
  have evmLookup := congrArg (fun globals : HolFiniteMapExact MlS (ValueHOL 64)=>globals.lookup field.name) (globals_of_hash _ evmMiddle evm.control)
  have evmOther := EvmInitialization.template_other (headerState bnMiddle) 2713730624 field.name field.not_heap
    (by intro name member; exact different field name (by simp [afterSszWrites,member]))
  have headerOther := header_from_ssz source mptMiddle bnMiddle mpt bn field.name
    (by intro name member; exact different field name (by simp [afterSszWrites,member]))
  exact forkLookup.trans (forkOther.trans (evmLookup.trans (evmOther.trans (headerOther.trans (ssz_value source field)))))

theorem copied_value (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (copied : InputCopied input source current) (field : Field) :
    current.globals.lookup field.name=some (.val (.word (BitVec.ofNat 64 field.pointer))) :=
  (copied.other_global input source current field.name field.not_heap).trans (startup_value input source copied.history field)

/-- The same actual original main decoder return retains every initialized
workspace address, with arena/alignment facts provided independently above. -/
theorem decoded_value (input : Guest.InputBlob) (before copiedSource current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (copied : InputCopied input before copiedSource) (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) current) (field : Field) :
    current.globals.lookup field.name=some (.val (.word (BitVec.ofNat 64 field.pointer))) :=
  (actual.globals field.name field.not_heap).trans ((DecoderSetup.entered_other_global copiedSource input field.name field.not_heap).trans
    (copied_value input before copiedSource copied field))

theorem hashing_value (input : Guest.InputBlob) (before copiedSource current : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (copied : InputCopied input before copiedSource) (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) current) (field : Field) :
    (RequestHash.entered current root).globals.lookup field.name=some (.val (.word (BitVec.ofNat 64 field.pointer))) := by
  have same : (RequestHash.entered current root).globals.lookup field.name=current.globals.lookup field.name := by
    simp [RequestHash.entered,WitnessRadix.QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm field.not_heap]
  exact same.trans (decoded_value input before copiedSource current copied actual field)

end InitECandidate.Solver.Input.Main.CryptoWorkspace

#print axioms InitECandidate.Solver.Input.Main.CryptoWorkspace.Field.geometry
#print axioms InitECandidate.Solver.Input.Main.CryptoWorkspace.ssz_value
#print axioms InitECandidate.Solver.Input.Main.CryptoWorkspace.startup_value
#print axioms InitECandidate.Solver.Input.Main.CryptoWorkspace.copied_value
#print axioms InitECandidate.Solver.Input.Main.CryptoWorkspace.decoded_value
#print axioms InitECandidate.Solver.Input.Main.CryptoWorkspace.hashing_value
