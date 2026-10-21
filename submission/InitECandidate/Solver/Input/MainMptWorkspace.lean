import InitECandidate.Solver.Input.MainKeccakWorkspace

namespace InitECandidate.Solver.Input.Main.MptWorkspace
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

inductive Field where | emptyRoot | emptyCode | nibbles | hash | key
  deriving DecidableEq

def Field.name : Field→MlS
  | .emptyRoot=>ofString "empty_trie_root" | .emptyCode=>ofString "empty_code_hash"
  | .nibbles=>ofString "mpt_nib_scratch" | .hash=>ofString "mpt_hash_scratch" | .key=>ofString "mpt_key_scratch"
def Field.pointer : Field→BitVec 64
  | .emptyRoot=>2713717456#64 | .emptyCode=>2713717488#64 | .nibbles=>2713717520#64 | .hash=>2713717584#64 | .key=>2713717624#64
def Field.bytes : Field→Nat
  | .emptyRoot=>32 | .emptyCode=>32 | .nibbles=>64 | .hash=>40 | .key=>16

theorem Field.not_heap (field : Field) : field.name≠ofString "heap_ptr" := by cases field <;> decide

theorem Field.geometry (field : Field) : AllocatedBytes.Arena field.pointer field.bytes ∧ field.pointer.toNat%8=0 ∧
    field.pointer.toNat+field.bytes≤inputPointer.toNat := by
  cases field <;> exact ⟨⟨by decide,by decide⟩,by decide,by decide⟩

def afterMptNames : List String :=
  ["heap_ptr","u256_ws","secp_accel_scratch","bn_gamma","bn_b2","bn_expw"] ++ BnAccelInitialization.symbols ++
  ["bls_c","bls_discount"] ++ BlsFpInitialization.symbols ++ BlsPairInitialization.symbols ++
  RipemdInitialization.symbols ++ BlakeInitialization.symbols ++ ["hdr_zero8"]

theorem header_from_mpt (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle)
    (key : MlS) (different : ∀ name ∈ afterMptNames,key ≠ ofString name) :
    (headerState middle).globals.lookup key = mptMiddle.globals.lookup key := by
  have heap := different "heap_ptr" (by simp [afterMptNames])
  have u256Other : (u256State mptMiddle).globals.lookup key = mptMiddle.globals.lookup key :=
    InitializerAllocations.template_other mptMiddle 2713717640 U256Initialization.actions key heap
      (by intro action member; simp only [U256Initialization.actions,List.mem_cons,List.not_mem_nil,or_false] at member; subst action; exact different "u256_ws" (by simp [afterMptNames]))
  have secpOther : (secpState mptMiddle).globals.lookup key = (u256State mptMiddle).globals.lookup key :=
    SecpInitialization.template_other (u256State mptMiddle) 2713718280 key heap (different "secp_accel_scratch" (by simp [afterMptNames]))
  have bnOther := BnInitialization.template_other (secpState mptMiddle) 2713718728 key heap
    (different "bn_gamma" (by simp [afterMptNames])) (different "bn_b2" (by simp [afterMptNames])) (different "bn_expw" (by simp [afterMptNames]))
    (by intro name member; exact different name (by simp [afterMptNames,member]))
  have blsOther : (blsState middle).globals.lookup key = middle.globals.lookup key :=
    BlsInitialization.template_other middle 2713719944 key heap (different "bls_discount" (by simp [afterMptNames])) (different "bls_c" (by simp [afterMptNames]))
      (by intro name member; exact different name (by simp [afterMptNames,member])) (by intro name member; exact different name (by simp [afterMptNames,member]))
  have ripemdOther : (ripemdState middle).globals.lookup key = (blsState middle).globals.lookup key :=
    RipemdInitialization.template_other (blsState middle) 2713729752 key heap (by intro name member; exact different name (by simp [afterMptNames,member]))
  have blakeOther : (blakeState middle).globals.lookup key = (ripemdState middle).globals.lookup key :=
    BlakeInitialization.template_other (ripemdState middle) 2713730208 key heap (by intro name member; exact different name (by simp [afterMptNames,member]))
  have headerOther : (headerState middle).globals.lookup key = (blakeState middle).globals.lookup key :=
    InitializerAllocations.template_other (blakeState middle) 2713730616 [HeaderInitialization.action] key heap
      (by intro action member; have same := List.mem_singleton.mp member; subst action; exact different "hdr_zero8" (by simp [afterMptNames]))
  have bnSame:=congrArg (fun state=>state.globals.lookup key) reached.control
  exact headerOther.trans (blakeOther.trans (ripemdOther.trans (blsOther.trans (bnSame.trans (bnOther.trans (secpOther.trans u256Other))))))

private def remainingNames := afterMptNames ++ EvmInitialization.symbols ++ ForkInitialization.symbols
open scoped InitE.MetadataComputation InitE.NameComputation in
private theorem fresh (field : Field) : remainingNames.all (fun name=>decide (field.name≠ofString name))=true := by
  cases field <;> decide_cbv
private theorem different (field : Field) (name : String) (member : name∈remainingNames) : field.name≠ofString name :=
  of_decide_eq_true (List.all_eq_true.mp (fresh field) name member)

theorem allocated_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (field : Field) :
    (MptInitialization.allocated source 2713717456).globals.lookup field.name=some (.val (.word field.pointer)) := by
  have layout:=MptInitialization.layout source 2713717456
  cases field
  · exact layout.root
  · exact layout.hash
  · exact layout.nibbles
  · exact layout.scratch
  · exact layout.key

/-- All five original MPT globals retain their real initializer allocations
through the remaining startup, with Keccak's observed event history. -/
theorem startup_value (input : Guest.InputBlob) (current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (history : StartupHistory input current) (field : Field) :
    current.globals.lookup field.name=some (.val (.word field.pointer)) := by
  obtain ⟨source,mptMiddle,bnMiddle,evmMiddle,entry,mpt,bn,evm,fork⟩ := history
  have forkLookup:=congrArg (fun state=>state.globals.lookup field.name) fork.control
  have forkOther:=ForkInitialization.template_other evmMiddle 2713730840 field.name field.not_heap
    (by intro name member; exact different field name (by simp [remainingNames,member]))
  have evmLookup:=congrArg (fun state=>state.globals.lookup field.name) evm.control
  have evmOther:=EvmInitialization.template_other (headerState bnMiddle) 2713730624 field.name field.not_heap
    (by intro name member; exact different field name (by simp [remainingNames,member]))
  have headerOther:=header_from_mpt source mptMiddle bnMiddle mpt bn field.name
    (by intro name member; exact different field name (by simp [remainingNames,member]))
  have mptLookup:=congrArg (fun state=>state.globals.lookup field.name) mpt.control
  exact forkLookup.trans (forkOther.trans (evmLookup.trans (evmOther.trans (headerOther.trans (mptLookup.trans (allocated_value (sszState source) field))))))

theorem after_hash_value (input : Guest.InputBlob) (before copiedSource origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (returned : RequestHash.Returned input origin current root) (field : Field) :
    current.globals.lookup field.name=some (.val (.word field.pointer)) :=
  (returned.globals field.name field.not_heap).trans ((actual.globals field.name field.not_heap).trans
    ((DecoderSetup.entered_other_global copiedSource input field.name field.not_heap).trans
      ((copied.other_global input before copiedSource field.name field.not_heap).trans (startup_value input before copied.history field))))

end InitECandidate.Solver.Input.Main.MptWorkspace

#print axioms InitECandidate.Solver.Input.Main.MptWorkspace.header_from_mpt
#print axioms InitECandidate.Solver.Input.Main.MptWorkspace.allocated_value
#print axioms InitECandidate.Solver.Input.Main.MptWorkspace.startup_value
#print axioms InitECandidate.Solver.Input.Main.MptWorkspace.after_hash_value
