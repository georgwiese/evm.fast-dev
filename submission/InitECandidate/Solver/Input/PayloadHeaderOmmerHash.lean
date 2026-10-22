import InitECandidate.Solver.Input.PayloadHeaderOmmerMarker
import InitECandidate.Solver.WitnessRadix.Keccak256CurrentCall
import InitECandidate.Solver.WitnessRadix.Keccak256EnvironmentFields

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main Main.RunAttemptConstructors

structure OmmerLayout (heap : BitVec 64) : Prop where
  headerArena : AllocatedBytes.Arena heap 248
  headerAligned : heap.toNat%8=0
  ommerArena : AllocatedBytes.Arena (ommerBase heap) 32
  temporaryArena : AllocatedBytes.Arena (temporaryBase heap) 8
  ommerAligned : (ommerBase heap).toNat%8=0
  temporaryAligned : (temporaryBase heap).toNat%8=0
  headerBefore : heap.toNat+248≤(ommerBase heap).toNat
  ommerBefore : (ommerBase heap).toNat+32≤(temporaryBase heap).toNat

structure OmmerHashOutput (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (target : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  normal : evaluateHOLFiniteState (markedOmmer input source heap) hashOmmer=(none,target)
  locals : target.locals=(markedOmmer input source heap).locals
  upper : target.clock≤(markedOmmer input source heap).clock
  lower : (markedOmmer input source heap).clock-203≤target.clock
  control : KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl (markedOmmer input source heap)
  memory : ∀ query,Keccak256.Protected 2713714976#64 2713715176#64 (ommerBase heap) query →
    target.memory query=(markedOmmer input source heap).memory query

theorem ommer_marked_environment (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (environment : Keccak256.Environment source 2713714976#64 2713715176#64) :
    Keccak256.Environment (markedOmmer input source heap) 2713714976#64 2713715176#64 := by
  apply Keccak256.Environment.of_fields source (markedOmmer input source heap) _ _ environment rfl rfl rfl
  intro key other
  simp [markedOmmer,temporaryAllocated,ommerAllocated,parentStoredHeader,markedHeader,clearedHeader,allocatedHeader,
    readEntry,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm other]

/-- The digest and FFI events are those of the actual original hash call.
Its normal return supplies the protected-memory and control facts. -/
theorem ommer_hash_from_execution (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (environment : Keccak256.Environment source 2713714976#64 2713715176#64) (layout : OmmerLayout heap)
    (execution : CallPrefix.Execution (temporaryAllocated input source heap) afterOmmerBuffers current) :
    ∃ hashed,OmmerHashOutput input source heap hashed ∧ CallPrefix.Execution hashed afterOmmerHash current := by
  have markedExecution:=ommer_marker_from_execution input source current heap environment.domain layout.temporaryArena execution
  obtain ⟨hashed,normal,next⟩:=markedExecution.command_next hashOmmer afterOmmerHash
  let marked:=markedOmmer input source heap
  have tmpCell : marked.locals.lookup (ofString "tmp")=some (.val (.word (temporaryBase heap))):=temporary_local input source heap
  have ohCell : marked.locals.lookup (ofString "oh")=some (.val (.word (ommerBase heap))):=ommer_local input source heap
  have args : evalListHOLFinite marked (h:=fun address=>Classical.propDecidable (marked.memaddrs address))
      [localVar "tmp",.const 1#64,localVar "oh"]=some (Keccak256.values (temporaryBase heap) (ommerBase heap) 1):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,tmpCell,ohCell,Keccak256.values]
  have buffers : Keccak256.Buffers 2713714976#64 (temporaryBase heap) 2713715176#64 (ommerBase heap) 1:=
    ⟨⟨by decide,by decide⟩,by decide,AllocatedBytes.Arena.weaken _ 8 1 layout.temporaryArena (by decide),
      ⟨by decide,by decide⟩,by decide,layout.ommerArena⟩
  have data:=Keccak256.allocated_entry marked _ _ _ _ 1 (ommer_marked_environment input source heap environment) buffers
  obtain ⟨locals,upper,lower,control,memory⟩:=Keccak256.call_normal marked hashed _ _ _ _ _ 1 args
    (Keccak256.original_code source.code installed) data (by decide) normal
  exact ⟨hashed,⟨normal,locals,upper,lower,control,memory⟩,next⟩

theorem ommer_hash (input : Guest.InputBlob) (origin initializer source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root workspace nodes stateRoot codes : BitVec 64) (counts : Nat→BitVec 64)
    (prepared : RequestRootHashData.Prepared input origin root counts)
    (ready : PayloadHeaderEntry input origin initializer source root workspace nodes stateRoot codes)
    (execution : CallPrefix.Execution source actions current) :
    ∃ heap hashed,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      workspace.toNat+40≤heap.toNat ∧ root.toNat≤heap.toNat ∧ OmmerLayout heap ∧
      OmmerHashOutput input source heap hashed ∧ CallPrefix.Execution hashed afterOmmerHash current := by
  obtain ⟨heap,cell,arena,aligned,workspaceBefore,rootBefore,ohArena,tmpArena,ohAligned,tmpAligned,headerBefore,ommerBefore,next⟩:=
    ommer_allocations input origin initializer source current root workspace nodes stateRoot codes counts prepared ready execution
  let layout : OmmerLayout heap:=⟨arena,aligned,ohArena,tmpArena,ohAligned,tmpAligned,headerBefore,ommerBefore⟩
  obtain ⟨hashed,output,rest⟩:=ommer_hash_from_execution input source current heap ready.state.1 ready.environment layout next
  exact ⟨heap,hashed,cell,workspaceBefore,rootBefore,layout,output,rest⟩

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.ommer_marked_environment
#print axioms InitECandidate.Solver.Input.PayloadHeader.ommer_hash_from_execution
#print axioms InitECandidate.Solver.Input.PayloadHeader.ommer_hash
