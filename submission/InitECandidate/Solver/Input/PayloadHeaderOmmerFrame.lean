import InitECandidate.Solver.Input.PayloadHeaderOmmerHash
import InitECandidate.Solver.WitnessRadix.CopyAwayIntervals

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main

theorem OmmerLayout.protected_before (heap query : BitVec 64) (layout : OmmerLayout heap)
    (lower : 2713717616≤query.toNat) (before : query.toNat<(ommerBase heap).toNat) :
    Keccak256.Protected 2713714976#64 2713715176#64 (ommerBase heap) query :=
  ⟨CopyGeneral.Away.before _ query 200 2713717616 (by decide) (by decide) lower,
    CopyGeneral.Away.before _ query 136 2713717616 (by decide) (by decide) lower,
    CopyGeneral.Away.after _ query 32 layout.ommerAligned (by have h:=layout.ommerArena.upper; omega) before⟩

theorem marked_ommer_older (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap query : BitVec 64) (layout : OmmerLayout heap) (before : query.toNat<heap.toNat) :
    (markedOmmer input source heap).memory query=source.memory query := by
  have tmpBacking:=AllocatedBytes.aligned_number (temporaryBase heap)
  have headerBefore:=layout.headerBefore
  have ommerBefore:=layout.ommerBefore
  have tmpAligned:=layout.temporaryAligned
  have differentTmp : query≠panByteAlignHOL (width:=64) (temporaryBase heap):=by
    intro same
    have numeric:=congrArg BitVec.toNat same
    omega
  have differentHeader : query≠heap:=by intro same; subst query; omega
  have plus8:=byteAddress_toNat heap 8 (by have h:=layout.headerArena.upper; omega)
  have differentParent : query≠heap+8#64:=by
    intro same
    have numeric:=congrArg BitVec.toNat same
    change (heap+8#64).toNat=heap.toNat+8 at plus8
    omega
  change ByteStore.put (parentStoredHeader input source heap).memory source.be (temporaryBase heap) 192#8 query=source.memory query
  rw [ByteStore.away _ _ _ _ _ differentTmp]
  change StoreWord.put (StoreWord.put (clearedHeader input source heap).memory heap 1#64)
    (heap+8#64) (inputPointer+62#64) query=source.memory query
  simp only [StoreWord.put,if_neg differentParent,if_neg differentHeader]
  exact cleared_older input source heap layout.headerArena query before

theorem OmmerHashOutput.older (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap query : BitVec 64) (layout : OmmerLayout heap) (output : OmmerHashOutput input source heap target)
    (lower : 2713717616≤query.toNat) (before : query.toNat<heap.toNat) : target.memory query=source.memory query := by
  have headerBefore:=layout.headerBefore
  exact (output.memory query (layout.protected_before heap query lower (by omega))).trans
    (marked_ommer_older input source heap query layout before)

def afterOmmerHeap (heap : BitVec 64):=PersistentAlloc.rounded (temporaryBase heap) 8#64

theorem OmmerHashOutput.heap (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (output : OmmerHashOutput input source heap target) :
    target.globals.lookup (ofString "heap_ptr")=some (.val (.word (afterOmmerHeap heap))) := by
  have globals:=congrArg (fun state=>state.globals.lookup (ofString "heap_ptr")) output.control
  change target.globals.lookup (ofString "heap_ptr")=(markedOmmer input source heap).globals.lookup (ofString "heap_ptr") at globals
  rw [globals]
  simp [markedOmmer,temporaryAllocated,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,afterOmmerHeap]

theorem OmmerHashOutput.environment (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (output : OmmerHashOutput input source heap target)
    (environment : Keccak256.Environment source 2713714976#64 2713715176#64) :
    Keccak256.Environment target 2713714976#64 2713715176#64 := by
  have domain:=congrArg PanSemStateFiniteExact.memaddrs output.control
  have code:=congrArg PanSemStateFiniteExact.code output.control
  have oracle:=congrArg (fun state=>state.ffi.oracle) output.control
  apply Keccak256.Environment.of_fields (markedOmmer input source heap) target _ _
    (ommer_marked_environment input source heap environment) domain code oracle
  intro key other
  have globals:=congrArg (fun state=>state.globals.lookup key) output.control
  exact globals

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.OmmerLayout.protected_before
#print axioms InitECandidate.Solver.Input.PayloadHeader.marked_ommer_older
#print axioms InitECandidate.Solver.Input.PayloadHeader.OmmerHashOutput.older
#print axioms InitECandidate.Solver.Input.PayloadHeader.OmmerHashOutput.heap
#print axioms InitECandidate.Solver.Input.PayloadHeader.OmmerHashOutput.environment
