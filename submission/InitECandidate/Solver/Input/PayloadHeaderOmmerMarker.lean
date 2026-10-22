import InitECandidate.Solver.Input.PayloadHeaderOmmerAllocation
import InitECandidate.Solver.WitnessRadix.ByteStoreWord

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def markOmmer : ProgHOL 64:=.storeByte (localVar "tmp") (.const 192#64)
def hashOmmer : ProgHOL 64:=.call (some (none,none)) (ofString "keccak256")
  [localVar "tmp",.const 1#64,localVar "oh"]
def afterOmmerMarker : List CallPrefix.Action:=afterOmmerBuffers.drop 1
def afterOmmerHash : List CallPrefix.Action:=afterOmmerMarker.drop 1
def markedOmmer (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  let allocated:=temporaryAllocated input source heap
  {allocated with memory:=ByteStore.put allocated.memory allocated.be (temporaryBase heap) 192#8}

set_option maxRecDepth 100000 in
theorem ommer_hash_actions : afterOmmerBuffers=.command markOmmer::.command hashOmmer::afterOmmerHash := by
  simp only [afterOmmerBuffers,afterFirstStores,afterClear,afterHeader,afterReads,actions,parts,body,Guest.guestFn_payload_header,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,
    afterOmmerHash,afterOmmerMarker,markOmmer,hashOmmer,localVar]
  rfl

theorem temporary_local (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) :
    (temporaryAllocated input source heap).locals.lookup (ofString "tmp")=some (.val (.word (temporaryBase heap))) :=
  bind_lookup_same _ _ _

theorem ommer_local (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) :
    (temporaryAllocated input source heap).locals.lookup (ofString "oh")=some (.val (.word (ommerBase heap))) := by
  simp [temporaryAllocated,ommerAllocated,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
    show ofString "tmp"≠ofString "oh" from by decide]

theorem ommer_marker_execute (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena (temporaryBase heap) 8) :
    evaluateHOLFiniteState (temporaryAllocated input source heap) markOmmer=(none,markedOmmer input source heap) := by
  let allocated:=temporaryAllocated input source heap
  have address : eval allocated (localVar "tmp")=some (.val (.word (temporaryBase heap))):=
    Request.local_word _ "tmp" _ (temporary_local input source heap)
  have mapped : allocated.memaddrs (panByteAlignHOL (width:=64) (temporaryBase heap)):=by
    simpa [byteAddress] using AllocatedBytes.byte_mapped allocated (temporaryBase heap) 8 0 domain arena (by decide)
  exact ByteStore.execute_word allocated (localVar "tmp") (.const 192#64) (temporaryBase heap) 192#64 address rfl mapped

theorem ommer_marker_from_execution (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena (temporaryBase heap) 8)
    (execution : CallPrefix.Execution (temporaryAllocated input source heap) afterOmmerBuffers current) :
    CallPrefix.Execution (markedOmmer input source heap) (.command hashOmmer::afterOmmerHash) current := by
  rw [ommer_hash_actions] at execution
  exact execution.command_known markOmmer _ (ommer_marker_execute input source heap domain arena)

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.ommer_hash_actions
#print axioms InitECandidate.Solver.Input.PayloadHeader.temporary_local
#print axioms InitECandidate.Solver.Input.PayloadHeader.ommer_local
#print axioms InitECandidate.Solver.Input.PayloadHeader.ommer_marker_execute
#print axioms InitECandidate.Solver.Input.PayloadHeader.ommer_marker_from_execution
