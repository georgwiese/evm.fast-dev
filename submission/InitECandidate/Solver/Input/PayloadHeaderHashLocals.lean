import InitECandidate.Solver.Input.PayloadHeaderOmmerHash

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main

theorem OmmerHashOutput.header_local (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (output : OmmerHashOutput input source heap target) :
    target.locals.lookup (ofString "h")=some (.val (.word heap)) := by
  rw [output.locals]
  simp [markedOmmer,temporaryAllocated,ommerAllocated,parentStoredHeader,markedHeader,clearedHeader,allocatedHeader,
    PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
    show ofString "tmp"≠ofString "h" from by decide,show ofString "oh"≠ofString "h" from by decide]

theorem OmmerHashOutput.raw_local (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (output : OmmerHashOutput input source heap target) :
    target.locals.lookup (ofString "raw")=some (.val (.word (inputPointer+62#64))) := by
  rw [output.locals]
  simp [markedOmmer,temporaryAllocated,ommerAllocated,parentStoredHeader,markedHeader,clearedHeader,allocatedHeader,readEntry,QueryBranch.bind,
    PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
    show ofString "tmp"≠ofString "raw" from by decide,show ofString "oh"≠ofString "raw" from by decide,
    show ofString "h"≠ofString "raw" from by decide]

theorem OmmerHashOutput.payload_local (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (output : OmmerHashOutput input source heap target) :
    target.locals.lookup (ofString "pl")=some (.val (.word (PayloadPrefix.cursor input))) := by
  rw [output.locals]
  simp [markedOmmer,temporaryAllocated,ommerAllocated,parentStoredHeader,markedHeader,clearedHeader,allocatedHeader,readEntry,QueryBranch.bind,
    PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
    show ofString "tmp"≠ofString "pl" from by decide,show ofString "oh"≠ofString "pl" from by decide,
    show ofString "h"≠ofString "pl" from by decide,show ofString "raw"≠ofString "pl" from by decide]

theorem OmmerHashOutput.ommer_local (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (output : OmmerHashOutput input source heap target) :
    target.locals.lookup (ofString "oh")=some (.val (.word (ommerBase heap))) := by
  rw [output.locals]
  exact PayloadHeader.ommer_local input source heap

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.OmmerHashOutput.header_local
#print axioms InitECandidate.Solver.Input.PayloadHeader.OmmerHashOutput.raw_local
#print axioms InitECandidate.Solver.Input.PayloadHeader.OmmerHashOutput.payload_local
#print axioms InitECandidate.Solver.Input.PayloadHeader.OmmerHashOutput.ommer_local
