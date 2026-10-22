import InitECandidate.Solver.Mpt.StateInitStorageNormal

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix MutableTable
open Flapjack.Basis.Pure.MlString

theorem storage_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (workspace heap : BitVec 64) (key : MlS)
    (other : key≠ofString "heap_ptr") :
    (storageReady source workspace heap).globals.lookup key=source.globals.lookup key:=by
  simp [storageReady,written,TableRuntime.callState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm other]

theorem storage_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (workspace heap : BitVec 64)
    (scalars : Input.OriginalScalarGlobals.Scalars source.globals) :
    Input.OriginalScalarGlobals.Scalars (storageReady source workspace heap).globals:=
  scalars.update (ofString "heap_ptr") (BitVec.ofNat 64 (NaturalLayout.freshEnd .word heap.toNat 64))

theorem storage_t (source : PanSemStateFiniteExact 64 Guest.HostMemory) (workspace heap : BitVec 64) :
    (storageReady source workspace heap).locals.lookup (ofString "t")=some (.val (.word heap)):=by
  simp [storageReady,written,TableRuntime.callState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem storage_code (source : PanSemStateFiniteExact 64 Guest.HostMemory) (workspace heap : BitVec 64) :
    (storageReady source workspace heap).code=source.code:=rfl

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.storage_other
#print axioms InitECandidate.Solver.Mpt.StateInit.storage_scalars
#print axioms InitECandidate.Solver.Mpt.StateInit.storage_t
#print axioms InitECandidate.Solver.Mpt.StateInit.storage_code
