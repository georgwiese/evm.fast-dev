import InitECandidate.Solver.Input.Requests.SetupProgram
import InitECandidate.Solver.Input.InitializerControl

namespace InitECandidate.Solver.Input.Requests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem prepared_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (cursor : BitVec 64) (start : Nat) :
    InitializerAllocations.context (prepared source input cursor start) = InitializerAllocations.context source := rfl

theorem prepared_globals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (cursor : BitVec 64) (start : Nat) :
    (prepared source input cursor start).globals = source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded cursor 80#64))) := rfl

theorem prepared_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (cursor : BitVec 64) (start : Nat) :
    (prepared source input cursor start).clock = source.clock - 1 := rfl

theorem prepared_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (cursor : BitVec 64) (start : Nat) (key : MlS)
    (rq : key ≠ ofString "rq") (o0 : key ≠ ofString "o0") (o1 : key ≠ ofString "o1") (o2 : key ≠ ofString "o2") (o3 : key ≠ ofString "o3") (o4 : key ≠ ofString "o4") :
    (prepared source input cursor start).locals.lookup key = source.locals.lookup key := by
  simp [prepared,loaded3,loaded2,loaded1,loaded0,allocated,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
    Ne.symm rq,Ne.symm o0,Ne.symm o1,Ne.symm o2,Ne.symm o3,Ne.symm o4]

theorem prepared_request (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (cursor : BitVec 64) (start : Nat) :
    (prepared source input cursor start).locals.lookup (ofString "rq") = some (.val (.word cursor)) := by
  simp [prepared,loaded3,loaded2,loaded1,loaded0,allocated,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
    show ofString "o4" ≠ ofString "rq" from by decide,show ofString "o3" ≠ ofString "rq" from by decide,
    show ofString "o2" ≠ ofString "rq" from by decide,show ofString "o1" ≠ ofString "rq" from by decide,show ofString "o0" ≠ ofString "rq" from by decide]

theorem prepared_offsets (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (cursor : BitVec 64) (start : Nat) :
    (prepared source input cursor start).locals.lookup (ofString "o0") = some (.val (.word (offsetWord input start 0))) ∧
    (prepared source input cursor start).locals.lookup (ofString "o1") = some (.val (.word (offsetWord input start 1))) ∧
    (prepared source input cursor start).locals.lookup (ofString "o2") = some (.val (.word (offsetWord input start 2))) ∧
    (prepared source input cursor start).locals.lookup (ofString "o3") = some (.val (.word (offsetWord input start 3))) ∧
    (prepared source input cursor start).locals.lookup (ofString "o4") = some (.val (.word (offsetWord input start 4))) := by
  simp [prepared,loaded3,loaded2,loaded1,loaded0,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
    show ofString "o1" ≠ ofString "o0" from by decide,show ofString "o2" ≠ ofString "o0" from by decide,
    show ofString "o3" ≠ ofString "o0" from by decide,show ofString "o4" ≠ ofString "o0" from by decide,
    show ofString "o2" ≠ ofString "o1" from by decide,show ofString "o3" ≠ ofString "o1" from by decide,
    show ofString "o4" ≠ ofString "o1" from by decide,show ofString "o3" ≠ ofString "o2" from by decide,
    show ofString "o4" ≠ ofString "o2" from by decide,show ofString "o4" ≠ ofString "o3" from by decide]

theorem restore_setup_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (cursor : BitVec 64) (start : Nat) :
    emptyLocalsHOLFinite (restoreSetup source input cursor start target) = emptyLocalsHOLFinite target := rfl

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.prepared_context
#print axioms InitECandidate.Solver.Input.Requests.prepared_globals
#print axioms InitECandidate.Solver.Input.Requests.prepared_clock
#print axioms InitECandidate.Solver.Input.Requests.prepared_other
#print axioms InitECandidate.Solver.Input.Requests.prepared_request
#print axioms InitECandidate.Solver.Input.Requests.prepared_offsets
#print axioms InitECandidate.Solver.Input.Requests.restore_setup_frame
