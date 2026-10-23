import InitECandidate.Solver.Mpt.NibbleKeySecureTail

namespace InitECandidate.Solver.Mpt.NibbleKey
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def secureAllocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  QueryBranch.bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 64#64) "nb" heap

/-- A true secure allocation return derives its real64-byte arena and
then the actual converter result; allocation room is never presumed. -/
theorem secure_allocation_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (hash heap : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false)
    (hashCell : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hash)))
    (inputArena : AllocatedBytes.Arena hash 32) (before : hash.toNat+32≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source secureAllocation=(some (.returned value),target)) :
    AllocatedBytes.Arena heap 64 ∧ value=output heap 32 ∧ TrieWalk.KeyView target.memory target.memaddrs target.be heap 64 ∧
      source.clock-target.clock≤10 ∧
      KeyToNibbles.writeMetadata target=KeyToNibbles.writeMetadata (PersistentAlloc.post source heap 64#64) ∧
      ∀ query : BitVec 64,query.toNat<heap.toNat ∨ heap.toNat+64≤query.toNat→target.memory query=source.memory query := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [.const 64#64]=some (PersistentAlloc.values 64#64):=rfl
  rw [secure_shapes.2.1] at normal
  obtain ⟨room,_funded,inner,continued,endpoint⟩:=PersistentAlloc.call_normal source target "nb" [.const 64#64] secureTail heap 64#64 args
    (PersistentAlloc.original_code source.code installed) (Input.Trap.original_code source.code installed) heapCell (by have upper:=frontier.upper; omega) value normal
  have arena : AllocatedBytes.Arena heap 64:=⟨frontier.lower,room⟩
  let current:=secureAllocated source heap
  have currentHash : current.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hash)):=by
    simpa [current,secureAllocated,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      show ofString "heap_ptr"≠ofString "mpt_hash_scratch" from by decide] using hashCell
  have currentOut : current.locals.lookup (ofString "nb")=some (.val (.word heap)):=bind_lookup_same _ _ _
  obtain ⟨answer,view,cost,fields,memory⟩:=secure_tail_normal current inner hash heap installed domain little currentHash currentOut inputArena arena aligned before value continued
  rw [endpoint]
  exact ⟨arena,answer,view,(by change source.clock-inner.clock≤10; change source.clock-1-inner.clock≤9 at cost; omega),fields,memory⟩

end InitECandidate.Solver.Mpt.NibbleKey

#print axioms InitECandidate.Solver.Mpt.NibbleKey.secure_allocation_normal
