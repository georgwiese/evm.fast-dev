import InitECandidate.Solver.Mpt.CompactToNibblesNormal
import InitECandidate.Solver.Rlp.ValidationArena

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Physical output of the same actual original compact-path conversion.
The true current heap/cursor and protected preceding storage are retained. -/
structure Snapshot (origin target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (length : Nat) (heap cursor limit : BitVec 64) (nibbles : Nat) (leaf : BitVec 64) : Prop where
  positive : 1≤length
  outputArena : AllocatedBytes.Arena heap (2*length)
  nibbleBound : nibbles≤2*length
  leafBinary : leaf=0#64 ∨ leaf=1#64
  arena : Rlp.Validation.Arena target cursor limit
  heapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap (BitVec.ofNat 64 (2*length)))))
  nextArena : AllocatedBytes.Arena (PersistentAlloc.rounded heap (BitVec.ofNat 64 (2*length))) 0
  nextAligned : (PersistentAlloc.rounded heap (BitVec.ofNat 64 (2*length))).toNat%8=0
  grows : heap.toNat+2*length≤(PersistentAlloc.rounded heap (BitVec.ofNat 64 (2*length))).toNat
  metadata : KeyToNibbles.writeMetadata target=KeyToNibbles.writeMetadata (PersistentAlloc.post origin heap (BitVec.ofNat 64 (2*length)))
  memory : ∀ query : BitVec 64,query.toNat<heap.toNat ∨ heap.toNat+2*length≤query.toNat→target.memory query=origin.memory query

theorem body_snapshot (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer heap cursor limit : BitVec 64) (length : Nat) (bounded : length≤1024)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ nibbles leaf,value=output heap nibbles leaf ∧ Snapshot source target length heap cursor limit nibbles leaf := by
  obtain ⟨positive,outputArena,nibbles,leaf,nibbleBound,binary,valueEq,metadata,memory⟩:=
    body_normal source target pointer heap length bounded pointerCell lengthCell heapCell heapArena aligned installed value normal
  have amountNumber : (BitVec.ofNat 64 (2*length)).toNat=2*length:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have checked:=PersistentAlloc.guards heap (BitVec.ofNat 64 (2*length)) (by rw [amountNumber]; exact outputArena.upper)
  have grows:=checked.2.2.1
  rw [amountNumber] at grows
  have nextArena : AllocatedBytes.Arena (PersistentAlloc.rounded heap (BitVec.ofNat 64 (2*length))) 0:=
    ⟨by have lower:=heapArena.lower; omega,by have upper:=checked.2.2.2.1; omega⟩
  have globals:=congrArg PanSemStateFiniteExact.globals metadata
  change target.globals=(PersistentAlloc.post source heap (BitVec.ofNat 64 (2*length))).globals at globals
  have domain:=congrArg PanSemStateFiniteExact.memaddrs metadata
  change target.memaddrs=source.memaddrs at domain
  have nextHeap : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap (BitVec.ofNat 64 (2*length))))):=by
    rw [globals]
    simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
  have nextScratch : Rlp.Validation.Arena target cursor limit:=by
    refine ⟨domain.trans arena.domain,?_,?_,arena.ordered,arena.aligned,arena.lower,arena.upper⟩
    · rw [globals]
      simpa [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,
        show ofString "heap_ptr"≠ofString "scratch_ptr" from by decide] using arena.cursorGlobal
    · rw [globals]
      simpa [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,
        show ofString "heap_ptr"≠ofString "frame_mem_ptr" from by decide] using arena.limitGlobal
  exact ⟨nibbles,leaf,valueEq,⟨positive,outputArena,nibbleBound,binary,nextScratch,nextHeap,nextArena,checked.2.2.2.2,grows,metadata,memory⟩⟩

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.body_snapshot
