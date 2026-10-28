import InitECandidate.Solver.Input.CurrentTable.NewGeometry
import InitECandidate.Solver.Input.CurrentStartup.ArenaFrame
import InitECandidate.Solver.CurrentKeccak.Environment

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Reached current table-constructor entry. Capacity bounds come from the
actual builder loop; no allocation room or future successful call is assumed. -/
structure Context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cap stp pad : BitVec 64) : Prop where
  arena : CurrentStartup.ArenaState source
  environment : CurrentKeccak.Hash.Environment source stp pad
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapLower : 2701131776≤heap.toNat
  heapBound : heap.toNat≤2952790016
  heapAligned : heap.toNat%8=0
  capLower : 2≤cap.toNat
  capSmall : cap.toNat≤2^32

theorem Context.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {heap cap stp pad : BitVec 64}
    (ready : Context source heap cap stp pad) (same : LocalEffects.erase target=LocalEffects.erase source) : Context target heap cap stp pad := by
  have globals:=congrArg PanSemStateFiniteExact.globals same
  change target.globals=source.globals at globals
  exact ⟨ready.arena.of_frame same,ready.environment.of_frame same,by rw [globals]; exact ready.heapCell,
    ready.heapLower,ready.heapBound,ready.heapAligned,ready.capLower,ready.capSmall⟩

theorem finish_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cap : BitVec 64) :
    (finishSource source heap cap).globals.lookup (ofString "heap_ptr")=some (.val (.word (endPointer heap cap))) :=
  (array_frame (orderEntry source heap cap) heap (orderPointer heap cap) (size8 cap) "order" 48).1

theorem finish_globals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cap : BitVec 64)
    (arena : AllocatedBytes.Arena heap 88) (key : MlS) (different : key≠ofString "heap_ptr") :
    (finishSource source heap cap).globals.lookup key=source.globals.lookup key := by
  have header:=keys_frame source heap cap arena
  have first:=array_frame (keysEntry source heap cap) heap (keysPointer heap) (size32 cap) "keys" 32
  have second:=array_frame (nodesEntry source heap cap) heap (nodesPointer heap cap) (size32 cap) "nodes" 40
  have third:=array_frame (orderEntry source heap cap) heap (orderPointer heap cap) (size8 cap) "order" 48
  exact (third.2.2.2.1 key different).trans ((second.2.2.2.1 key different).trans
    ((first.2.2.2.1 key different).trans (header.2.2.2 key different)))

/-- Physical result of the actual current constructor, including its empty
Patricia header, separated arrays and advanced heap. -/
structure Returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cap stp pad : BitVec 64) : Prop where
  geometry : Geometry heap cap
  arena : CurrentStartup.ArenaState post
  environment : CurrentKeccak.Hash.Environment post stp pad
  heapCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word (endPointer heap cap)))
  heapAfter : heap.toNat≤(endPointer heap cap).toNat
  fields : ∀ entry∈writes heap cap,post.memory entry.1=.word entry.2
  earlier : ∀ query : BitVec 64,query.toNat<heap.toNat→post.memory query=source.memory query
  globals : ∀ key : MlS,key≠ofString "heap_ptr"→post.globals.lookup key=source.globals.lookup key
  metadata : post.memaddrs=source.memaddrs ∧ post.be=source.be ∧ post.eshapes=source.eshapes ∧ post.code=source.code

/-- Re-anchor the same physical returned table across caller/callee local
and clock changes. All source memory/global observations stay explicit. -/
theorem Returned.reanchor {source origin post : PanSemStateFiniteExact 64 Guest.HostMemory} {heap cap stp pad : BitVec 64}
    (ready : Returned source post heap cap stp pad) (same : LocalEffects.erase origin=LocalEffects.erase source) :
    Returned origin post heap cap stp pad := by
  have memory:=LocalEffects.memory_of_erase source origin same
  have globals:=congrArg PanSemStateFiniteExact.globals same
  have domain:=congrArg PanSemStateFiniteExact.memaddrs same
  have endian:=congrArg PanSemStateFiniteExact.be same
  have shapes:=congrArg PanSemStateFiniteExact.eshapes same
  have code:=congrArg PanSemStateFiniteExact.code same
  change origin.globals=source.globals at globals
  change origin.memaddrs=source.memaddrs at domain
  change origin.be=source.be at endian
  change origin.eshapes=source.eshapes at shapes
  change origin.code=source.code at code
  exact ⟨ready.geometry,ready.arena,ready.environment,ready.heapCell,ready.heapAfter,ready.fields,
    by intro query before; exact (ready.earlier query before).trans (congrFun memory query).symm,
    by intro key different; exact (ready.globals key different).trans (congrArg (fun table=>table.lookup key) globals).symm,
    ready.metadata.1.trans domain.symm,ready.metadata.2.1.trans endian.symm,ready.metadata.2.2.1.trans shapes.symm,ready.metadata.2.2.2.trans code.symm⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- A genuine normal current constructor return supplies the entire next
physical workspace and empty-table representation. Its room, header cells
and earlier-memory frame all come from that same actual execution. -/
theorem Context.returned {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {heap cap stp pad : BitVec 64}
    (ready : Context source heap cap stp pad)
    (keyLocal : source.locals.lookup (ofString "key_len")=some (.val (.word 32#64)))
    (capLocal : source.locals.lookup (ofString "cap")=some (.val (.word cap)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=.val (.word heap) ∧ Returned source post heap cap stp pad := by
  obtain ⟨answer,funded,tableRoom,keysRoom,nodesRoom,orderRoom,tableArena,erased,clock⟩:=
    body_returned source post heap cap keyLocal capLocal ready.capLower ready.heapCell ready.heapLower ready.heapBound ready.heapAligned
      ready.arena.domain ready.arena.code value normal
  have geometry:=geometry_of_room heap cap ready.heapLower ready.capSmall tableRoom keysRoom nodesRoom orderRoom
  have globals:=congrArg PanSemStateFiniteExact.globals erased
  change post.globals=(finishSource source heap cap).globals at globals
  have memory:=LocalEffects.memory_of_erase (finishSource source heap cap) post erased
  have kept (key : MlS) (different : key≠ofString "heap_ptr") : post.globals.lookup key=source.globals.lookup key := by
    rw [globals]
    exact finish_globals source heap cap tableArena key different
  have metadata:=evaluation_fields source post body (some (.returned value)) normal
  have nextArena : CurrentStartup.ArenaState post :=
    ⟨(kept _ (by decide)).trans ready.arena.scratch,(kept _ (by decide)).trans ready.arena.frame,
      metadata.1.trans ready.arena.domain,by rw [metadata.2.2.2]; exact ready.arena.code⟩
  have environment : CurrentKeccak.Hash.Environment post stp pad :=
    ⟨nextArena.code,nextArena.domain,(kept _ (by decide)).trans ready.environment.stateGlobal,
      (kept _ (by decide)).trans ready.environment.padGlobal,ready.environment.stateArena,ready.environment.padArena,
      ready.environment.stateAligned,ready.environment.padAligned⟩
  have afterHeap : heap.toNat≤(endPointer heap cap).toNat := by
    have a:=geometry.tableBefore
    have b:=geometry.keysBefore
    have c:=geometry.nodesBefore
    have d:=geometry.orderBefore
    omega
  exact ⟨answer,geometry,nextArena,environment,by rw [globals]; exact finish_heap source heap cap,afterHeap,
    by intro entry member; rw [memory]; exact finish_field source heap cap entry member,
    by intro query before; rw [memory]; exact finish_before source heap cap query tableArena before,kept,metadata⟩

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.Context.of_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.New.finish_heap
#print axioms InitECandidate.Solver.Input.CurrentTable.New.finish_globals
#print axioms InitECandidate.Solver.Input.CurrentTable.New.Context.returned

#print axioms InitECandidate.Solver.Input.CurrentTable.New.Returned.reanchor
