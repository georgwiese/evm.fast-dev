import InitECandidate.Solver.Input.CurrentTable.NewScalarFrame
import InitECandidate.Solver.WitnessRadix.WordWrites
import Mathlib.Data.List.Nodup
import InitECandidate.Solver.Input.AssignedCallNormal
import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Input.GlobalAssign
import InitECandidate.Solver.Input.PersistentMemoryFrame

namespace InitECandidate.Solver.Input.CurrentTable.New
set_option maxRecDepth 10000
set_option maxHeartbeats 300000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

def scalarKeysEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key cap : BitVec 64) :=
  scalarHeaderStored (scalarFieldsEntry source heap key cap) heap key cap (strideWord key)
def scalarKeyAmount (key cap : BitVec 64) : BitVec 64 := (cap+1#64)*strideWord key
def scalarNodesPointer (heap key cap : BitVec 64) : BitVec 64 :=
  PersistentAlloc.rounded (keysPointer heap) (scalarKeyAmount key cap)
def scalarOrderPointer (heap key cap : BitVec 64) : BitVec 64 :=
  PersistentAlloc.rounded (scalarNodesPointer heap key cap) (size32 cap)
def scalarNextHeap (heap key cap : BitVec 64) : BitVec 64 :=
  PersistentAlloc.rounded (scalarOrderPointer heap key cap) (size8 cap)
def scalarNodesEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key cap : BitVec 64) :=
  arrayEntry (scalarKeysEntry source heap key cap) heap (keysPointer heap) (scalarKeyAmount key cap) "keys" 32
def scalarOrderEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key cap : BitVec 64) :=
  arrayEntry (scalarNodesEntry source heap key cap) heap (scalarNodesPointer heap key cap) (size32 cap) "nodes" 40
def scalarFinalEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key cap : BitVec 64) :=
  arrayEntry (scalarOrderEntry source heap key cap) heap (scalarOrderPointer heap key cap) (size8 cap) "order" 48
def scalarFinish (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key cap : BitVec 64) :=
  finishStored (scalarFinalEntry source heap key cap) heap cap

/-- The actual normal constructor prefix exposes its real scalar header
and continuation. Its first successful allocation supplies the header room. -/
theorem scalar_header_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key cap : BitVec 64)
    (keyCell : source.locals.lookup (ofString "key_len")=some (.val (.word key)))
    (capCell : source.locals.lookup (ofString "cap")=some (.val (.word cap))) (atLeastTwo : 2≤cap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    1≤source.clock ∧ heap.toNat+88≤2952790016 ∧ AllocatedBytes.Arena heap 88 ∧
      ScalarContext (scalarKeysEntry source heap key cap) heap (keysPointer heap) cap (strideWord key) ∧
      ∃ inner,evaluateHOLFiniteState (scalarKeysEntry source heap key cap) keysCall=(some (.returned value),inner) ∧
        LocalEffects.erase post=LocalEffects.erase inner ∧ post.clock=inner.clock := by
  rw [shapes.1] at normal
  rcases CurrentAlloc.scoped_classified source post "t" [.const 88#64] afterTable heap 88#64 rfl arena.code heapCell heapBound _ normal with stopped|reached
  · exact (stopped.2 value rfl).elim
  · obtain ⟨funded,room,middle,continued,endpoint⟩:=reached
    have tableArena : AllocatedBytes.Arena heap 88:=⟨heapArena.lower,by change heap.toNat+88≤2952790016 at room; omega⟩
    change evaluateHOLFiniteState (tableEntry source heap) afterTable=(some (.returned value),middle) at continued
    have currentKey : (tableEntry source heap).locals.lookup (ofString "key_len")=some (.val (.word key)):=
      (bind_lookup_other _ "t" "key_len" heap (by decide)).trans keyCell
    have currentCap : (tableEntry source heap).locals.lookup (ofString "cap")=some (.val (.word cap)):=
      (bind_lookup_other _ "t" "cap" heap (by decide)).trans capCell
    rw [scalar_prefix_execute (tableEntry source heap) key cap currentKey currentCap atLeastTwo] at continued
    let entered:=scalarFieldsEntry source heap key cap
    let inner:=(evaluateHOLFiniteState entered fields).2
    have observed:=congrArg Prod.fst continued
    have restored:=congrArg Prod.snd continued
    dsimp only at restored
    change (evaluateHOLFiniteState entered fields).1=some (.returned value) at observed
    have fieldsRun : evaluateHOLFiniteState entered fields=(some (.returned value),inner):=Prod.ext observed rfl
    have tableLocal : entered.locals.lookup (ofString "t")=some (.val (.word heap)) :=
      (bind_lookup_other _ "ncap" "t" cap (by decide)).trans
        ((bind_lookup_other _ "stride" "t" (strideWord key) (by decide)).trans (bind_lookup_same _ _ _))
    have keyLocal : entered.locals.lookup (ofString "key_len")=some (.val (.word key)) :=
      (bind_lookup_other _ "ncap" "key_len" cap (by decide)).trans
        ((bind_lookup_other _ "stride" "key_len" (strideWord key) (by decide)).trans currentKey)
    have strideLocal : entered.locals.lookup (ofString "stride")=some (.val (.word (strideWord key))) :=
      (bind_lookup_other _ "ncap" "stride" cap (by decide)).trans (bind_lookup_same _ _ _)
    have capLocal : entered.locals.lookup (ofString "cap")=some (.val (.word cap)) :=
      (bind_lookup_other _ "ncap" "cap" cap (by decide)).trans
        ((bind_lookup_other _ "stride" "cap" (strideWord key) (by decide)).trans currentCap)
    have ncapLocal : entered.locals.lookup (ofString "ncap")=some (.val (.word cap)):=bind_lookup_same _ _ _
    rw [scalar_fields_execute entered heap key cap (strideWord key) arena.domain tableArena heapAligned tableLocal keyLocal strideLocal capLocal] at fieldsRun
    let ready:=scalarKeysEntry source heap key cap
    have checked:=PersistentAlloc.guards heap 88#64 room
    have nextArena : AllocatedBytes.Arena (keysPointer heap) 0:=
      ⟨by have low:=heapArena.lower; have grows:=checked.2.2.1; change heap.toNat+88≤(keysPointer heap).toNat at grows; omega,
        by have upper:=checked.2.2.2.1; change (keysPointer heap).toNat≤2952790016 at upper; omega⟩
    have nextCell : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word (keysPointer heap))) := by
      simp [ready,scalarKeysEntry,scalarHeaderStored,putField,scalarFieldsEntry,tableEntry,QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,keysPointer]
    have currentArena : CurrentStartup.ArenaState ready := by
      refine ⟨?_,?_,arena.domain,arena.code⟩
      · simpa [ready,scalarKeysEntry,scalarHeaderStored,putField,scalarFieldsEntry,tableEntry,QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,show ofString "heap_ptr"≠ofString "scratch_ptr" from by decide] using arena.scratch
      · simpa [ready,scalarKeysEntry,scalarHeaderStored,putField,scalarFieldsEntry,tableEntry,QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,show ofString "heap_ptr"≠ofString "frame_mem_ptr" from by decide] using arena.frame
    have context : ScalarContext ready heap (keysPointer heap) cap (strideWord key):=
      ⟨currentArena,nextCell,nextArena,checked.2.2.2.1,checked.2.2.2.2,tableArena,heapAligned,
        by have grows:=checked.2.2.1; change heap.toNat+88≤(keysPointer heap).toNat at grows; omega,tableLocal,ncapLocal,strideLocal⟩
    refine ⟨funded,room,tableArena,context,inner,fieldsRun,?_,?_⟩
    · rw [endpoint,←restored]; rfl
    · rw [endpoint,←restored]; rfl

/-- A genuine normal array-allocation scope retains both the exact inner
state and its own request room. No later successful call is an entry premise. -/
theorem scalar_array_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cursor cap stride amount : BitVec 64) (name : String) (offset : Nat)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (context : ScalarContext source table cursor cap stride)
    (notTable : ofString name≠ofString "t") (notCap : ofString name≠ofString "ncap") (notStride : ofString name≠ofString "stride")
    (inside : offset<88) (aligned : offset%8=0)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (PersistentAlloc.values amount))
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "alloc") arguments
      (.seq (.store (Scalar.plus (localVar "t") offset) (localVar name)) continuation))=(some (.returned value),post)) :
    1≤source.clock ∧ cursor.toNat+amount.toNat≤2952790016 ∧
      ScalarContext (arrayEntry source table cursor amount name offset) table (PersistentAlloc.rounded cursor amount) cap stride ∧
      ∃ inner,evaluateHOLFiniteState (arrayEntry source table cursor amount name offset) continuation=(some (.returned value),inner) ∧
        LocalEffects.erase post=LocalEffects.erase inner ∧ post.clock=inner.clock := by
  rcases array_allocation_trace source post table cursor amount name offset arguments continuation notTable inside aligned
    context.arena.domain context.tableArena context.tableAligned context.tableCell args context.arena.code context.heapCell context.cursorBound _ normal with stopped|reached
  · exact (stopped.2 value rfl).elim
  · obtain ⟨funded,room,inner,continued,endpoint⟩:=reached
    refine ⟨funded,room,context.after_array amount name offset notTable notCap notStride inside room,inner,continued,?_,?_⟩
    · rw [endpoint]; rfl
    · rw [endpoint]; rfl

private theorem scalar_erase_empty (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    LocalEffects.erase (emptyLocalsHOLFinite source)=LocalEffects.erase source := by rfl

/-- The unchanged constructor at any scalar key width has this exact
normal result. All four allocation extents and clock funding follow from
the same observed run, including all eleven actual header stores. -/
theorem body_scalar_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key cap : BitVec 64)
    (keyCell : source.locals.lookup (ofString "key_len")=some (.val (.word key)))
    (capCell : source.locals.lookup (ofString "cap")=some (.val (.word cap))) (atLeastTwo : 2≤cap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=.val (.word heap) ∧ 4≤source.clock ∧ AllocatedBytes.Arena heap 88 ∧ heap.toNat+88≤2952790016 ∧
      (keysPointer heap).toNat+(scalarKeyAmount key cap).toNat≤2952790016 ∧
      (scalarNodesPointer heap key cap).toNat+(size32 cap).toNat≤2952790016 ∧
      (scalarOrderPointer heap key cap).toNat+(size8 cap).toNat≤2952790016 ∧
      LocalEffects.erase post=LocalEffects.erase (scalarFinish source heap key cap) ∧
      post.clock=source.clock-4 ∧ PersistentNormalFrame source post heap := by
  obtain ⟨valueEq,owned,frame⟩:=body_scalar_normal_frame source post heap key cap keyCell capCell atLeastTwo heapCell heapArena heapBound heapAligned arena value normal
  obtain ⟨headerFunded,tableRoom,tableArena,keysContext,keysPost,keysRun,headerErase,headerClock⟩:=
    scalar_header_normal source post heap key cap keyCell capCell atLeastTwo heapCell heapArena heapBound heapAligned arena value normal
  have keysArgs : evalListHOLFinite (scalarKeysEntry source heap key cap) (h:=fun query=>Classical.propDecidable ((scalarKeysEntry source heap key cap).memaddrs query)) [keyAmount]=some (PersistentAlloc.values (scalarKeyAmount key cap)) := by
    simp [keyAmount,scalarKeyAmount,PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,
      keysContext.capCell,keysContext.strideCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]
  rw [array_shapes.1] at keysRun
  obtain ⟨keysFunded,keysRoom,nodesContext,nodesPost,nodesRun,keysErase,keysClock⟩:=
    scalar_array_normal _ _ heap (keysPointer heap) cap (strideWord key) (scalarKeyAmount key cap) "keys" 32 [keyAmount] nodesCall
      keysContext (by decide) (by decide) (by decide) (by decide) (by decide) keysArgs value keysRun
  change ScalarContext (scalarNodesEntry source heap key cap) heap (scalarNodesPointer heap key cap) cap (strideWord key) at nodesContext
  have nodeArgs:=node_arguments (scalarNodesEntry source heap key cap) cap nodesContext.capCell
  rw [array_shapes.2.1] at nodesRun
  obtain ⟨nodesFunded,nodesRoom,orderContext,orderPost,orderRun,nodesErase,nodesClock⟩:=
    scalar_array_normal _ _ heap (scalarNodesPointer heap key cap) cap (strideWord key) (size32 cap) "nodes" 40 [nodeAmount] orderCall
      nodesContext (by decide) (by decide) (by decide) (by decide) (by decide) nodeArgs value nodesRun
  change ScalarContext (scalarOrderEntry source heap key cap) heap (scalarOrderPointer heap key cap) cap (strideWord key) at orderContext
  have orderArgs:=order_arguments (scalarOrderEntry source heap key cap) cap orderContext.capCell
  rw [array_shapes.2.2] at orderRun
  obtain ⟨orderFunded,orderRoom,finalContext,finalPost,finalRun,orderErase,orderClock⟩:=
    scalar_array_normal _ _ heap (scalarOrderPointer heap key cap) cap (strideWord key) (size8 cap) "order" 48 [orderAmount] finalFields
      orderContext (by decide) (by decide) (by decide) (by decide) (by decide) orderArgs value orderRun
  change ScalarContext (scalarFinalEntry source heap key cap) heap (scalarNextHeap heap key cap) cap (strideWord key) at finalContext
  have last:=final_fields_execute (scalarFinalEntry source heap key cap) heap cap finalContext.arena.domain tableArena heapAligned finalContext.tableCell finalContext.capCell
  change evaluateHOLFiniteState (scalarFinalEntry source heap key cap) finalFields=(some (.returned value),finalPost) at finalRun
  rw [last] at finalRun
  have endpoint:=congrArg Prod.snd finalRun
  dsimp only at endpoint
  have physical : LocalEffects.erase finalPost=LocalEffects.erase (scalarFinish source heap key cap) := by
    simpa only [scalar_erase_empty,scalarFinish] using (congrArg LocalEffects.erase endpoint).symm
  have lastClock:=congrArg PanSemStateFiniteExact.clock endpoint
  change source.clock-1-1-1-1=finalPost.clock at lastClock
  have clock : post.clock=source.clock-4 := by
    have same:=headerClock.trans (keysClock.trans (nodesClock.trans orderClock))
    omega
  have funded : 4≤source.clock := by
    change 1≤source.clock-1-1-1 at orderFunded
    omega
  exact ⟨valueEq,funded,tableArena,tableRoom,keysRoom,nodesRoom,orderRoom,headerErase.trans (keysErase.trans (nodesErase.trans (orderErase.trans physical))),clock,frame⟩

def scalarWrites (table key cap : BitVec 64) : List (BitVec 64×BitVec 64) :=
  [(table+0#64,key),(table+8#64,strideWord key),(table+16#64,cap),(table+24#64,0#64),
   (table+32#64,keysPointer table),(table+40#64,scalarNodesPointer table key cap),(table+48#64,scalarOrderPointer table key cap),
   (table+56#64,0#64),(table+64#64,1#64),(table+72#64,0#64),(table+80#64,cap)]

theorem scalar_finish_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap : BitVec 64) :
    (scalarFinish source table key cap).memory=WordWrites.write source.memory (scalarWrites table key cap) := by rfl

theorem scalar_writes_distinct (table key cap : BitVec 64) : ((scalarWrites table key cap).map Prod.fst).Nodup := by
  change (([0#64,8#64,16#64,24#64,32#64,40#64,48#64,56#64,64#64,72#64,80#64] : List (BitVec 64)).map (fun offset=>table+offset)).Nodup
  apply List.Nodup.map (fun left right same=>(BitVec.add_right_inj table).mp same)
  decide

/-- Every one of the eleven fields has its actual stored value, without
asserting anything about the contents of the newly allocated arrays. -/
theorem scalar_finish_field (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap : BitVec 64)
    (entry : BitVec 64×BitVec 64) (member : entry∈scalarWrites table key cap) :
    (scalarFinish source table key cap).memory entry.1=.word entry.2 := by
  rw [scalar_finish_memory]
  exact WordWrites.write_unique source.memory (scalarWrites table key cap) entry (scalar_writes_distinct table key cap) member

/-- The real array extents use the constructor's word arithmetic. Larger
natural-number formulas require separate no-overflow facts at their callers. -/
structure ScalarGeometry (heap key cap : BitVec 64) : Prop where
  table : AllocatedBytes.Arena heap 88
  keys : AllocatedBytes.Arena (keysPointer heap) (scalarKeyAmount key cap).toNat
  nodes : AllocatedBytes.Arena (scalarNodesPointer heap key cap) (size32 cap).toNat
  order : AllocatedBytes.Arena (scalarOrderPointer heap key cap) (size8 cap).toNat
  tableBefore : heap.toNat+88≤(keysPointer heap).toNat
  keysBefore : (keysPointer heap).toNat+(scalarKeyAmount key cap).toNat≤(scalarNodesPointer heap key cap).toNat
  nodesBefore : (scalarNodesPointer heap key cap).toNat+(size32 cap).toNat≤(scalarOrderPointer heap key cap).toNat
  orderBefore : (scalarOrderPointer heap key cap).toNat+(size8 cap).toNat≤(scalarNextHeap heap key cap).toNat
  keysAligned : (keysPointer heap).toNat%8=0
  nodesAligned : (scalarNodesPointer heap key cap).toNat%8=0
  orderAligned : (scalarOrderPointer heap key cap).toNat%8=0
  endAligned : (scalarNextHeap heap key cap).toNat%8=0
  endBound : (scalarNextHeap heap key cap).toNat≤2952790016

theorem scalar_geometry_of_room (table key cap : BitVec 64) (owned : AllocatedBytes.Arena table 88)
    (tableRoom : table.toNat+88≤2952790016)
    (keysRoom : (keysPointer table).toNat+(scalarKeyAmount key cap).toNat≤2952790016)
    (nodesRoom : (scalarNodesPointer table key cap).toNat+(size32 cap).toNat≤2952790016)
    (orderRoom : (scalarOrderPointer table key cap).toNat+(size8 cap).toNat≤2952790016) :
    ScalarGeometry table key cap := by
  have first:=PersistentAlloc.guards table 88#64 tableRoom
  have second:=PersistentAlloc.guards (keysPointer table) (scalarKeyAmount key cap) keysRoom
  have third:=PersistentAlloc.guards (scalarNodesPointer table key cap) (size32 cap) nodesRoom
  have fourth:=PersistentAlloc.guards (scalarOrderPointer table key cap) (size8 cap) orderRoom
  have tableBefore : table.toNat+88≤(keysPointer table).toNat:=first.2.2.1
  have keysBefore : (keysPointer table).toNat+(scalarKeyAmount key cap).toNat≤(scalarNodesPointer table key cap).toNat:=second.2.2.1
  have nodesBefore : (scalarNodesPointer table key cap).toNat+(size32 cap).toNat≤(scalarOrderPointer table key cap).toNat:=third.2.2.1
  have orderBefore : (scalarOrderPointer table key cap).toNat+(size8 cap).toNat≤(scalarNextHeap table key cap).toNat:=fourth.2.2.1
  have lower:=owned.lower
  exact ⟨owned,⟨by omega,by omega⟩,⟨by omega,by omega⟩,⟨by omega,by omega⟩,
    tableBefore,keysBefore,nodesBefore,orderBefore,first.2.2.2.2,second.2.2.2.2,third.2.2.2.2,fourth.2.2.2.2,fourth.2.2.2.1⟩

/-- Empty current Patricia header at the actual scalar key width. This
asserts initialized metadata and owned arrays, without initialized nodes. -/
structure ScalarEmpty (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap : BitVec 64) : Prop where
  geometry : ScalarGeometry table key cap
  aligned : table.toNat%8=0
  domain : source.memaddrs=InitE.ordinaryDomain
  capLower : 2≤cap.toNat
  fields : ∀ entry∈scalarWrites table key cap,source.memory entry.1=.word entry.2

theorem ScalarEmpty.of_memory {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap : BitVec 64}
    (image : ScalarEmpty source table key cap) (domain : target.memaddrs=source.memaddrs)
    (memory : ∀ entry∈scalarWrites table key cap,target.memory entry.1=source.memory entry.1) :
    ScalarEmpty target table key cap := by
  refine ⟨image.geometry,image.aligned,domain.trans image.domain,image.capLower,?_⟩
  intro entry member
  exact (memory entry member).trans (image.fields entry member)

/-- Exact normal execution establishes a usable scalar empty-table image
and the allocator cursor beyond all three actual backing allocations. -/
theorem body_scalar_empty (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key cap : BitVec 64)
    (keyCell : source.locals.lookup (ofString "key_len")=some (.val (.word key)))
    (capCell : source.locals.lookup (ofString "cap")=some (.val (.word cap))) (atLeastTwo : 2≤cap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=.val (.word heap) ∧ ScalarEmpty post heap key cap ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word (scalarNextHeap heap key cap))) ∧
      PersistentNormalFrame source post heap := by
  obtain ⟨valueEq,funded,owned,tableRoom,keysRoom,nodesRoom,orderRoom,physical,clock,frame⟩:=
    body_scalar_returned source post heap key cap keyCell capCell atLeastTwo heapCell heapArena heapBound heapAligned arena value normal
  have memory:=LocalEffects.memory_of_erase (scalarFinish source heap key cap) post physical
  have domain:=congrArg PanSemStateFiniteExact.memaddrs physical
  change post.memaddrs=source.memaddrs at domain
  have globals:=congrArg PanSemStateFiniteExact.globals physical
  change post.globals=(scalarFinish source heap key cap).globals at globals
  refine ⟨valueEq,⟨scalar_geometry_of_room heap key cap owned tableRoom keysRoom nodesRoom orderRoom,heapAligned,domain.trans arena.domain,atLeastTwo,?_⟩,?_,frame⟩
  · intro entry member
    rw [memory]
    exact scalar_finish_field source heap key cap entry member
  · rw [globals]
    simp [scalarFinish,finishStored,putField,scalarFinalEntry,arrayEntry,QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,scalarNextHeap]

theorem scalar_write_before (table key cap : BitVec 64) (entry : BitVec 64×BitVec 64)
    (owned : AllocatedBytes.Arena table 88) (member : entry∈scalarWrites table key cap) :
    entry.1.toNat<table.toNat+88 := by
  have addresses : (scalarWrites table key cap).map Prod.fst=
      ([0#64,8#64,16#64,24#64,32#64,40#64,48#64,56#64,64#64,72#64,80#64] : List (BitVec 64)).map (fun offset=>table+offset):=rfl
  have present : entry.1∈(scalarWrites table key cap).map Prod.fst:=List.mem_map.mpr ⟨entry,member,rfl⟩
  rw [addresses] at present
  obtain ⟨offset,inside,same⟩:=List.mem_map.mp present
  have small : offset.toNat<88 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  have number : (table+offset).toNat=table.toNat+offset.toNat:=BitVec.toNat_add_of_lt (by have upper:=owned.upper; omega)
  rw [←same,number]
  omega

theorem ScalarEmpty.of_erase {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap : BitVec 64}
    (image : ScalarEmpty source table key cap) (same : LocalEffects.erase target=LocalEffects.erase source) :
    ScalarEmpty target table key cap := by
  have memory:=LocalEffects.memory_of_erase source target same
  have domain:=congrArg PanSemStateFiniteExact.memaddrs same
  change target.memaddrs=source.memaddrs at domain
  exact image.of_memory domain (by intros; rw [memory])

/-- Later persistent calls can retain the initialized header using their
actual earlier-memory frame; backing cells need no initialization premise. -/
theorem ScalarEmpty.of_persistent {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap heap : BitVec 64}
    (image : ScalarEmpty source table key cap) (before : table.toNat+88≤heap.toNat)
    (frame : PersistentMemoryFrame source target heap) : ScalarEmpty target table key cap := by
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame.metadata
  change target.memaddrs=source.memaddrs at domain
  apply image.of_memory (target:=target) domain
  intro entry member
  apply frame.memory entry.1
  have inside:=scalar_write_before table key cap entry image.geometry.table member
  omega

/-- A genuine ordinary global-result call preserves the exact empty
header image and returns the heap beyond all its backing arrays. -/
theorem global_scalar_empty (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (key cap heap : BitVec 64) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word key),.val (.word cap)]) (atLeastTwo : 2≤cap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (notHeap : ofString "heap_ptr"≠ofString name)
    (normal : evaluateHOLFiniteState source (.call (some (some (.global,ofString name),none)) (ofString "htab_new") arguments)=(none,post)) :
    ScalarEmpty post heap key cap ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word (scalarNextHeap heap key cap))) := by
  obtain ⟨callee,called,keyCell,capCell⟩:=word_pair_environment source.code.lookup (ofString "htab_new") (ofString "key_len") (ofString "cap")
    body .one key cap (by decide) (original_code source.code arena.code)
  obtain ⟨funded,child,value,bodyRun⟩:=CallNormal.assigned_callee_return source post (some (.global,ofString name)) (ofString "htab_new") arguments _
    body callee .one args called normal
  have enteredArena : CurrentStartup.ArenaState (callEntryStateHOLFinite source callee):=
    ⟨arena.scratch,arena.frame,arena.domain,arena.code⟩
  obtain ⟨answer,image,next,frame⟩:=body_scalar_empty (callEntryStateHOLFinite source callee) child heap key cap
    keyCell capCell atLeastTwo heapCell heapArena heapBound heapAligned enteredArena value bodyRun
  let raw:={child with locals:=source.locals}
  rw [answer] at bodyRun
  rw [evaluateHOLFiniteState_call,args] at normal
  simp only [called,if_neg (show source.clock≠0 by omega),bodyRun,shapeOfHOLExact,shapeEqHOL,↓reduceIte] at normal
  split at normal
  · have endpoint:=(congrArg Prod.snd normal).symm
    change post=setKvarHOLFinite .global (ofString name) (.val (.word heap)) raw at endpoint
    rw [endpoint]
    exact ⟨image.of_memory rfl (by intros; rfl),(putGlobal.lookup_other raw name heap _ notHeap).trans next⟩
  · cases normal

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.scalar_header_normal
#print axioms InitECandidate.Solver.Input.CurrentTable.New.scalar_array_normal
#print axioms InitECandidate.Solver.Input.CurrentTable.New.body_scalar_returned
#print axioms InitECandidate.Solver.Input.CurrentTable.New.scalar_finish_memory
#print axioms InitECandidate.Solver.Input.CurrentTable.New.scalar_writes_distinct
#print axioms InitECandidate.Solver.Input.CurrentTable.New.scalar_finish_field
#print axioms InitECandidate.Solver.Input.CurrentTable.New.scalar_geometry_of_room
#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarEmpty.of_memory
#print axioms InitECandidate.Solver.Input.CurrentTable.New.body_scalar_empty

#print axioms InitECandidate.Solver.Input.CurrentTable.New.scalar_write_before
#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarEmpty.of_erase
#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarEmpty.of_persistent
#print axioms InitECandidate.Solver.Input.CurrentTable.New.global_scalar_empty
