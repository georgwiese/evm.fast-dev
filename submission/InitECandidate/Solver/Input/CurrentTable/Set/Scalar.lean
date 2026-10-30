import InitECandidate.Solver.Input.CurrentTable.NewScalarImage
import InitECandidate.Solver.Input.CurrentTable.NewNode.Call
import InitECandidate.Solver.Input.CurrentTable.NewLeaf.Program
import InitECandidate.Solver.Input.CopyAnyCost
import InitECandidate.Solver.Input.ClockCost
import InitECandidate.Solver.Input.ClockCostCurrent
import InitECandidate.Solver.Input.CurrentTable.ScalarLookup
import InitECandidate.Solver.Input.CurrentTable.Set.Guards
import InitECandidate.Solver.Input.WordTripleEnvironment
import InitECandidate.Solver.Input.ClockCostCurrentScoped
import InitECandidate.Solver.Input.CallResume
import InitECandidate.Solver.Input.NoReturnIgnored
import InitECandidate.Solver.Input.CurrentTable.CellGeometry
import InitECandidate.Solver.Input.CurrentTable.FieldFrames

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix

/-- Natural extents of the real padded scalar key width. -/
theorem scalar_stride_numbers (key : BitVec 64) (small : key.toNat≤60) :
    key.toNat≤(strideWord key).toNat ∧ (strideWord key).toNat≤64 ∧ (strideWord key).toNat%8=0 := by
  have same : strideWord key=PersistentAlloc.rounded 0#64 key:=by simp [strideWord,PersistentAlloc.rounded]
  have number:=PersistentAlloc.rounded_nat 0#64 key (by change 0+key.toNat+7<2^64; omega)
  rw [←same] at number
  change (strideWord key).toNat=(0+key.toNat+7)/8*8 at number
  omega

theorem scalar_array_numbers (key cap : BitVec 64) (keySmall : key.toNat≤60) (capSmall : cap.toNat≤2^32) :
    (scalarKeyAmount key cap).toNat=(cap.toNat+1)*(strideWord key).toNat ∧
      (size32 cap).toNat=32*(cap.toNat+1) ∧ (size8 cap).toNat=8*(cap.toNat+1) := by
  have next : (cap+1#64).toNat=cap.toNat+1:=by
    rw [BitVec.toNat_add_of_lt (by change cap.toNat+1<2^64; omega)]
    rfl
  have strideBound:=(scalar_stride_numbers key keySmall).2.1
  have productBound : (cap.toNat+1)*(strideWord key).toNat≤(2^32+1)*64:=
    Nat.mul_le_mul (by omega) strideBound
  refine ⟨?_,(size_numbers cap capSmall).1,(size_numbers cap capSmall).2⟩
  rw [scalarKeyAmount,BitVec.toNat_mul,next,Nat.mod_eq_of_lt (by omega)]

def scalarKeyDestination (table key : BitVec 64) : BitVec 64:=keysPointer table+strideWord key

def OutsideScalar (table key cap query : BitVec 64) : Prop :=
  query.toNat<table.toNat ∨ (scalarNextHeap table key cap).toNat≤query.toNat

/-- The first copied key lies in the actual allocated scalar key array,
with its complete padded room before the node array. -/
theorem ScalarGeometry.first_key_copy {table key cap : BitVec 64} (geometry : ScalarGeometry table key cap)
    (keySmall : key.toNat≤60) (capSmall : cap.toNat≤2^32) (capLower : 2≤cap.toNat) :
    AllocatedBytes.Arena (scalarKeyDestination table key) key.toNat ∧
      (scalarKeyDestination table key).toNat%8=0 ∧
      table.toNat+88≤(scalarKeyDestination table key).toNat ∧
      (scalarKeyDestination table key).toNat+key.toNat≤(scalarNodesPointer table key cap).toNat := by
  obtain ⟨widthLower,widthUpper,widthAligned⟩:=scalar_stride_numbers key keySmall
  have numbers:=scalar_array_numbers key cap keySmall capSmall
  have twice : 2*(strideWord key).toNat≤(cap.toNat+1)*(strideWord key).toNat:=
    Nat.mul_le_mul_right (strideWord key).toNat (by omega)
  have room : (strideWord key).toNat+key.toNat≤(scalarKeyAmount key cap).toNat:=by rw [numbers.1]; omega
  have keysUpper:=geometry.keys.upper
  have number : (scalarKeyDestination table key).toNat=(keysPointer table).toNat+(strideWord key).toNat:=by
    apply BitVec.toNat_add_of_lt
    omega
  have owned : AllocatedBytes.Arena (byteAddress (keysPointer table) (strideWord key).toNat) key.toNat:=
    AllocatedBytes.Arena.subrange (keysPointer table) (scalarKeyAmount key cap).toNat (strideWord key).toNat key.toNat geometry.keys room
  have actualOwned : AllocatedBytes.Arena (scalarKeyDestination table key) key.toNat:=by
    simpa [scalarKeyDestination,byteAddress,BitVec.ofNat_toNat,BitVec.setWidth_eq] using owned
  refine ⟨actualOwned,?_,?_,?_⟩
  · rw [number]
    have aligned:=geometry.keysAligned
    omega
  · rw [number]
    have before:=geometry.tableBefore
    omega
  · rw [number]
    have before:=geometry.keysBefore
    omega

/-- The actual key copy protects every word outside this constructor's
complete region, including a different table's metadata and backing arrays. -/
theorem ScalarGeometry.first_key_copy_away {table key cap : BitVec 64} (geometry : ScalarGeometry table key cap)
    (keySmall : key.toNat≤60) (capSmall : cap.toNat≤2^32) (capLower : 2≤cap.toNat)
    (query : BitVec 64) (outside : OutsideScalar table key cap query) :
    CopyGeneral.Away (scalarKeyDestination table key) query key.toNat := by
  obtain ⟨owned,aligned,afterHeader,beforeNodes⟩:=geometry.first_key_copy keySmall capSmall capLower
  rcases outside with before|after
  · exact CopyGeneral.Away.after _ query _ aligned (by have upper:=owned.upper; omega) (by omega)
  · apply CopyGeneral.Away.before _ query _ (scalarNextHeap table key cap).toNat
    · have first:=geometry.nodesBefore
      have second:=geometry.orderBefore
      omega
    · have bound:=geometry.endBound
      omega
    · exact after

theorem ScalarGeometry.scalar_header_away {table key cap : BitVec 64} (geometry : ScalarGeometry table key cap)
    (capSmall : cap.toNat≤2^32) (node : BitVec 64) (inside : node.toNat≤cap.toNat)
    (offset field : Nat) (small : offset<32) (fieldInside : field<88) :
    table+BitVec.ofNat 64 field≠FindLeaf.cell (scalarNodesPointer table key cap) node offset := by
  have nodes : AllocatedBytes.Arena (scalarNodesPointer table key cap) (32*(cap.toNat+1)):=by
    simpa only [(size_numbers cap capSmall).1] using geometry.nodes
  have number:=cell_number _ node cap offset nodes inside small
  have header:=byteAddress_toNat table field (by have upper:=geometry.table.upper; omega)
  change (table+BitVec.ofNat 64 field).toNat=table.toNat+field at header
  have first:=geometry.tableBefore
  have second:=geometry.keysBefore
  intro same
  have equal:=congrArg BitVec.toNat same
  rw [header,number] at equal
  omega

theorem ScalarGeometry.node_in_scalar {table key cap : BitVec 64} (geometry : ScalarGeometry table key cap)
    (capSmall : cap.toNat≤2^32) (node : BitVec 64) (inside : node.toNat≤cap.toNat) (offset : Nat) (small : offset<32) :
    table.toNat≤(FindLeaf.cell (scalarNodesPointer table key cap) node offset).toNat ∧
      (FindLeaf.cell (scalarNodesPointer table key cap) node offset).toNat<(scalarNextHeap table key cap).toNat := by
  have nodes : AllocatedBytes.Arena (scalarNodesPointer table key cap) (32*(cap.toNat+1)):=by
    simpa only [(size_numbers cap capSmall).1] using geometry.nodes
  have number:=cell_number _ node cap offset nodes inside small
  have tableBefore:=geometry.tableBefore
  have keysBefore:=geometry.keysBefore
  have nodesBefore:=geometry.nodesBefore
  have orderBefore:=geometry.orderBefore
  rw [(size_numbers cap capSmall).1] at nodesBefore
  constructor <;> rw [number] <;> omega

theorem ScalarGeometry.order_in_scalar {table key cap : BitVec 64} (geometry : ScalarGeometry table key cap)
    (capSmall : cap.toNat≤2^32) (position : BitVec 64) (inside : position.toNat≤cap.toNat) :
    table.toNat≤(slot (scalarOrderPointer table key cap) position 8).toNat ∧
      (slot (scalarOrderPointer table key cap) position 8).toNat<(scalarNextHeap table key cap).toNat := by
  have order : AllocatedBytes.Arena (scalarOrderPointer table key cap) (8*(cap.toNat+1)):=by
    simpa only [(size_numbers cap capSmall).2] using geometry.order
  have number:=slot_number _ position cap 8 order inside
  have tableBefore:=geometry.tableBefore
  have keysBefore:=geometry.keysBefore
  have nodesBefore:=geometry.nodesBefore
  have orderBefore:=geometry.orderBefore
  rw [(size_numbers cap capSmall).2] at orderBefore
  constructor <;> rw [number] <;> omega

theorem OutsideScalar.ne_address {table key cap query address : BitVec 64} (outside : OutsideScalar table key cap query)
    (lower : table.toNat≤address.toNat) (upper : address.toNat<(scalarNextHeap table key cap).toNat) : query≠address := by
  intro same
  have equal:=congrArg BitVec.toNat same
  rcases outside with before|after <;> omega

/-- Actual scalar-table write footprint, independent of caller locals and
clock. The complete table region includes all backing allocations. -/
structure ScalarFrame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap : BitVec 64) : Prop where
  fields : MemoryMetadata.erase target=MemoryMetadata.erase source
  memory : ∀ query : BitVec 64,OutsideScalar table key cap query→target.memory query=source.memory query

theorem ScalarFrame.of_erase {source target source' target' : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap : BitVec 64}
    (frame : ScalarFrame source target table key cap) (entry : LocalEffects.erase source'=LocalEffects.erase source)
    (exit : LocalEffects.erase target'=LocalEffects.erase target) : ScalarFrame source' target' table key cap := by
  have sourceMemory:=LocalEffects.memory_of_erase source source' entry
  have targetMemory:=LocalEffects.memory_of_erase target target' exit
  exact ⟨(MemoryMetadata.of_frame exit).trans (frame.fields.trans (MemoryMetadata.of_frame entry).symm),
    by intro query outside; rw [sourceMemory,targetMemory]; exact frame.memory query outside⟩

theorem ScalarFrame.store_inside {origin source target : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap : BitVec 64}
    (frame : ScalarFrame origin source table key cap) (destination expression : ExpHOL 64) (address value : BitVec 64)
    (addressRead : QueryBranch.eval source destination=some (.val (.word address)))
    (valueRead : QueryBranch.eval source expression=some (.val (.word value)))
    (lower : table.toNat≤address.toNat) (upper : address.toNat<(scalarNextHeap table key cap).toNat)
    (normal : evaluateHOLFiniteState source (.store destination expression)=(none,target)) : ScalarFrame origin target table key cap := by
  obtain ⟨mapped,endpoint⟩:=word_store_normal source target destination expression address value addressRead valueRead normal
  refine ⟨?_,?_⟩
  · rw [endpoint]
    exact frame.fields
  · intro query outside
    rw [endpoint]
    exact (if_neg (outside.ne_address lower upper)).trans (frame.memory query outside)

end InitECandidate.Solver.Input.CurrentTable.New

namespace InitECandidate.Solver.Input.CurrentTable.NewNode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The actual scalar constructor already supplies the first no-grow node
at every current key width, including20byte account-access keys. -/
theorem from_scalar_empty {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap : BitVec 64}
    (image : New.ScalarEmpty source table key cap) : Context source table 1#64 cap := by
  exact ⟨image.domain,image.geometry.table,image.aligned,
    image.fields (table+72#64,0#64) (by simp [New.scalarWrites]),image.fields (table+64#64,1#64) (by simp [New.scalarWrites]),
    image.fields (table+80#64,cap) (by simp [New.scalarWrites]),by have lower:=image.capLower; change 1≤cap.toNat; omega⟩

end InitECandidate.Solver.Input.CurrentTable.NewNode

namespace InitECandidate.Solver.Input.CurrentTable.NewLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Only actual scalar header fields read before the real key copy. The
node allocator may update the next-index word independently. -/
structure ScalarFields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key : BitVec 64) : Prop where
  domain : source.memaddrs=InitE.ordinaryDomain
  arena : AllocatedBytes.Arena table 88
  aligned : table.toNat%8=0
  length : source.memory table=.word key
  stride : source.memory (table+8#64)=.word (New.strideWord key)
  keys : source.memory (table+32#64)=.word (New.keysPointer table)

theorem ScalarFields.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {table key : BitVec 64}
    (fields : ScalarFields source table key) (same : LocalEffects.erase target=LocalEffects.erase source) : ScalarFields target table key := by
  have memory:=LocalEffects.memory_of_erase source target same
  have domain:=congrArg PanSemStateFiniteExact.memaddrs same
  change target.memaddrs=source.memaddrs at domain
  exact ⟨domain.trans fields.domain,fields.arena,fields.aligned,by rw [memory]; exact fields.length,
    by rw [memory]; exact fields.stride,by rw [memory]; exact fields.keys⟩

theorem ScalarFields.after_next {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap : BitVec 64}
    (image : New.ScalarEmpty source table key cap) : ScalarFields (New.putField source table 64 2#64) table key := by
  have different (offset : BitVec 64) (other : offset≠64#64) : table+offset≠table+64#64:=by
    intro same
    exact other ((BitVec.add_right_inj table).mp same)
  refine ⟨image.domain,image.geometry.table,image.aligned,?_,?_,?_⟩
  · have cell:=image.fields (table+0#64,key) (by simp [New.scalarWrites])
    simpa [New.putField,StoreWord.put,different 0#64 (by decide)] using cell
  · have cell:=image.fields (table+8#64,New.strideWord key) (by simp [New.scalarWrites])
    simpa [New.putField,StoreWord.put,different 8#64 (by decide)] using cell
  · have cell:=image.fields (table+32#64,New.keysPointer table) (by simp [New.scalarWrites])
    simpa [New.putField,StoreWord.put,different 32#64 (by decide)] using cell

/-- All original leaf/order/count stores and the final return are finite
straight-line source work, including failed reads and stores. -/
theorem scalar_tail_quiet (code) : QuietClock.Preserves code afterCopy := by
  rw [shapes.2.2.2.2.1,shapes.2.2.2.2.2.1,shapes.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.1,
    shapes.2.2.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.2.2.2.2]
  repeat first | apply QuietClock.declared | apply QuietClock.sequence | apply QuietClock.store | apply QuietClock.returned

def scalarCopyEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key : BitVec 64) :=
  bind (bind source "klen" key) "stride" (New.strideWord key)

/-- Actual scalar copy arguments after the two real declarations. -/
theorem scalar_copy_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key pointer : BitVec 64)
    (fields : ScalarFields source table key)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (nodeCell : source.locals.lookup (ofString "n")=some (.val (.word 1#64)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer))) :
    evalListHOLFinite (scalarCopyEntry source key) (h:=fun address=>Classical.propDecidable ((scalarCopyEntry source key).memaddrs address)) copyArguments=
      some (CopyGeneral.values (New.keysPointer table+New.strideWord key) pointer key.toNat) := by
  let first:=bind source "klen" key
  let current:=scalarCopyEntry source key
  have firstTable : first.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other source "klen" "t" key (by decide)).trans tableCell
  have currentTable : current.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other first "stride" "t" (New.strideWord key) (by decide)).trans firstTable
  have currentNode : current.locals.lookup (ofString "n")=some (.val (.word 1#64)):=
    (bind_lookup_other first "stride" "n" (New.strideWord key) (by decide)).trans ((bind_lookup_other source "klen" "n" key (by decide)).trans nodeCell)
  have currentKey : current.locals.lookup (ofString "key")=some (.val (.word pointer)):=
    (bind_lookup_other first "stride" "key" (New.strideWord key) (by decide)).trans ((bind_lookup_other source "klen" "key" key (by decide)).trans keyCell)
  have currentLength : current.locals.lookup (ofString "klen")=some (.val (.word key)):=
    (bind_lookup_other first "stride" "klen" (New.strideWord key) (by decide)).trans (bind_lookup_same _ _ _)
  have currentStride : current.locals.lookup (ofString "stride")=some (.val (.word (New.strideWord key))):=bind_lookup_same _ _ _
  have keysRead:=NewNode.field_read current table (New.keysPointer table) 32 fields.domain fields.arena fields.aligned (by decide) (by decide) currentTable fields.keys
  have destinationRead : eval current (.op .add [.load .one (NewNode.address 32),.panop .mul [localVar "n",localVar "stride"]])=
      some (.val (.word (New.keysPointer table+New.strideWord key))):=by
    simp only [eval] at keysRead ⊢
    rw [evalHOLExact]
    simp only [evalListHOLExact,keysRead]
    simp [evalHOLExact,evalListHOLExact,localVar,currentNode,currentStride,valueIsWord,valueWord,panOpHOL,wordOpHOL,wordOp]
  have args : evalListHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) copyArguments=
      some (CopyGeneral.values (New.keysPointer table+New.strideWord key) pointer key.toNat):=by
    have number : BitVec.ofNat 64 key.toNat=key:=by simp [BitVec.ofNat_toNat,BitVec.setWidth_eq]
    simp only [eval] at destinationRead
    simp only [copyArguments,CopyGeneral.values,evalListHOLFinite,evalListHOLExact,destinationRead]
    simp [evalHOLExact,localVar,currentKey,currentLength,number]
  exact args

theorem scalar_after_node_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key pointer : BitVec 64)
    (fields : ScalarFields source table key) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (nodeCell : source.locals.lookup (ofString "n")=some (.val (.word 1#64)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer))) (small : key.toNat+32<2^64) :
    source.clock-(evaluateHOLFiniteState source afterNode).2.clock≤CopyAny.price key.toNat+1 := by
  have lengthRead:=NewNode.field_read source table key 0 fields.domain fields.arena fields.aligned (by decide) (by decide) tableCell
    (by simpa using fields.length)
  rw [shapes.2.1]
  apply ClockCost.declared_current source "klen" _ key _ (CopyAny.price key.toNat+1) lengthRead
  let first:=bind source "klen" key
  have firstTable : first.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other source "klen" "t" key (by decide)).trans tableCell
  have strideRead:=NewNode.field_read first table (New.strideWord key) 8 fields.domain fields.arena fields.aligned (by decide) (by decide) firstTable fields.stride
  rw [shapes.2.2.1]
  apply ClockCost.declared_current first "stride" _ (New.strideWord key) _ (CopyAny.price key.toNat+1) strideRead
  let current:=scalarCopyEntry source key
  have args:=scalar_copy_arguments source table key pointer fields tableCell nodeCell keyCell
  rw [shapes.2.2.2.1]
  have front:=CopyAny.call_cost current copyArguments (New.keysPointer table+New.strideWord key) pointer key.toNat small args
    (CopyGeneral.original_code current.code installed)
  simpa only [current,scalarCopyEntry,first,Nat.add_zero] using ClockCost.sequence_current current _ afterCopy (CopyAny.price key.toNat+1) 0 front
    (ClockCost.of_quiet current.code afterCopy (scalar_tail_quiet current.code))

/-- All outcomes of the real first leaf construction at its actual scalar
key width. Copy failure and short clocks need no additional success premise. -/
theorem scalar_empty_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer : BitVec 64)
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer))) (small : key.toNat+32<2^64) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤CopyAny.price key.toNat+2 := by
  let output:=evaluateHOLFiniteState source body
  have actual : evaluateHOLFiniteState source body=(output.1,output.2):=rfl
  rw [shapes.1] at actual
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "t"]=some [.val (.word table)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,tableCell]
  rcases NewNode.scoped_trace source output.2 table 1#64 cap (NewNode.from_scalar_empty image) installed "n" [localVar "t"] afterNode args output.1 actual with stopped|reached
  · change source.clock-output.2.clock≤CopyAny.price key.toNat+2
    have bound:=stopped.1
    omega
  · obtain ⟨target,inner,frame,forward,price,continued,endpoint⟩:=reached
    let current:=CallNormal.continuationEntry source target "n" (.val (.word 1#64))
    have fields : ScalarFields current table key:=(ScalarFields.after_next image).of_frame frame
    have currentTable : current.locals.lookup (ofString "t")=some (.val (.word table)):=
      (CallNormal.continuation_lookup_other source target "n" "t" (.val (.word 1#64)) (by decide)).trans tableCell
    have currentKey : current.locals.lookup (ofString "key")=some (.val (.word pointer)):=
      (CallNormal.continuation_lookup_other source target "n" "key" (.val (.word 1#64)) (by decide)).trans keyCell
    have code:=congrArg PanSemStateFiniteExact.code frame
    change current.code=source.code at code
    have cost:=scalar_after_node_cost current table key pointer fields (by rw [code]; exact installed)
      currentTable (CallNormal.continuation_lookup_same source target "n" (.val (.word 1#64))) currentKey small
    rw [continued] at cost
    change current.clock-inner.clock≤CopyAny.price key.toNat+1 at cost
    have entryClock : current.clock=target.clock:=rfl
    have exitClock : output.2.clock=inner.clock:=by rw [endpoint] <;> rfl
    change source.clock-output.2.clock≤CopyAny.price key.toNat+2
    omega

def scalarNodeEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) :=
  bind (New.putField {source with clock:=source.clock-1} table 64 2#64) "n" 1#64

/-- The actual funded first node call resumes the unchanged leaf body with
its real metadata increment and scalar node index. Every later outcome is
left as the original evaluator continuation. -/
theorem scalar_prefix_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap : BitVec 64)
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table))) (funded : 1≤source.clock) :
    evaluateHOLFiniteState source body=
      let output:=evaluateHOLFiniteState (scalarNodeEntry source table) afterNode
      (output.1,restore source "n" output.2) := by
  obtain ⟨callee,called,tCell⟩:=word_environment source.code.lookup (ofString "htab_new_node") (ofString "t")
    NewNode.body .one table (NewNode.original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have ready : NewNode.Context entry table 1#64 cap:=(NewNode.from_scalar_empty image).of_frame rfl
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "t"]=some [.val (.word table)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,tableCell]
  have run:=CallNormal.return_execute source (NewNode.returnedState entry table 1#64) "n" .one (ofString "htab_new_node")
    [localVar "t"] [.val (.word table)] NewNode.body afterNode callee .one (.val (.word 1#64)) args called funded
    (ready.execute tCell) (by simp [shapeOfHOLExact,shapeEqHOL])
  have resumed : CallNormal.continuationEntry source (NewNode.returnedState entry table 1#64) "n" (.val (.word 1#64))=scalarNodeEntry source table:=rfl
  rw [shapes.1,run,resumed]

/-- A real normally returned leaf exposes the same canonical copy entry.
Its node allocation and declarations provide their own funding/read facts. -/
theorem scalar_copy_trace {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap : BitVec 64}
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    1≤source.clock ∧ ∃ inner,evaluateHOLFiniteState (scalarCopyEntry (scalarNodeEntry source table) key) copyPhase=(some (.returned value),inner) ∧
      LocalEffects.erase post=LocalEffects.erase inner ∧ post.clock=inner.clock := by
  obtain ⟨callee,called,tCell⟩:=word_environment source.code.lookup (ofString "htab_new_node") (ofString "t")
    NewNode.body .one table (NewNode.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "t"]=some [.val (.word table)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,tableCell]
  have expanded:=normal
  rw [shapes.1] at expanded
  have funded:=(CallNormal.scoped_normal source post "n" .one (ofString "htab_new_node") [localVar "t"] [.val (.word table)] NewNode.body afterNode callee .one args called value expanded).1
  let current:=scalarNodeEntry source table
  let output:=evaluateHOLFiniteState current afterNode
  have actual:=scalar_prefix_execute source table key cap image installed tableCell funded
  have observed:=congrArg Prod.fst (normal.symm.trans actual)
  have endpoint:=congrArg Prod.snd (normal.symm.trans actual)
  change post=restore source "n" output.2 at endpoint
  have run : evaluateHOLFiniteState current afterNode=(some (.returned value),output.2):=Prod.ext observed.symm rfl
  have fields : ScalarFields current table key:=(ScalarFields.after_next image).of_frame rfl
  have currentTable : current.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other _ "n" "t" 1#64 (by decide)).trans tableCell
  have lengthRead:=NewNode.field_read current table key 0 fields.domain fields.arena fields.aligned (by decide) (by decide) currentTable (by simpa using fields.length)
  rw [shapes.2.1] at run
  obtain ⟨middle,continued,middleEq⟩:=ScalarScope.declare_trace current output.2 "klen" _ key afterLength (some (.returned value)) lengthRead run
  let first:=bind current "klen" key
  have firstTable : first.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other _ "klen" "t" key (by decide)).trans currentTable
  have strideRead:=NewNode.field_read first table (New.strideWord key) 8 fields.domain fields.arena fields.aligned (by decide) (by decide) firstTable fields.stride
  rw [shapes.2.2.1] at continued
  obtain ⟨inner,copyRun,innerEq⟩:=ScalarScope.declare_trace first middle "stride" _ (New.strideWord key) copyPhase (some (.returned value)) strideRead continued
  exact ⟨funded,inner,copyRun,by rw [endpoint,middleEq,innerEq]; rfl,by rw [endpoint,middleEq,innerEq]; rfl⟩

/-- Actual copy completion supplies its span frame, saved locals and real
remaining leaf stores. No successful memcpy is supplied as an entry premise. -/
theorem scalar_copied_returned {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer : BitVec 64}
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer))) (small : key.toNat+32<2^64)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ copied inner,Copy32Span.Frame (scalarCopyEntry (scalarNodeEntry source table) key) copied (New.scalarKeyDestination table key) key.toNat ∧
      copied.locals=(scalarCopyEntry (scalarNodeEntry source table) key).locals ∧
      evaluateHOLFiniteState copied afterCopy=(some (.returned value),inner) ∧
      LocalEffects.erase post=LocalEffects.erase inner ∧ post.clock=inner.clock := by
  obtain ⟨funded,middle,copyRun,scope,clock⟩:=scalar_copy_trace image installed tableCell value normal
  rw [shapes.2.2.2.1] at copyRun
  let node:=scalarNodeEntry source table
  let current:=scalarCopyEntry node key
  obtain ⟨copied,called,remaining⟩:=sequence_returned current middle (.call (some (none,none)) (ofString "memcpy") copyArguments) afterCopy value
    (NoReturn.ignored_call (ofString "memcpy") copyArguments current) copyRun
  have fields : ScalarFields node table key:=(ScalarFields.after_next image).of_frame rfl
  have currentTable : node.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other _ "n" "t" 1#64 (by decide)).trans tableCell
  have currentKey : node.locals.lookup (ofString "key")=some (.val (.word pointer)):=
    (bind_lookup_other _ "n" "key" 1#64 (by decide)).trans keyCell
  have args:=scalar_copy_arguments node table key pointer fields currentTable (bind_lookup_same _ _ _) currentKey
  obtain ⟨frame,locals⟩:=CopyAny.call_span_normal current copied (New.keysPointer table+New.strideWord key) pointer key.toNat small copyArguments args installed called
  exact ⟨copied,middle,frame,locals,remaining,scope,clock⟩

structure ScalarLocals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key base node value : BitVec 64) : Prop where
  tableCell : source.locals.lookup (ofString "t") = some (.val (.word table))
  baseCell : source.locals.lookup (ofString "nodes") = some (.val (.word base))
  nodeCell : source.locals.lookup (ofString "n") = some (.val (.word node))
  valueCell : source.locals.lookup (ofString "value") = some (.val (.word value))
  lengthCell : source.locals.lookup (ofString "klen") = some (.val (.word key))

theorem ScalarLocals.with_memory {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table key base node value : BitVec 64}
    (locals : ScalarLocals source table key base node value) (memory : BitVec 64 → HolWordLab 64) :
    ScalarLocals {source with memory := memory} table key base node value :=
  ⟨locals.tableCell,locals.baseCell,locals.nodeCell,locals.valueCell,locals.lengthCell⟩

theorem ScalarLocals.with_position {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table key base node value : BitVec 64}
    (locals : ScalarLocals source table key base node value) (pos : BitVec 64) : ScalarLocals (bind source "pos" pos) table key base node value := by
  exact ⟨(bind_lookup_other _ "pos" "t" pos (by decide)).trans locals.tableCell,
    (bind_lookup_other _ "pos" "nodes" pos (by decide)).trans locals.baseCell,
    (bind_lookup_other _ "pos" "n" pos (by decide)).trans locals.nodeCell,
    (bind_lookup_other _ "pos" "value" pos (by decide)).trans locals.valueCell,
    (bind_lookup_other _ "pos" "klen" pos (by decide)).trans locals.lengthCell⟩

def scalarPutOrder (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pos node : BitVec 64) :=
  {source with memory := StoreWord.put source.memory (slot (New.scalarOrderPointer table key cap) pos 8) node}

def scalarTailStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap node pos : BitVec 64) :=
  New.putField (scalarPutOrder
    (putNode (putNode source (New.scalarNodesPointer table key cap) node 16 pos) (New.scalarNodesPointer table key cap) node 24 (key*8#64))
    table key cap pos node) table 24 (pos+1#64)

theorem scalar_order_address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pos : BitVec 64)
    (domain : source.memaddrs = InitE.ordinaryDomain) (geometry : New.ScalarGeometry table key cap) (aligned : table.toNat%8 = 0)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word pos)))
    (orderCell : source.memory (table+48#64) = .word (New.scalarOrderPointer table key cap)) :
    eval source orderAddress = some (.val (.word (slot (New.scalarOrderPointer table key cap) pos 8))) := by
  have orderRead := NewNode.field_read source table (New.scalarOrderPointer table key cap) 48 domain geometry.table aligned
    (by decide) (by decide) tableCell orderCell
  simp only [eval] at orderRead ⊢
  rw [orderAddress,evalHOLExact]
  simp only [evalListHOLExact,orderRead]
  simp [evalHOLExact,evalListHOLExact,localVar,posCell,valueIsWord,valueWord,panOpHOL,wordOpHOL,wordOp,slot]

/-- The original leaf tail stores the insertion position, leaf marker,
order-array entry and incremented count, and returns the allocated index. -/
theorem scalar_tail_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap node pos value : BitVec 64)
    (domain : source.memaddrs = InitE.ordinaryDomain) (geometry : New.ScalarGeometry table key cap) (aligned : table.toNat%8 = 0)
    (capSmall : cap.toNat≤2^32) (inside : node.toNat ≤ cap.toNat) (posInside : pos.toNat ≤ cap.toNat)
    (locals : ScalarLocals source table key (New.scalarNodesPointer table key cap) node value)
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word pos)))
    (orderCell : source.memory (table+48#64) = .word (New.scalarOrderPointer table key cap)) :
    evaluateHOLFiniteState source afterPosition =
      (some (.returned (.val (.word node))),emptyLocalsHOLFinite (scalarTailStored source table key cap node pos)) := by
  have nodeArray : AllocatedBytes.Arena (New.scalarNodesPointer table key cap) (32*(cap.toNat+1)):=by
    simpa only [(New.size_numbers cap capSmall).1] using geometry.nodes
  have orderArray : AllocatedBytes.Arena (New.scalarOrderPointer table key cap) (8*(cap.toNat+1)):=by
    simpa only [(New.size_numbers cap capSmall).2] using geometry.order
  let base := New.scalarNodesPointer table key cap
  let one := putNode source base node 16 pos
  let two := putNode one base node 24 (key*8#64)
  let three := scalarPutOrder two table key cap pos node
  have first := store_node source base node cap pos 16 (localVar "pos") domain nodeArray geometry.nodesAligned inside
    (by decide) (by decide) locals.baseCell locals.nodeCell (Request.local_word source "pos" pos posCell)
  have marker : eval one (.panop .mul [localVar "klen",.const 8#64]) = some (.val (.word (key*8#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,locals.lengthCell,panOpHOL,valueIsWord,valueWord,one,putNode]
  have second := store_node one base node cap (key*8#64) 24 _ domain nodeArray geometry.nodesAligned inside
    (by decide) (by decide) locals.baseCell locals.nodeCell marker
  have header : two.memory (table+48#64) = .word (New.scalarOrderPointer table key cap) := by
    have away16 := geometry.scalar_header_away capSmall node inside 16 48 (by decide) (by decide)
    have away24 := geometry.scalar_header_away capSmall node inside 24 48 (by decide) (by decide)
    change table+48#64 ≠ FindLeaf.cell base node 16 at away16
    change table+48#64 ≠ FindLeaf.cell base node 24 at away24
    change StoreWord.put (StoreWord.put source.memory (FindLeaf.cell base node 16) pos) (FindLeaf.cell base node 24) (key*8#64) (table+48#64) = _
    simp only [StoreWord.put,if_neg away16,if_neg away24]
    exact orderCell
  have orderRead := scalar_order_address_read two table key cap pos domain geometry aligned locals.tableCell posCell header
  have mapped := AllocatedBytes.word_mapped two (slot (New.scalarOrderPointer table key cap) pos 8) 8 0 domain
    (slot_arena _ pos cap 8 orderArray posInside) (by decide)
    (slot_aligned (New.scalarOrderPointer table key cap) pos cap 8 orderArray posInside geometry.orderAligned (by decide)) (by decide)
  have third := StoreWord.execute two orderAddress (localVar "n") (slot (New.scalarOrderPointer table key cap) pos 8) node
    orderRead (Request.local_word two "n" node locals.nodeCell) (by simpa [byteAddress] using mapped)
  change evaluateHOLFiniteState two (.store orderAddress (localVar "n")) = (none,three) at third
  have countRead : eval three (.op .add [localVar "pos",.const 1#64]) = some (.val (.word (pos+1#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,three,scalarPutOrder,two,one,putNode,posCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have fourth := New.store_field three table (pos+1#64) 24 _ domain geometry.table aligned (by decide) (by decide) locals.tableCell countRead
  change evaluateHOLFiniteState three (.store (NewNode.address 24) (.op .add [localVar "pos",.const 1#64])) = _ at fourth
  rw [shapes.2.2.2.2.2.2.2.2.1,evaluateHOLFiniteState_seq_line780,first]
  simp only
  rw [shapes.2.2.2.2.2.2.2.2.2.1,evaluateHOLFiniteState_seq_line780,second]
  simp only
  rw [shapes.2.2.2.2.2.2.2.2.2.2.1,evaluateHOLFiniteState_seq_line780,third]
  simp only
  rw [shapes.2.2.2.2.2.2.2.2.2.2.2,evaluateHOLFiniteState_seq_line780,fourth]
  simp [evaluateHOLFiniteState_return,evalHOLExact,localVar,New.putField,scalarPutOrder,putNode,locals.nodeCell,
    scalarTailStored,three,two,one,base,shapeOfHOLExact,sizeOfShapeWithContextHOL]

def scalarStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap node pos value : BitVec 64) :=
  scalarTailStored (putNode (putNode source (New.scalarNodesPointer table key cap) node 0 0#64) (New.scalarNodesPointer table key cap) node 8 value)
    table key cap node pos

def scalarStoresReturned (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap node pos value : BitVec 64) :=
  restore (putNode (putNode source (New.scalarNodesPointer table key cap) node 0 0#64) (New.scalarNodesPointer table key cap) node 8 value) "pos"
    (emptyLocalsHOLFinite (scalarTailStored
      (bind (putNode (putNode source (New.scalarNodesPointer table key cap) node 0 0#64) (New.scalarNodesPointer table key cap) node 8 value) "pos" pos)
      table key cap node pos))

theorem scalar_stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap node pos value : BitVec 64)
    (domain : source.memaddrs = InitE.ordinaryDomain) (geometry : New.ScalarGeometry table key cap) (aligned : table.toNat%8 = 0)
    (capSmall : cap.toNat≤2^32) (inside : node.toNat ≤ cap.toNat) (posInside : pos.toNat ≤ cap.toNat)
    (locals : ScalarLocals source table key (New.scalarNodesPointer table key cap) node value)
    (countCell : source.memory (table+24#64) = .word pos)
    (orderCell : source.memory (table+48#64) = .word (New.scalarOrderPointer table key cap)) :
    evaluateHOLFiniteState source stores =
      (some (.returned (.val (.word node))),scalarStoresReturned source table key cap node pos value) := by
  have nodeArray : AllocatedBytes.Arena (New.scalarNodesPointer table key cap) (32*(cap.toNat+1)):=by
    simpa only [(New.size_numbers cap capSmall).1] using geometry.nodes
  have orderArray : AllocatedBytes.Arena (New.scalarOrderPointer table key cap) (8*(cap.toNat+1)):=by
    simpa only [(New.size_numbers cap capSmall).2] using geometry.order
  let base := New.scalarNodesPointer table key cap
  let one := putNode source base node 0 0#64
  let two := putNode one base node 8 value
  have first := store_node source base node cap 0#64 0 (.const 0#64) domain nodeArray geometry.nodesAligned inside
    (by decide) (by decide) locals.baseCell locals.nodeCell rfl
  have second := store_node one base node cap value 8 (localVar "value") domain nodeArray geometry.nodesAligned inside
    (by decide) (by decide) locals.baseCell locals.nodeCell (Request.local_word one "value" value locals.valueCell)
  have fields (offset : Nat) (small : offset < 88) : two.memory (table+BitVec.ofNat 64 offset) = source.memory (table+BitVec.ofNat 64 offset) := by
    have away0 := geometry.scalar_header_away capSmall node inside 0 offset (by decide) small
    have away8 := geometry.scalar_header_away capSmall node inside 8 offset (by decide) small
    change table+BitVec.ofNat 64 offset ≠ FindLeaf.cell base node 0 at away0
    change table+BitVec.ofNat 64 offset ≠ FindLeaf.cell base node 8 at away8
    simp only [two,one,putNode,StoreWord.put,if_neg away0,if_neg away8]
  have countRead := NewNode.field_read two table pos 24 domain geometry.table aligned (by decide) (by decide) locals.tableCell
    ((fields 24 (by decide)).trans countCell)
  have enteredLocals : ScalarLocals (bind two "pos" pos) table key base node value := (locals.with_memory two.memory).with_position pos
  have tail := scalar_tail_execute (bind two "pos" pos) table key cap node pos value domain geometry aligned capSmall inside posInside enteredLocals
    (bind_lookup_same _ _ _) ((fields 48 (by decide)).trans orderCell)
  have last : evaluateHOLFiniteState two afterValue = (some (.returned (.val (.word node))),scalarStoresReturned source table key cap node pos value) := by
    rw [shapes.2.2.2.2.2.2.2.1]
    exact ScalarScope.declare_execute _ _ "pos" _ pos afterPosition _ countRead tail
  rw [shapes.2.2.2.2.2.1,evaluateHOLFiniteState_seq_line780,first]
  simp only
  rw [shapes.2.2.2.2.2.2.1,evaluateHOLFiniteState_seq_line780,second]
  exact last

theorem scalar_stores_returned_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap node pos value : BitVec 64) :
    LocalEffects.erase (scalarStoresReturned source table key cap node pos value) = LocalEffects.erase (scalarStored source table key cap node pos value) ∧
      (scalarStoresReturned source table key cap node pos value).clock = source.clock := ⟨rfl,rfl⟩

/-- Physical state after the real scalar key copy and before the original
leaf stores. Copy bytes are unconstrained; header fields and all words
outside the complete allocation retain their actual earlier values. -/
structure ScalarCopied (source copied : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap : BitVec 64) : Prop where
  fields : MemoryMetadata.erase copied=MemoryMetadata.erase source
  locals : copied.locals=(scalarCopyEntry (scalarNodeEntry source table) key).locals
  header : ∀ offset : Nat,offset<88→copied.memory (table+BitVec.ofNat 64 offset)=
    (New.putField source table 64 2#64).memory (table+BitVec.ofNat 64 offset)
  outside : ∀ query : BitVec 64,New.OutsideScalar table key cap query→copied.memory query=source.memory query

/-- The actual normally returned leaf derives a usable physical copied
state. Its key region, metadata and later continuation all come from this
same execution, without a predicted successful copy as a premise. -/
theorem scalar_copied_state {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer : BitVec 64}
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (keySmall : key.toNat≤60) (capSmall : cap.toNat≤2^32) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ copied inner,ScalarCopied source copied table key cap ∧
      evaluateHOLFiniteState copied afterCopy=(some (.returned value),inner) ∧
      LocalEffects.erase post=LocalEffects.erase inner ∧ post.clock=inner.clock := by
  obtain ⟨copied,inner,frame,locals,remaining,scope,clock⟩:=scalar_copied_returned image installed tableCell keyCell (by omega) value normal
  obtain ⟨owned,aligned,afterHeader,beforeNodes⟩:=image.geometry.first_key_copy keySmall capSmall image.capLower
  refine ⟨copied,inner,⟨frame.fields,locals,?_,?_⟩,remaining,scope,clock⟩
  · intro offset inside
    have number:=byteAddress_toNat table offset (by have upper:=image.geometry.table.upper; omega)
    change (table+BitVec.ofNat 64 offset).toNat=table.toNat+offset at number
    exact frame.memory _ (CopyGeneral.Away.after _ _ _ aligned (by have upper:=owned.upper; omega) (by rw [number]; omega))
  · intro query outside
    rw [frame.memory query (image.geometry.first_key_copy_away keySmall capSmall image.capLower query outside)]
    have different : query≠table+64#64:=by
      have number:=byteAddress_toNat table 64 (by have upper:=image.geometry.table.upper; omega)
      change (table+64#64).toNat=table.toNat+64 at number
      have bound:=image.geometry.header_before_end
      intro same
      have equal:=congrArg BitVec.toNat same
      rw [number] at equal
      rcases outside with before|after <;> omega
    exact if_neg different

/-- The original remaining leaf stores execute with the actual scalar
marker and constructor-derived node/order arrays. The source copy bytes
are not needed to establish these writes and the returned node index. -/
theorem ScalarCopied.after_copy_execute {source copied : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap value : BitVec 64}
    (physical : ScalarCopied source copied table key cap) (image : New.ScalarEmpty source table key cap)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value))) (capSmall : cap.toNat≤2^32) :
    evaluateHOLFiniteState copied afterCopy=
      (some (.returned (.val (.word 1#64))),restore copied "nodes"
        (scalarStoresReturned (bind copied "nodes" (New.scalarNodesPointer table key cap)) table key cap 1#64 0#64 value)) := by
  have header (offset : Nat) (inside : offset<88) (different : offset≠64) :
      copied.memory (table+BitVec.ofNat 64 offset)=source.memory (table+BitVec.ofNat 64 offset):=
    (physical.header offset inside).trans (header_other source table 2#64 64 offset image.geometry.table (by decide) inside different)
  have tableCopied : copied.locals.lookup (ofString "t")=some (.val (.word table)):=by
    rw [physical.locals]
    simpa [scalarCopyEntry,scalarNodeEntry,QueryBranch.bind,New.putField,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using tableCell
  have valueCopied : copied.locals.lookup (ofString "value")=some (.val (.word value)):=by
    rw [physical.locals]
    simpa [scalarCopyEntry,scalarNodeEntry,QueryBranch.bind,New.putField,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using valueCell
  have nodeCopied : copied.locals.lookup (ofString "n")=some (.val (.word 1#64)):=by
    rw [physical.locals]
    simp [scalarCopyEntry,scalarNodeEntry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
  have lengthCopied : copied.locals.lookup (ofString "klen")=some (.val (.word key)):=by
    rw [physical.locals]
    simp [scalarCopyEntry,scalarNodeEntry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
  have domain : copied.memaddrs=InitE.ordinaryDomain:=(MemoryMetadata.domain physical.fields).trans image.domain
  have nodesCell : copied.memory (table+40#64)=.word (New.scalarNodesPointer table key cap):=
    (header 40 (by decide) (by decide)).trans (image.fields (table+40#64,New.scalarNodesPointer table key cap) (by simp [New.scalarWrites]))
  have countCell : copied.memory (table+24#64)=.word 0#64:=
    (header 24 (by decide) (by decide)).trans (image.fields (table+24#64,0#64) (by simp [New.scalarWrites]))
  have orderCell : copied.memory (table+48#64)=.word (New.scalarOrderPointer table key cap):=
    (header 48 (by decide) (by decide)).trans (image.fields (table+48#64,New.scalarOrderPointer table key cap) (by simp [New.scalarWrites]))
  have nodesRead:=NewNode.field_read copied table (New.scalarNodesPointer table key cap) 40 domain image.geometry.table image.aligned (by decide) (by decide) tableCopied nodesCell
  let entered:=bind copied "nodes" (New.scalarNodesPointer table key cap)
  have locals : ScalarLocals entered table key (New.scalarNodesPointer table key cap) 1#64 value:=
    ⟨(bind_lookup_other _ "nodes" "t" _ (by decide)).trans tableCopied,bind_lookup_same _ _ _,
      (bind_lookup_other _ "nodes" "n" _ (by decide)).trans nodeCopied,
      (bind_lookup_other _ "nodes" "value" _ (by decide)).trans valueCopied,
      (bind_lookup_other _ "nodes" "klen" _ (by decide)).trans lengthCopied⟩
  have storesRun:=scalar_stores_execute entered table key cap 1#64 0#64 value domain image.geometry image.aligned capSmall
    (by have lower:=image.capLower; change 1≤cap.toNat; omega) (by simp) locals countCell orderCell
  rw [shapes.2.2.2.2.1]
  exact ScalarScope.declare_execute copied _ "nodes" _ (New.scalarNodesPointer table key cap) stores (some (.returned (.val (.word 1#64)))) nodesRead storesRun

/-- Complete normally returned first scalar leaf: its actual copy state
and all subsequent real writes, with no future-copy/store result assumed. -/
theorem scalar_empty_returned {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer value : BitVec 64}
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (keySmall : key.toNat≤60) (capSmall : cap.toNat≤2^32) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    returned=.val (.word 1#64) ∧ ∃ copied,ScalarCopied source copied table key cap ∧
      LocalEffects.erase post=LocalEffects.erase (scalarStored copied table key cap 1#64 0#64 value) := by
  obtain ⟨copied,inner,physical,remaining,scope,clock⟩:=scalar_copied_state image installed tableCell keyCell keySmall capSmall returned normal
  have actual:=physical.after_copy_execute image tableCell valueCell capSmall
  have result:=congrArg Prod.fst (remaining.symm.trans actual)
  have answer : returned=.val (.word 1#64):=by simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using result
  have endpoint:=congrArg Prod.snd (remaining.symm.trans actual)
  have fields:=congrArg LocalEffects.erase endpoint
  change LocalEffects.erase inner=LocalEffects.erase (scalarStored copied table key cap 1#64 0#64 value) at fields
  exact ⟨answer,copied,physical,scope.trans fields⟩

/-- The actual scalar node/order/count writes stay in the constructor's
complete region. This protects later table headers and every earlier word. -/
theorem scalar_stored_outside (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap node pos value : BitVec 64)
    (geometry : New.ScalarGeometry table key cap) (capSmall : cap.toNat≤2^32)
    (inside : node.toNat≤cap.toNat) (posInside : pos.toNat≤cap.toNat)
    (query : BitVec 64) (outside : New.OutsideScalar table key cap query) :
    (scalarStored source table key cap node pos value).memory query=source.memory query := by
  have nodes (offset : Nat) (small : offset<32) : query≠FindLeaf.cell (New.scalarNodesPointer table key cap) node offset:=by
    have bounds:=geometry.node_in_scalar capSmall node inside offset small
    exact outside.ne_address bounds.1 bounds.2
  have order : query≠slot (New.scalarOrderPointer table key cap) pos 8:=by
    have bounds:=geometry.order_in_scalar capSmall pos posInside
    exact outside.ne_address bounds.1 bounds.2
  have header : query≠table+24#64:=by
    have number:=byteAddress_toNat table 24 (by have upper:=geometry.table.upper; omega)
    change (table+24#64).toNat=table.toNat+24 at number
    apply outside.ne_address
    · rw [number]; omega
    · rw [number]; have endBefore:=geometry.header_before_end; omega
  simp only [scalarStored,scalarTailStored,scalarPutOrder,putNode,New.putField,StoreWord.put,
    if_neg (nodes 0 (by decide)),if_neg (nodes 8 (by decide)),if_neg (nodes 16 (by decide)),if_neg (nodes 24 (by decide)),if_neg order,if_neg header]

theorem scalar_stored_metadata (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap node pos value : BitVec 64) :
    MemoryMetadata.erase (scalarStored source table key cap node pos value)=MemoryMetadata.erase source := by
  unfold scalarStored scalarTailStored scalarPutOrder putNode New.putField
  rfl

/-- Whole genuine normal first scalar-leaf frame. Every write and copy is
from the same real execution; globals/heap are unchanged and memory outside
its allocated region retains its original value. -/
theorem scalar_empty_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer value : BitVec 64}
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (keySmall : key.toNat≤60) (capSmall : cap.toNat≤2^32) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    returned=.val (.word 1#64) ∧ New.ScalarFrame source post table key cap := by
  obtain ⟨answer,copied,physical,scope⟩:=scalar_empty_returned image installed tableCell keyCell valueCell keySmall capSmall returned normal
  have metadata:=MemoryMetadata.of_frame scope
  have finalMetadata:=metadata.trans (scalar_stored_metadata copied table key cap 1#64 0#64 value)
  have memory:=LocalEffects.memory_of_erase (scalarStored copied table key cap 1#64 0#64 value) post scope
  refine ⟨answer,⟨finalMetadata.trans physical.fields,?_⟩⟩
  intro query outside
  rw [memory]
  exact (scalar_stored_outside copied table key cap 1#64 0#64 value image.geometry capSmall
    (by have lower:=image.capLower; change 1≤cap.toNat; omega) (by simp) query outside).trans (physical.outside query outside)

end InitECandidate.Solver.Input.CurrentTable.NewLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.NewNode.from_scalar_empty
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.ScalarFields.of_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.ScalarFields.after_next
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_tail_quiet
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_after_node_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_empty_cost

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem scalar_empty_finish_quiet (code) : QuietClock.Preserves code emptyFinish := by
  rw [guard_shapes.2.2.1]
  exact QuietClock.sequence code _ _ (QuietClock.store code _ _) (QuietClock.returned code _)

/-- An actual zero leaf takes only the real first-insertion branch. The
callee allowance uses its scalar key width, without a32byte key image. -/
theorem scalar_after_leaf_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer value : BitVec 64)
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word 0#64))) (small : key.toNat+32<2^64) :
    source.clock-(evaluateHOLFiniteState source afterLeaf).2.clock≤CopyAny.price key.toNat+3 := by
  have keysRead:=NewNode.field_read source table (New.keysPointer table) 32 image.domain image.geometry.table image.aligned (by decide) (by decide) tableCell
    (image.fields (table+32#64,New.keysPointer table) (by simp [New.scalarWrites]))
  rw [entry_shapes.2.2.2.1]
  apply ClockCost.declared_current source "keys" _ (New.keysPointer table) _ (CopyAny.price key.toNat+3) keysRead
  let current:=bind source "keys" (New.keysPointer table)
  have currentTable : current.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other source "keys" "t" (New.keysPointer table) (by decide)).trans tableCell
  have currentKey : current.locals.lookup (ofString "key")=some (.val (.word pointer)):=
    (bind_lookup_other source "keys" "key" (New.keysPointer table) (by decide)).trans keyCell
  have currentValue : current.locals.lookup (ofString "value")=some (.val (.word value)):=
    (bind_lookup_other source "keys" "value" (New.keysPointer table) (by decide)).trans valueCell
  have currentLeaf : current.locals.lookup (ofString "leaf")=some (.val (.word 0#64)):=
    (bind_lookup_other source "keys" "leaf" (New.keysPointer table) (by decide)).trans leafCell
  rw [after_keys_empty current currentLeaf,guard_shapes.2.1]
  obtain ⟨callee,called,tCell,kCell,vCell⟩:=word_triple_environment current.code.lookup (ofString "htab_new_leaf")
    (ofString "t") (ofString "key") (ofString "value") NewLeaf.body .one table pointer value
    (by decide) (by decide) (by decide) (NewLeaf.original_code current.code installed)
  have args : evalListHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) leafArguments=
      some [.val (.word table),.val (.word pointer),.val (.word value)]:=by
    simp [leafArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,currentTable,currentKey,currentValue]
  have cost:=NewLeaf.scalar_empty_cost (callEntryStateHOLFinite current callee) table key cap pointer (image.of_erase rfl) installed tCell kCell small
  simpa only [current,Nat.add_zero] using ClockCost.scoped_current current (ofString "nl") .one (ofString "htab_new_leaf") leafArguments
    [.val (.word table),.val (.word pointer),.val (.word value)] NewLeaf.body emptyFinish callee .one (CopyAny.price key.toNat+2) 0 args called cost
    (ClockCost.of_quiet current.code emptyFinish (scalar_empty_finish_quiet current.code))

/-- The actual empty scalar lookup returns zero and retains the same table
before the first leaf construction. Every stopped outcome is priced too. -/
theorem scalar_after_stride_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer value : BitVec 64)
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value))) (small : key.toNat+32<2^64) :
    source.clock-(evaluateHOLFiniteState source afterStride).2.clock≤CopyAny.price key.toNat+4 := by
  let output:=evaluateHOLFiniteState source afterStride
  have actual : evaluateHOLFiniteState source afterStride=(output.1,output.2):=rfl
  rw [entry_shapes.2.2.1] at actual
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "t",localVar "key"]=
      some [.val (.word table),.val (.word pointer)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,tableCell,keyCell]
  rcases FindLeaf.scoped_scalar_empty_trace source output.2 table key cap pointer image installed "leaf" [localVar "t",localVar "key"] afterLeaf args output.1 actual with stopped|reached
  · change source.clock-output.2.clock≤CopyAny.price key.toNat+4
    have bound:=stopped.1
    omega
  · obtain ⟨target,inner,frame,clock,price,continued,endpoint⟩:=reached
    let current:=CallNormal.continuationEntry source target "leaf" (.val (.word 0#64))
    have currentImage : New.ScalarEmpty current table key cap:=image.of_erase frame
    have currentTable : current.locals.lookup (ofString "t")=some (.val (.word table)):=
      (CallNormal.continuation_lookup_other source target "leaf" "t" (.val (.word 0#64)) (by decide)).trans tableCell
    have currentKey : current.locals.lookup (ofString "key")=some (.val (.word pointer)):=
      (CallNormal.continuation_lookup_other source target "leaf" "key" (.val (.word 0#64)) (by decide)).trans keyCell
    have currentValue : current.locals.lookup (ofString "value")=some (.val (.word value)):=
      (CallNormal.continuation_lookup_other source target "leaf" "value" (.val (.word 0#64)) (by decide)).trans valueCell
    have code:=congrArg PanSemStateFiniteExact.code frame
    change current.code=source.code at code
    have cost:=scalar_after_leaf_cost current table key cap pointer value currentImage (by rw [code]; exact installed)
      currentTable currentKey currentValue (CallNormal.continuation_lookup_same source target "leaf" (.val (.word 0#64))) small
    rw [continued] at cost
    change current.clock-inner.clock≤CopyAny.price key.toNat+3 at cost
    have entryClock : current.clock=target.clock:=rfl
    have exitClock : output.2.clock=inner.clock:=by rw [endpoint] <;> rfl
    change source.clock-output.2.clock≤CopyAny.price key.toNat+4
    omega

/-- Whole unchanged htab_set at a genuinely fresh scalar table. The bound
includes both real helper calls and the full variable-length key copy. -/
theorem scalar_empty_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer value : BitVec 64)
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value))) (small : key.toNat+32<2^64) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤CopyAny.price key.toNat+4 := by
  have lengthRead:=NewNode.field_read source table key 0 image.domain image.geometry.table image.aligned (by decide) (by decide) tableCell
    (image.fields (table+0#64,key) (by simp [New.scalarWrites]))
  rw [entry_shapes.1]
  apply ClockCost.declared_current source "klen" _ key _ (CopyAny.price key.toNat+4) lengthRead
  let first:=bind source "klen" key
  have firstTable : first.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other source "klen" "t" key (by decide)).trans tableCell
  have strideRead:=NewNode.field_read first table (New.strideWord key) 8 image.domain image.geometry.table image.aligned (by decide) (by decide) firstTable
    (image.fields (table+8#64,New.strideWord key) (by simp [New.scalarWrites]))
  rw [entry_shapes.2.1]
  apply ClockCost.declared_current first "stride" _ (New.strideWord key) _ (CopyAny.price key.toNat+4) strideRead
  let current:=bind first "stride" (New.strideWord key)
  have kept (name : String) (notStride : ofString "stride"≠ofString name) (notLength : ofString "klen"≠ofString name) :
      current.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    (bind_lookup_other first "stride" name (New.strideWord key) notStride).trans (bind_lookup_other source "klen" name key notLength)
  exact scalar_after_stride_cost current table key cap pointer value (image.of_erase rfl) installed
    ((kept "t" (by decide) (by decide)).trans tableCell) ((kept "key" (by decide) (by decide)).trans keyCell)
    ((kept "value" (by decide) (by decide)).trans valueCell) small

/-- Actual ignored first-insertion caller at the scalar constructor's
width. Argument values come from the same evaluated call. -/
theorem scalar_empty_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer value : BitVec 64)
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word table),.val (.word pointer),.val (.word value)]) (small : key.toNat+32<2^64) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htab_set") arguments)).2.clock≤CopyAny.price key.toNat+5 := by
  obtain ⟨callee,called,tCell,kCell,vCell⟩:=word_triple_environment source.code.lookup (ofString "htab_set")
    (ofString "t") (ofString "key") (ofString "value") body .one table pointer value
    (by decide) (by decide) (by decide) (original_code source.code installed)
  exact ClockCost.call_current source (some none) (ofString "htab_set") arguments
    [.val (.word table),.val (.word pointer),.val (.word value)] body callee .one (CopyAny.price key.toNat+4) args called
    (scalar_empty_cost (callEntryStateHOLFinite source callee) table key cap pointer value (image.of_erase rfl) installed tCell kCell vCell small)

/-- The real20byte first account-access insertion, including its ordinary
caller and every copy/setup failure or timeout. -/
theorem account_first_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap pointer value : BitVec 64)
    (image : New.ScalarEmpty source table 20#64 cap) (installed : OriginalCode.Installed source.code)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word table),.val (.word pointer),.val (.word value)]) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htab_set") arguments)).2.clock≤29 := by
  simpa [CopyAny.price] using scalar_empty_call_cost source table 20#64 cap pointer value image installed arguments args (by decide)

/-- The actual first-leaf caller and original root store retain the same
complete allocation footprint and return the real setter's zero word. -/
theorem scalar_empty_leaf_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer value : BitVec 64}
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (keySmall : key.toNat≤60) (capSmall : cap.toNat≤2^32) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source emptyLeafCall=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ New.ScalarFrame source post table key cap := by
  obtain ⟨callee,called,tCell,kCell,vCell⟩:=word_triple_environment source.code.lookup (ofString "htab_new_leaf")
    (ofString "t") (ofString "key") (ofString "value") NewLeaf.body .one table pointer value
    (by decide) (by decide) (by decide) (NewLeaf.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) leafArguments=
      some [.val (.word table),.val (.word pointer),.val (.word value)]:=by
    simp [leafArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,tableCell,keyCell,valueCell]
  rw [guard_shapes.2.1] at normal
  obtain ⟨funded,target,node,inner,leafRun,checked,continued,endpoint⟩:=CallNormal.scoped_normal source post "nl" .one (ofString "htab_new_leaf")
    leafArguments _ NewLeaf.body emptyFinish callee .one args called returned normal
  obtain ⟨nodeEq,leafFrame⟩:=NewLeaf.scalar_empty_frame (source:=callEntryStateHOLFinite source callee) (post:=target) (image.of_erase rfl) installed tCell kCell vCell keySmall capSmall node leafRun
  rw [nodeEq] at continued
  let current:=CallNormal.continuationEntry source target "nl" (.val (.word 1#64))
  have currentFrame : New.ScalarFrame source current table key cap:=leafFrame.of_erase rfl rfl
  have tCurrent : current.locals.lookup (ofString "t")=some (.val (.word table)):=
    (CallNormal.continuation_lookup_other source target "nl" "t" (.val (.word 1#64)) (by decide)).trans tableCell
  have nlCurrent : current.locals.lookup (ofString "nl")=some (.val (.word 1#64)):=CallNormal.continuation_lookup_same source target "nl" _
  have addressRead:=Scalar.plus_read current (localVar "t") table 56 (Request.local_word current "t" table tCurrent)
  have valueRead:=Request.local_word current "nl" 1#64 nlCurrent
  have domain : current.memaddrs=InitE.ordinaryDomain:=(MemoryMetadata.domain currentFrame.fields).trans image.domain
  have stored : evaluateHOLFiniteState current (.store (Scalar.plus (localVar "t") 56) (localVar "nl"))=(none,New.putField current table 56 1#64):=
    StoreWord.execute current _ _ _ _ addressRead valueRead
      (AllocatedBytes.word_mapped current table 88 56 domain image.geometry.table (by decide) image.aligned (by decide))
  rw [guard_shapes.2.2.1] at continued
  change evaluateHOLFiniteState current (.seq (.store (Scalar.plus (localVar "t") 56) (localVar "nl")) (.return (.const 0#64)))=(some (.returned returned),inner) at continued
  rw [evaluateHOLFiniteState_seq_line780,stored] at continued
  obtain ⟨read,innerEq⟩:=return_normal (New.putField current table 56 1#64) inner (.const 0#64) returned continued
  have answer : returned=.val (.word 0#64):=Option.some.inj read.symm
  have number:=byteAddress_toNat table 56 (by have upper:=image.geometry.table.upper; omega)
  change (table+56#64).toNat=table.toNat+56 at number
  have storedFrame:=currentFrame.store_inside _ _ (table+56#64) 1#64 addressRead valueRead
    (by rw [number]; omega) (by rw [number]; have lower:=image.geometry.header_before_end; omega) stored
  have scope : LocalEffects.erase post=LocalEffects.erase (New.putField current table 56 1#64):=by rw [endpoint,innerEq] <;> rfl
  exact ⟨answer,storedFrame.of_erase rfl scope⟩

theorem scalar_after_leaf_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer value : BitVec 64}
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word 0#64)))
    (keySmall : key.toNat≤60) (capSmall : cap.toNat≤2^32) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterLeaf=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ New.ScalarFrame source post table key cap := by
  have keysRead:=NewNode.field_read source table (New.keysPointer table) 32 image.domain image.geometry.table image.aligned (by decide) (by decide) tableCell
    (image.fields (table+32#64,New.keysPointer table) (by simp [New.scalarWrites]))
  rw [entry_shapes.2.2.2.1] at normal
  obtain ⟨inner,continued,endpoint⟩:=ScalarScope.declare_trace source post "keys" _ (New.keysPointer table) afterKeys (some (.returned returned)) keysRead normal
  let current:=bind source "keys" (New.keysPointer table)
  have kept (name : String) (different : ofString "keys"≠ofString name) : current.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    bind_lookup_other source "keys" name (New.keysPointer table) different
  rw [after_keys_empty current ((kept "leaf" (by decide)).trans leafCell)] at continued
  obtain ⟨answer,frame⟩:=scalar_empty_leaf_frame (source:=current) (post:=inner) (image.of_erase rfl) installed
    ((kept "t" (by decide)).trans tableCell) ((kept "key" (by decide)).trans keyCell) ((kept "value" (by decide)).trans valueCell)
    keySmall capSmall returned continued
  exact ⟨answer,frame.of_erase rfl (by rw [endpoint] <;> rfl)⟩

theorem scalar_after_stride_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer value : BitVec 64}
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (keySmall : key.toNat≤60) (capSmall : cap.toNat≤2^32) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterStride=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ New.ScalarFrame source post table key cap := by
  rw [entry_shapes.2.2.1] at normal
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "t",localVar "key"]=
      some [.val (.word table),.val (.word pointer)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,tableCell,keyCell]
  rcases FindLeaf.scoped_scalar_empty_trace source post table key cap pointer image installed "leaf" [localVar "t",localVar "key"] afterLeaf args (some (.returned returned)) normal with stopped|reached
  · exact False.elim (stopped.2 returned rfl)
  · obtain ⟨target,inner,frame,clock,price,continued,endpoint⟩:=reached
    let current:=CallNormal.continuationEntry source target "leaf" (.val (.word 0#64))
    have currentImage : New.ScalarEmpty current table key cap:=image.of_erase frame
    have kept (name : String) (different : ofString "leaf"≠ofString name) : current.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
      CallNormal.continuation_lookup_other source target "leaf" name (.val (.word 0#64)) different
    have code:=congrArg PanSemStateFiniteExact.code frame
    change current.code=source.code at code
    obtain ⟨answer,physical⟩:=scalar_after_leaf_frame currentImage (by rw [code]; exact installed)
      ((kept "t" (by decide)).trans tableCell) ((kept "key" (by decide)).trans keyCell) ((kept "value" (by decide)).trans valueCell)
      (CallNormal.continuation_lookup_same source target "leaf" (.val (.word 0#64))) keySmall capSmall returned continued
    exact ⟨answer,physical.of_erase frame.symm (by rw [endpoint] <;> rfl)⟩

/-- Whole original first setter normal return, retaining the same full
scalar-table footprint through both declarations and all lexical scopes. -/
theorem scalar_empty_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer value : BitVec 64}
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (keySmall : key.toNat≤60) (capSmall : cap.toNat≤2^32) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ New.ScalarFrame source post table key cap := by
  have lengthRead:=NewNode.field_read source table key 0 image.domain image.geometry.table image.aligned (by decide) (by decide) tableCell
    (image.fields (table+0#64,key) (by simp [New.scalarWrites]))
  rw [entry_shapes.1] at normal
  obtain ⟨middle,continued,endpoint⟩:=ScalarScope.declare_trace source post "klen" _ key afterLength (some (.returned returned)) lengthRead normal
  let first:=bind source "klen" key
  have firstTable : first.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other source "klen" "t" key (by decide)).trans tableCell
  have strideRead:=NewNode.field_read first table (New.strideWord key) 8 image.domain image.geometry.table image.aligned (by decide) (by decide) firstTable
    (image.fields (table+8#64,New.strideWord key) (by simp [New.scalarWrites]))
  rw [entry_shapes.2.1] at continued
  obtain ⟨inner,remaining,innerEq⟩:=ScalarScope.declare_trace first middle "stride" _ (New.strideWord key) afterStride (some (.returned returned)) strideRead continued
  let current:=bind first "stride" (New.strideWord key)
  have kept (name : String) (notStride : ofString "stride"≠ofString name) (notLength : ofString "klen"≠ofString name) :
      current.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    (bind_lookup_other first "stride" name (New.strideWord key) notStride).trans (bind_lookup_other source "klen" name key notLength)
  obtain ⟨answer,frame⟩:=scalar_after_stride_frame (source:=current) (post:=inner) (image.of_erase rfl) installed
    ((kept "t" (by decide) (by decide)).trans tableCell) ((kept "key" (by decide) (by decide)).trans keyCell)
    ((kept "value" (by decide) (by decide)).trans valueCell) keySmall capSmall returned remaining
  exact ⟨answer,frame.of_erase rfl (by rw [endpoint,innerEq] <;> rfl)⟩

/-- Actual ordinary first-set caller; its callee return, saved locals and
complete write footprint are derived from the same normally continuing call. -/
theorem scalar_empty_call_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer value : BitVec 64}
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word table),.val (.word pointer),.val (.word value)])
    (keySmall : key.toNat≤60) (capSmall : cap.toNat≤2^32)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htab_set") arguments)=(none,post)) :
    New.ScalarFrame source post table key cap ∧ post.locals=source.locals := by
  obtain ⟨callee,called,tCell,kCell,vCell⟩:=word_triple_environment source.code.lookup (ofString "htab_set")
    (ofString "t") (ofString "key") (ofString "value") body .one table pointer value
    (by decide) (by decide) (by decide) (original_code source.code installed)
  obtain ⟨funded,values,actual,actualCallee,shape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩:=CallNormal.ignored_data source post (ofString "htab_set") arguments normal
  have valuesEq : values=[.val (.word table),.val (.word pointer),.val (.word value)]:=Option.some.inj (actualArgs.symm.trans args)
  subst values
  have entryEq : (actual,actualCallee,shape)=(body,callee,.one):=Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  obtain ⟨answer,frame⟩:=scalar_empty_frame (source:=callEntryStateHOLFinite source callee) (post:=target) (image.of_erase rfl) installed tCell kCell vCell keySmall capSmall returned bodyRun
  exact ⟨frame.of_erase rfl (by rw [endpoint] <;> rfl),by rw [endpoint]⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_empty_finish_quiet
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_after_leaf_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_after_stride_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_empty_cost

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_empty_call_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.account_first_call_cost

#print axioms InitECandidate.Solver.Input.CurrentTable.New.scalar_stride_numbers
#print axioms InitECandidate.Solver.Input.CurrentTable.New.scalar_array_numbers
#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarGeometry.first_key_copy
#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarGeometry.first_key_copy_away

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_copy_arguments
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_prefix_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_copy_trace
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_copied_returned

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_copied_state

#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarGeometry.scalar_header_away
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_tail_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_stores_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_stores_returned_frame

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.ScalarCopied.after_copy_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_empty_returned

#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarGeometry.node_in_scalar
#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarGeometry.order_in_scalar
#print axioms InitECandidate.Solver.Input.CurrentTable.New.OutsideScalar.ne_address
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_stored_outside
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_empty_frame

#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarFrame.of_erase
#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarFrame.store_inside
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_stored_metadata

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_empty_leaf_frame

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_after_leaf_frame

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_after_stride_frame

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_empty_frame

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_empty_call_frame
