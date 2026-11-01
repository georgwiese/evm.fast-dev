import InitECandidate.Solver.Input.CurrentTable.FirstDiff.Cost
import InitECandidate.Solver.Input.CurrentTable.NewScalarImage
import InitECandidate.Solver.MutableTable.MemeqVariableCost
import InitECandidate.Solver.Input.CurrentTable.NewInternal.Call
import InitECandidate.Solver.Input.CurrentTable.Set.SpliceLocals
import InitECandidate.Solver.Input.CurrentTable.Set.SpliceProgram
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
import InitECandidate.Solver.Input.CurrentTable.NodeFrames

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

def OutsideScalar (table key cap query : BitVec 64) : Prop :=
  query.toNat<table.toNat ∨ (scalarNextHeap table key cap).toNat≤query.toNat

/-- Actual padded-key destination at an available scalar node index. -/
def scalarKeyAt (table key index : BitVec 64) : BitVec 64:=keysPointer table+index*strideWord key

/-- Every available scalar key slot is aligned, starts after the header,
and ends before the actual nodes. No source-key mapping is assumed. -/
theorem ScalarGeometry.key_copy {table key cap : BitVec 64} (geometry : ScalarGeometry table key cap)
    (keySmall : key.toNat≤60) (capSmall : cap.toNat≤2^32) (index : BitVec 64) (inside : index.toNat≤cap.toNat) :
    AllocatedBytes.Arena (scalarKeyAt table key index) key.toNat ∧
      (scalarKeyAt table key index).toNat%8=0 ∧ table.toNat+88≤(scalarKeyAt table key index).toNat ∧
      (scalarKeyAt table key index).toNat+key.toNat≤(scalarNodesPointer table key cap).toNat := by
  obtain ⟨widthLower,widthUpper,widthAligned⟩:=scalar_stride_numbers key keySmall
  have numbers:=scalar_array_numbers key cap keySmall capSmall
  have array : AllocatedBytes.Arena (keysPointer table) ((strideWord key).toNat*(cap.toNat+1)):=by
    simpa only [numbers.1,Nat.mul_comm] using geometry.keys
  have destination : slot (keysPointer table) index (strideWord key).toNat=scalarKeyAt table key index:=by
    simp [slot,scalarKeyAt,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have room:=slot_arena (keysPointer table) index cap (strideWord key).toNat array inside
  have owned:=AllocatedBytes.Arena.subrange _ (strideWord key).toNat 0 key.toNat room (by omega)
  have number:=slot_number (keysPointer table) index cap (strideWord key).toNat array inside
  rw [destination] at room number
  have extent:=Nat.mul_le_mul_left (strideWord key).toNat (show index.toNat+1≤cap.toNat+1 by omega)
  have keysBefore:=geometry.keysBefore
  rw [numbers.1] at keysBefore
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [destination,byteAddress,BitVec.add_zero] using owned
  · rw [←destination]
    exact slot_aligned _ index cap _ array inside geometry.keysAligned widthAligned
  · rw [number]
    have before:=geometry.tableBefore
    omega
  · rw [number]
    rw [Nat.mul_add,Nat.mul_one] at extent
    rw [Nat.mul_comm (cap.toNat+1)] at keysBefore
    omega

theorem ScalarGeometry.key_copy_away {table key cap : BitVec 64} (geometry : ScalarGeometry table key cap)
    (keySmall : key.toNat≤60) (capSmall : cap.toNat≤2^32) (index : BitVec 64) (inside : index.toNat≤cap.toNat)
    (query : BitVec 64) (outside : OutsideScalar table key cap query) :
    CopyGeneral.Away (scalarKeyAt table key index) query key.toNat := by
  obtain ⟨owned,aligned,afterHeader,beforeNodes⟩:=geometry.key_copy keySmall capSmall index inside
  rcases outside with before|after
  · exact CopyGeneral.Away.after _ query _ aligned (by have upper:=owned.upper; omega) (by omega)
  · apply CopyGeneral.Away.before _ query _ (scalarNextHeap table key cap).toNat
    · have first:=geometry.nodesBefore
      have second:=geometry.orderBefore
      omega
    · have upper:=geometry.endBound
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

theorem ScalarFrame.refl (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap : BitVec 64) : ScalarFrame source source table key cap:=
  ⟨rfl,by intros; rfl⟩

theorem ScalarFrame.trans {source middle target : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap : BitVec 64}
    (first : ScalarFrame source middle table key cap) (second : ScalarFrame middle target table key cap) : ScalarFrame source target table key cap:=
  ⟨second.fields.trans first.fields,by intro query outside; exact (second.memory query outside).trans (first.memory query outside)⟩

/-- A scalar word update inside the actual allocation protects every
external word, independently of its stored value. -/
theorem ScalarFrame.put_word {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap : BitVec 64}
    (frame : ScalarFrame origin source table key cap) (address value : BitVec 64)
    (lower : table.toNat≤address.toNat) (upper : address.toNat<(scalarNextHeap table key cap).toNat) :
    ScalarFrame origin {source with memory:=StoreWord.put source.memory address value} table key cap := by
  refine ⟨frame.fields,?_⟩
  intro query outside
  exact (if_neg (outside.ne_address lower upper)).trans (frame.memory query outside)

theorem ScalarFrame.put_field {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap : BitVec 64}
    (frame : ScalarFrame origin source table key cap) (geometry : ScalarGeometry table key cap)
    (offset : Nat) (small : offset<88) (value : BitVec 64) : ScalarFrame origin (putField source table offset value) table key cap := by
  have number:=byteAddress_toNat table offset (by have upper:=geometry.table.upper; omega)
  change (table+BitVec.ofNat 64 offset).toNat=table.toNat+offset at number
  exact frame.put_word _ value (by rw [number]; omega) (by rw [number]; have before:=geometry.header_before_end; omega)

theorem ScalarFrame.put_node {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap : BitVec 64}
    (frame : ScalarFrame origin source table key cap) (geometry : ScalarGeometry table key cap) (capSmall : cap.toNat≤2^32)
    (node value : BitVec 64) (offset : Nat) (inside : node.toNat≤cap.toNat) (small : offset<32) :
    ScalarFrame origin (putNode source (scalarNodesPointer table key cap) node offset value) table key cap := by
  have bounds:=geometry.node_in_scalar capSmall node inside offset small
  exact frame.put_word _ value bounds.1 bounds.2

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


/-- Exact initialized metadata after the first scalar leaf. The root is0
inside the leaf helper and1 after the enclosing setter's real root store. -/
def singleHeaderWrites (table key cap root : BitVec 64) : List (BitVec 64×BitVec 64):=
  [(table+0#64,key),(table+8#64,strideWord key),(table+16#64,cap),(table+24#64,1#64),
   (table+32#64,keysPointer table),(table+40#64,scalarNodesPointer table key cap),(table+48#64,scalarOrderPointer table key cap),
   (table+56#64,root),(table+64#64,2#64),(table+72#64,0#64),(table+80#64,cap)]

structure ScalarSingle (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap root value : BitVec 64) : Prop where
  geometry : ScalarGeometry table key cap
  aligned : table.toNat%8=0
  domain : source.memaddrs=InitE.ordinaryDomain
  capLower : 2≤cap.toNat
  keySmall : key.toNat≤60
  capSmall : cap.toNat≤2^32
  fields : ∀ entry∈singleHeaderWrites table key cap root,source.memory entry.1=.word entry.2
  leafZero : source.memory (FindLeaf.cell (scalarNodesPointer table key cap) 1#64 0)=.word 0#64
  leafValue : source.memory (FindLeaf.cell (scalarNodesPointer table key cap) 1#64 8)=.word value
  leafPosition : source.memory (FindLeaf.cell (scalarNodesPointer table key cap) 1#64 16)=.word 0#64
  leafMarker : source.memory (FindLeaf.cell (scalarNodesPointer table key cap) 1#64 24)=.word (key*8#64)
  orderFirst : source.memory (scalarOrderPointer table key cap)=.word 1#64

theorem ScalarSingle.of_erase {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap root value : BitVec 64}
    (single : ScalarSingle source table key cap root value) (same : LocalEffects.erase target=LocalEffects.erase source) :
    ScalarSingle target table key cap root value := by
  have memory:=LocalEffects.memory_of_erase source target same
  have domain:=congrArg PanSemStateFiniteExact.memaddrs same
  change target.memaddrs=source.memaddrs at domain
  exact {single with
    domain:=domain.trans single.domain,fields:=by intro entry member; rw [memory]; exact single.fields entry member,
    leafZero:=by rw [memory]; exact single.leafZero,leafValue:=by rw [memory]; exact single.leafValue,
    leafPosition:=by rw [memory]; exact single.leafPosition,leafMarker:=by rw [memory]; exact single.leafMarker,
    orderFirst:=by rw [memory]; exact single.orderFirst}

/-- The original enclosing root store changes only the actual root word. -/
theorem ScalarSingle.with_root {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap root value : BitVec 64}
    (single : ScalarSingle source table key cap root value) (next : BitVec 64) : ScalarSingle (putField source table 56 next) table key cap next value := by
  have nodeAway (offset : Nat) (inside : offset<32) : FindLeaf.cell (scalarNodesPointer table key cap) 1#64 offset≠table+56#64:=
    Ne.symm (single.geometry.scalar_header_away single.capSmall 1#64 (by have lower:=single.capLower; change 1≤cap.toNat; omega) offset 56 inside (by decide))
  have orderAway : scalarOrderPointer table key cap≠table+56#64:=by
    have number:=byteAddress_toNat table 56 (by have upper:=single.geometry.table.upper; omega)
    have first:=single.geometry.tableBefore
    have second:=single.geometry.keysBefore
    have third:=single.geometry.nodesBefore
    intro same
    have equal:=congrArg BitVec.toNat same
    change (table+56#64).toNat=table.toNat+56 at number
    rw [number] at equal
    omega
  refine {single with
    fields:=?_,leafZero:=?_,leafValue:=?_,leafPosition:=?_,leafMarker:=?_,orderFirst:=?_}
  · intro entry member
    simp only [singleHeaderWrites,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · rw [header_other source table next 56 0 single.geometry.table (by decide) (by decide) (by decide)]
      exact single.fields (table+0#64,key) (by simp [singleHeaderWrites])
    · rw [header_other source table next 56 8 single.geometry.table (by decide) (by decide) (by decide)]
      exact single.fields (table+8#64,strideWord key) (by simp [singleHeaderWrites])
    · rw [header_other source table next 56 16 single.geometry.table (by decide) (by decide) (by decide)]
      exact single.fields (table+16#64,cap) (by simp [singleHeaderWrites])
    · rw [header_other source table next 56 24 single.geometry.table (by decide) (by decide) (by decide)]
      exact single.fields (table+24#64,1#64) (by simp [singleHeaderWrites])
    · rw [header_other source table next 56 32 single.geometry.table (by decide) (by decide) (by decide)]
      exact single.fields (table+32#64,keysPointer table) (by simp [singleHeaderWrites])
    · rw [header_other source table next 56 40 single.geometry.table (by decide) (by decide) (by decide)]
      exact single.fields (table+40#64,scalarNodesPointer table key cap) (by simp [singleHeaderWrites])
    · rw [header_other source table next 56 48 single.geometry.table (by decide) (by decide) (by decide)]
      exact single.fields (table+48#64,scalarOrderPointer table key cap) (by simp [singleHeaderWrites])
    · simp [putField,StoreWord.put]
    · rw [header_other source table next 56 64 single.geometry.table (by decide) (by decide) (by decide)]
      exact single.fields (table+64#64,2#64) (by simp [singleHeaderWrites])
    · rw [header_other source table next 56 72 single.geometry.table (by decide) (by decide) (by decide)]
      exact single.fields (table+72#64,0#64) (by simp [singleHeaderWrites])
    · rw [header_other source table next 56 80 single.geometry.table (by decide) (by decide) (by decide)]
      exact single.fields (table+80#64,cap) (by simp [singleHeaderWrites])
  · simpa only [putField,StoreWord.put,if_neg (nodeAway 0 (by decide))] using single.leafZero
  · simpa only [putField,StoreWord.put,if_neg (nodeAway 8 (by decide))] using single.leafValue
  · simpa only [putField,StoreWord.put,if_neg (nodeAway 16 (by decide))] using single.leafPosition
  · simpa only [putField,StoreWord.put,if_neg (nodeAway 24 (by decide))] using single.leafMarker
  · simpa only [putField,StoreWord.put,if_neg orderAway] using single.orderFirst

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

/-- A no-grow node allocation changes only the real next-index word,
so the scalar leaf's actual key-length/stride/base fields survive. -/
theorem ScalarFields.after_index {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table key : BitVec 64}
    (fields : ScalarFields source table key) (next : BitVec 64) : ScalarFields (New.putField source table 64 next) table key := by
  refine ⟨fields.domain,fields.arena,fields.aligned,?_,?_,?_⟩
  · have kept:=header_other source table next 64 0 fields.arena (by decide) (by decide) (by decide)
    simpa only [BitVec.add_zero] using kept.trans (by simpa only [BitVec.add_zero] using fields.length)
  · exact (header_other source table next 64 8 fields.arena (by decide) (by decide) (by decide)).trans fields.stride
  · exact (header_other source table next 64 32 fields.arena (by decide) (by decide) (by decide)).trans fields.keys

/-- All original leaf/order/count stores and the final return are finite
straight-line source work, including failed reads and stores. -/
theorem scalar_tail_quiet (code) : QuietClock.Preserves code afterCopy := by
  rw [shapes.2.2.2.2.1,shapes.2.2.2.2.2.1,shapes.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.1,
    shapes.2.2.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.2.2.2.2]
  repeat first | apply QuietClock.declared | apply QuietClock.sequence | apply QuietClock.store | apply QuietClock.returned

def scalarCopyEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key : BitVec 64) :=
  bind (bind source "klen" key) "stride" (New.strideWord key)

/-- Actual scalar copy arguments after the two real declarations. -/
theorem scalar_copy_arguments_at_node (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key pointer index : BitVec 64)
    (fields : ScalarFields source table key)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (nodeCell : source.locals.lookup (ofString "n")=some (.val (.word index)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer))) :
    evalListHOLFinite (scalarCopyEntry source key) (h:=fun address=>Classical.propDecidable ((scalarCopyEntry source key).memaddrs address)) copyArguments=
      some (CopyGeneral.values (New.keysPointer table+index*New.strideWord key) pointer key.toNat) := by
  let first:=bind source "klen" key
  let current:=scalarCopyEntry source key
  have firstTable : first.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other source "klen" "t" key (by decide)).trans tableCell
  have currentTable : current.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other first "stride" "t" (New.strideWord key) (by decide)).trans firstTable
  have currentNode : current.locals.lookup (ofString "n")=some (.val (.word index)):=
    (bind_lookup_other first "stride" "n" (New.strideWord key) (by decide)).trans ((bind_lookup_other source "klen" "n" key (by decide)).trans nodeCell)
  have currentKey : current.locals.lookup (ofString "key")=some (.val (.word pointer)):=
    (bind_lookup_other first "stride" "key" (New.strideWord key) (by decide)).trans ((bind_lookup_other source "klen" "key" key (by decide)).trans keyCell)
  have currentLength : current.locals.lookup (ofString "klen")=some (.val (.word key)):=
    (bind_lookup_other first "stride" "klen" (New.strideWord key) (by decide)).trans (bind_lookup_same _ _ _)
  have currentStride : current.locals.lookup (ofString "stride")=some (.val (.word (New.strideWord key))):=bind_lookup_same _ _ _
  have keysRead:=NewNode.field_read current table (New.keysPointer table) 32 fields.domain fields.arena fields.aligned (by decide) (by decide) currentTable fields.keys
  have destinationRead : eval current (.op .add [.load .one (NewNode.address 32),.panop .mul [localVar "n",localVar "stride"]])=
      some (.val (.word (New.keysPointer table+index*New.strideWord key))):=by
    simp only [eval] at keysRead ⊢
    rw [evalHOLExact]
    simp only [evalListHOLExact,keysRead]
    simp [evalHOLExact,evalListHOLExact,localVar,currentNode,currentStride,valueIsWord,valueWord,panOpHOL,wordOpHOL,wordOp]
  have args : evalListHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) copyArguments=
      some (CopyGeneral.values (New.keysPointer table+index*New.strideWord key) pointer key.toNat):=by
    have number : BitVec.ofNat 64 key.toNat=key:=by simp [BitVec.ofNat_toNat,BitVec.setWidth_eq]
    simp only [eval] at destinationRead
    simp only [copyArguments,CopyGeneral.values,evalListHOLFinite,evalListHOLExact,destinationRead]
    simp [evalHOLExact,localVar,currentKey,currentLength,number]
  exact args

theorem scalar_after_node_cost_at_node (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key pointer index : BitVec 64)
    (fields : ScalarFields source table key) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (nodeCell : source.locals.lookup (ofString "n")=some (.val (.word index)))
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
  have args:=scalar_copy_arguments_at_node source table key pointer index fields tableCell nodeCell keyCell
  rw [shapes.2.2.2.1]
  have front:=CopyAny.call_cost current copyArguments (New.keysPointer table+index*New.strideWord key) pointer key.toNat small args
    (CopyGeneral.original_code current.code installed)
  simpa only [current,scalarCopyEntry,first,Nat.add_zero] using ClockCost.sequence_current current _ afterCopy (CopyAny.price key.toNat+1) 0 front
    (ClockCost.of_quiet current.code afterCopy (scalar_tail_quiet current.code))

/-- Every actual scalar leaf construction with an available no-grow
node has the same width-dependent bound. Neither key contents nor a future
successful copy is assumed; the allocated node may be any current index. -/
theorem scalar_no_grow_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer next : BitVec 64)
    (fields : ScalarFields source table key) (ready : NewNode.Context source table next cap)
    (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer))) (small : key.toNat+32<2^64) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤CopyAny.price key.toNat+2 := by
  let output:=evaluateHOLFiniteState source body
  have actual : evaluateHOLFiniteState source body=(output.1,output.2):=rfl
  rw [shapes.1] at actual
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "t"]=some [.val (.word table)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,tableCell]
  rcases NewNode.scoped_trace source output.2 table next cap ready installed "n" [localVar "t"] afterNode args output.1 actual with stopped|reached
  · change source.clock-output.2.clock≤CopyAny.price key.toNat+2
    have bound:=stopped.1
    omega
  · obtain ⟨target,inner,frame,forward,price,continued,endpoint⟩:=reached
    let current:=CallNormal.continuationEntry source target "n" (.val (.word next))
    have currentFields : ScalarFields current table key:=(fields.after_index (next+1#64)).of_frame frame
    have currentTable : current.locals.lookup (ofString "t")=some (.val (.word table)):=
      (CallNormal.continuation_lookup_other source target "n" "t" (.val (.word next)) (by decide)).trans tableCell
    have currentKey : current.locals.lookup (ofString "key")=some (.val (.word pointer)):=
      (CallNormal.continuation_lookup_other source target "n" "key" (.val (.word next)) (by decide)).trans keyCell
    have code:=congrArg PanSemStateFiniteExact.code frame
    change current.code=source.code at code
    have cost:=scalar_after_node_cost_at_node current table key pointer next currentFields (by rw [code]; exact installed)
      currentTable (CallNormal.continuation_lookup_same source target "n" (.val (.word next))) currentKey small
    rw [continued] at cost
    change current.clock-inner.clock≤CopyAny.price key.toNat+1 at cost
    have entryClock : current.clock=target.clock:=rfl
    have exitClock : output.2.clock=inner.clock:=by rw [endpoint] <;> rfl
    change source.clock-output.2.clock≤CopyAny.price key.toNat+2
    omega

/-- The original first-leaf bound is an instance of the same current
no-grow scalar constructor, with index1 derived from the empty image. -/
theorem scalar_empty_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer : BitVec 64)
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer))) (small : key.toNat+32<2^64) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤CopyAny.price key.toNat+2 := by
  have fields : ScalarFields source table key:=⟨image.domain,image.geometry.table,image.aligned,
    by simpa only [BitVec.add_zero] using image.fields (table+0#64,key) (by simp [New.scalarWrites]),
    image.fields (table+8#64,New.strideWord key) (by simp [New.scalarWrites]),
    image.fields (table+32#64,New.keysPointer table) (by simp [New.scalarWrites])⟩
  exact scalar_no_grow_cost source table key cap pointer 1#64 fields (NewNode.from_scalar_empty image) installed tableCell keyCell small

/-- Actual singleton metadata supplies node2 and every scalar header read
needed by the next original leaf construction. -/
theorem scalar_single_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer root value : BitVec 64)
    (single : New.ScalarSingle source table key cap root value) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤CopyAny.price key.toNat+2 := by
  have fields : ScalarFields source table key:=⟨single.domain,single.geometry.table,single.aligned,
    by simpa only [BitVec.add_zero] using single.fields (table+0#64,key) (by simp [New.singleHeaderWrites]),
    single.fields (table+8#64,New.strideWord key) (by simp [New.singleHeaderWrites]),
    single.fields (table+32#64,New.keysPointer table) (by simp [New.singleHeaderWrites])⟩
  have ready : NewNode.Context source table 2#64 cap:=⟨single.domain,single.geometry.table,single.aligned,
    single.fields (table+72#64,0#64) (by simp [New.singleHeaderWrites]),
    single.fields (table+64#64,2#64) (by simp [New.singleHeaderWrites]),
    single.fields (table+80#64,cap) (by simp [New.singleHeaderWrites]),single.capLower⟩
  exact scalar_no_grow_cost source table key cap pointer 2#64 fields ready installed tableCell keyCell (by have small:=single.keySmall; omega)

/-- Canonical real continuation after an arbitrary no-grow node call. -/
def scalarNodeEntryAt (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table next : BitVec 64) :=
  bind (New.putField {source with clock:=source.clock-1} table 64 (next+1#64)) "n" next

/-- Funded actual node allocation resumes the original scalar leaf body
with its own returned index and real metadata increment. -/
theorem scalar_prefix_execute_at (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table next cap : BitVec 64)
    (ready : NewNode.Context source table next cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table))) (funded : 1≤source.clock) :
    evaluateHOLFiniteState source body=
      let output:=evaluateHOLFiniteState (scalarNodeEntryAt source table next) afterNode
      (output.1,restore source "n" output.2) := by
  obtain ⟨callee,called,tCell⟩:=word_environment source.code.lookup (ofString "htab_new_node") (ofString "t")
    NewNode.body .one table (NewNode.original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have current : NewNode.Context entry table next cap:=ready.of_frame rfl
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "t"]=some [.val (.word table)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,tableCell]
  have run:=CallNormal.return_execute source (NewNode.returnedState entry table next) "n" .one (ofString "htab_new_node")
    [localVar "t"] [.val (.word table)] NewNode.body afterNode callee .one (.val (.word next)) args called funded
    (current.execute tCell) (by simp [shapeOfHOLExact,shapeEqHOL])
  have resumed : CallNormal.continuationEntry source (NewNode.returnedState entry table next) "n" (.val (.word next))=scalarNodeEntryAt source table next:=rfl
  rw [shapes.1,run,resumed]

/-- A genuine normal leaf return exposes the exact variable-index copy
entry; the actual call provides its own funding and real header reads. -/
theorem scalar_copy_trace_at {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap next : BitVec 64}
    (fields : ScalarFields source table key) (ready : NewNode.Context source table next cap)
    (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    1≤source.clock ∧ ∃ inner,evaluateHOLFiniteState (scalarCopyEntry (scalarNodeEntryAt source table next) key) copyPhase=(some (.returned value),inner) ∧
      LocalEffects.erase post=LocalEffects.erase inner ∧ post.clock=inner.clock := by
  obtain ⟨callee,called,tCell⟩:=word_environment source.code.lookup (ofString "htab_new_node") (ofString "t")
    NewNode.body .one table (NewNode.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "t"]=some [.val (.word table)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,tableCell]
  have expanded:=normal
  rw [shapes.1] at expanded
  have funded:=(CallNormal.scoped_normal source post "n" .one (ofString "htab_new_node") [localVar "t"] [.val (.word table)] NewNode.body afterNode callee .one args called value expanded).1
  let current:=scalarNodeEntryAt source table next
  let output:=evaluateHOLFiniteState current afterNode
  have actual:=scalar_prefix_execute_at source table next cap ready installed tableCell funded
  have observed:=congrArg Prod.fst (normal.symm.trans actual)
  have endpoint:=congrArg Prod.snd (normal.symm.trans actual)
  change post=restore source "n" output.2 at endpoint
  have run : evaluateHOLFiniteState current afterNode=(some (.returned value),output.2):=Prod.ext observed.symm rfl
  have currentFields : ScalarFields current table key:=(fields.after_index (next+1#64)).of_frame rfl
  have currentTable : current.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other _ "n" "t" next (by decide)).trans tableCell
  have lengthRead:=NewNode.field_read current table key 0 currentFields.domain currentFields.arena currentFields.aligned (by decide) (by decide) currentTable (by simpa only [BitVec.add_zero] using currentFields.length)
  rw [shapes.2.1] at run
  obtain ⟨middle,continued,middleEq⟩:=ScalarScope.declare_trace current output.2 "klen" _ key afterLength (some (.returned value)) lengthRead run
  let first:=bind current "klen" key
  have firstTable : first.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other _ "klen" "t" key (by decide)).trans currentTable
  have strideRead:=NewNode.field_read first table (New.strideWord key) 8 currentFields.domain currentFields.arena currentFields.aligned (by decide) (by decide) firstTable currentFields.stride
  rw [shapes.2.2.1] at continued
  obtain ⟨inner,copyRun,innerEq⟩:=ScalarScope.declare_trace first middle "stride" _ (New.strideWord key) copyPhase (some (.returned value)) strideRead continued
  exact ⟨funded,inner,copyRun,by rw [endpoint,middleEq,innerEq]; rfl,by rw [endpoint,middleEq,innerEq]; rfl⟩

/-- Actual memcpy completion at any available scalar leaf retains its
full span frame, saved locals and the real remaining stores. -/
theorem scalar_copied_returned_at {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap next pointer : BitVec 64}
    (fields : ScalarFields source table key) (ready : NewNode.Context source table next cap)
    (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer))) (small : key.toNat+32<2^64)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ copied inner,Copy32Span.Frame (scalarCopyEntry (scalarNodeEntryAt source table next) key) copied (New.scalarKeyAt table key next) key.toNat ∧
      copied.locals=(scalarCopyEntry (scalarNodeEntryAt source table next) key).locals ∧
      evaluateHOLFiniteState copied afterCopy=(some (.returned value),inner) ∧
      LocalEffects.erase post=LocalEffects.erase inner ∧ post.clock=inner.clock := by
  obtain ⟨funded,middle,copyRun,scope,clock⟩:=scalar_copy_trace_at fields ready installed tableCell value normal
  rw [shapes.2.2.2.1] at copyRun
  let node:=scalarNodeEntryAt source table next
  let current:=scalarCopyEntry node key
  obtain ⟨copied,called,remaining⟩:=sequence_returned current middle (.call (some (none,none)) (ofString "memcpy") copyArguments) afterCopy value
    (NoReturn.ignored_call (ofString "memcpy") copyArguments current) copyRun
  have currentFields : ScalarFields node table key:=(fields.after_index (next+1#64)).of_frame rfl
  have currentTable : node.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other _ "n" "t" next (by decide)).trans tableCell
  have currentKey : node.locals.lookup (ofString "key")=some (.val (.word pointer)):=
    (bind_lookup_other _ "n" "key" next (by decide)).trans keyCell
  have args:=scalar_copy_arguments_at_node node table key pointer next currentFields currentTable (bind_lookup_same _ _ _) currentKey
  obtain ⟨frame,locals⟩:=CopyAny.call_span_normal current copied (New.scalarKeyAt table key next) pointer key.toNat small copyArguments args installed called
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

/-- Exact physical state after the actual key copy at any no-grow index.
The copy contents are unrestricted; metadata and external memory are derived. -/
structure ScalarCopiedAt (source copied : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap next : BitVec 64) : Prop where
  fields : MemoryMetadata.erase copied=MemoryMetadata.erase source
  locals : copied.locals=(scalarCopyEntry (scalarNodeEntryAt source table next) key).locals
  header : ∀ offset : Nat,offset<88→copied.memory (table+BitVec.ofNat 64 offset)=
    (New.putField source table 64 (next+1#64)).memory (table+BitVec.ofNat 64 offset)
  outside : ∀ query : BitVec 64,New.OutsideScalar table key cap query→copied.memory query=source.memory query
  afterNodes : ∀ query : BitVec 64,(New.scalarNodesPointer table key cap).toNat≤query.toNat→copied.memory query=source.memory query

/-- Every normally returned current scalar leaf derives this copied state
from the same node call and memcpy, including index2 on a singleton table. -/
theorem scalar_copied_state_at {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap next pointer : BitVec 64}
    (fields : ScalarFields source table key) (ready : NewNode.Context source table next cap)
    (geometry : New.ScalarGeometry table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (keySmall : key.toNat≤60) (capSmall : cap.toNat≤2^32) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ copied inner,ScalarCopiedAt source copied table key cap next ∧
      evaluateHOLFiniteState copied afterCopy=(some (.returned value),inner) ∧
      LocalEffects.erase post=LocalEffects.erase inner ∧ post.clock=inner.clock := by
  obtain ⟨copied,inner,frame,locals,remaining,scope,clock⟩:=scalar_copied_returned_at fields ready installed tableCell keyCell (by omega) value normal
  obtain ⟨owned,aligned,afterHeader,beforeNodes⟩:=geometry.key_copy keySmall capSmall next ready.room
  refine ⟨copied,inner,⟨frame.fields,locals,?_,?_,?_⟩,remaining,scope,clock⟩
  · intro offset inside
    have number:=byteAddress_toNat table offset (by have upper:=geometry.table.upper; omega)
    change (table+BitVec.ofNat 64 offset).toNat=table.toNat+offset at number
    exact frame.memory _ (CopyGeneral.Away.after _ _ _ aligned (by have upper:=owned.upper; omega) (by rw [number]; omega))
  · intro query outside
    rw [frame.memory query (geometry.key_copy_away keySmall capSmall next ready.room query outside)]
    have different : query≠table+64#64:=by
      have number:=byteAddress_toNat table 64 (by have upper:=geometry.table.upper; omega)
      change (table+64#64).toNat=table.toNat+64 at number
      have bound:=geometry.header_before_end
      intro same
      have equal:=congrArg BitVec.toNat same
      rw [number] at equal
      rcases outside with before|after <;> omega
    exact if_neg different

  · intro query later
    rw [frame.memory query (CopyGeneral.Away.before _ query key.toNat (New.scalarNodesPointer table key cap).toNat
      beforeNodes (New.scalarNodesPointer table key cap).isLt later)]
    have number : (table+64#64).toNat=table.toNat+64:=byteAddress_toNat table 64 (by have upper:=geometry.table.upper; omega)
    have beforeHeader:=geometry.tableBefore
    have beforeKeys:=geometry.keysBefore
    have different : query≠table+64#64:=by
      intro same
      have equal:=congrArg BitVec.toNat same
      rw [number] at equal
      omega
    exact if_neg different

/-- The actual remaining constructor reads its own count and array pointers,
then executes all stores at the same allocated node and order position. -/
theorem ScalarCopiedAt.after_copy_execute {source copied : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap next pos value : BitVec 64}
    (physical : ScalarCopiedAt source copied table key cap next)
    (ready : NewNode.Context source table next cap) (geometry : New.ScalarGeometry table key cap)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value))) (capSmall : cap.toNat≤2^32)
    (posInside : pos.toNat≤cap.toNat)
    (nodesCell : source.memory (table+40#64)=.word (New.scalarNodesPointer table key cap))
    (countCell : source.memory (table+24#64)=.word pos)
    (orderCell : source.memory (table+48#64)=.word (New.scalarOrderPointer table key cap)) :
    evaluateHOLFiniteState copied afterCopy=
      (some (.returned (.val (.word next))),restore copied "nodes"
        (scalarStoresReturned (bind copied "nodes" (New.scalarNodesPointer table key cap)) table key cap next pos value)) := by
  have header (offset : Nat) (inside : offset<88) (different : offset≠64) :
      copied.memory (table+BitVec.ofNat 64 offset)=source.memory (table+BitVec.ofNat 64 offset):=
    (physical.header offset inside).trans (header_other source table (next+1#64) 64 offset geometry.table (by decide) inside different)
  have tableCopied : copied.locals.lookup (ofString "t")=some (.val (.word table)):=by
    rw [physical.locals]
    simpa [scalarCopyEntry,scalarNodeEntryAt,QueryBranch.bind,New.putField,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using tableCell
  have valueCopied : copied.locals.lookup (ofString "value")=some (.val (.word value)):=by
    rw [physical.locals]
    simpa [scalarCopyEntry,scalarNodeEntryAt,QueryBranch.bind,New.putField,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using valueCell
  have nodeCopied : copied.locals.lookup (ofString "n")=some (.val (.word next)):=by
    rw [physical.locals]
    simp [scalarCopyEntry,scalarNodeEntryAt,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
  have lengthCopied : copied.locals.lookup (ofString "klen")=some (.val (.word key)):=by
    rw [physical.locals]
    simp [scalarCopyEntry,scalarNodeEntryAt,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
  have domain : copied.memaddrs=InitE.ordinaryDomain:=(MemoryMetadata.domain physical.fields).trans ready.domain
  have currentNodes : copied.memory (table+40#64)=.word (New.scalarNodesPointer table key cap):=
    (header 40 (by decide) (by decide)).trans nodesCell
  have currentCount : copied.memory (table+24#64)=.word pos:=
    (header 24 (by decide) (by decide)).trans countCell
  have currentOrder : copied.memory (table+48#64)=.word (New.scalarOrderPointer table key cap):=
    (header 48 (by decide) (by decide)).trans orderCell
  have nodesRead:=NewNode.field_read copied table (New.scalarNodesPointer table key cap) 40 domain geometry.table ready.aligned (by decide) (by decide) tableCopied currentNodes
  let entered:=bind copied "nodes" (New.scalarNodesPointer table key cap)
  have locals : ScalarLocals entered table key (New.scalarNodesPointer table key cap) next value:=
    ⟨(bind_lookup_other _ "nodes" "t" _ (by decide)).trans tableCopied,bind_lookup_same _ _ _,
      (bind_lookup_other _ "nodes" "n" _ (by decide)).trans nodeCopied,
      (bind_lookup_other _ "nodes" "value" _ (by decide)).trans valueCopied,
      (bind_lookup_other _ "nodes" "klen" _ (by decide)).trans lengthCopied⟩
  have storesRun:=scalar_stores_execute entered table key cap next pos value domain geometry ready.aligned capSmall ready.room posInside locals currentCount currentOrder
  rw [shapes.2.2.2.2.1]
  exact ScalarScope.declare_execute copied _ "nodes" _ (New.scalarNodesPointer table key cap) stores (some (.returned (.val (.word next)))) nodesRead storesRun

/-- Complete actual no-grow scalar-leaf return, with the exact stored
snapshot from its own copied state and all actual metadata/order writes. -/
theorem scalar_no_grow_returned {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap next pos pointer value : BitVec 64}
    (fields : ScalarFields source table key) (ready : NewNode.Context source table next cap)
    (geometry : New.ScalarGeometry table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (keySmall : key.toNat≤60) (capSmall : cap.toNat≤2^32) (posInside : pos.toNat≤cap.toNat)
    (nodesCell : source.memory (table+40#64)=.word (New.scalarNodesPointer table key cap))
    (countCell : source.memory (table+24#64)=.word pos)
    (orderCell : source.memory (table+48#64)=.word (New.scalarOrderPointer table key cap))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    returned=.val (.word next) ∧ ∃ copied,ScalarCopiedAt source copied table key cap next ∧
      LocalEffects.erase post=LocalEffects.erase (scalarStored copied table key cap next pos value) := by
  obtain ⟨copied,inner,physical,remaining,scope,clock⟩:=scalar_copied_state_at fields ready geometry installed tableCell keyCell keySmall capSmall returned normal
  have actual:=physical.after_copy_execute ready geometry tableCell valueCell capSmall posInside nodesCell countCell orderCell
  have result:=congrArg Prod.fst (remaining.symm.trans actual)
  have answer : returned=.val (.word next):=by simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using result
  have endpoint:=congrArg Prod.snd (remaining.symm.trans actual)
  have memory:=congrArg LocalEffects.erase endpoint
  change LocalEffects.erase inner=LocalEffects.erase (scalarStored copied table key cap next pos value) at memory
  exact ⟨answer,copied,physical,scope.trans memory⟩

/-- Complete normally returned first scalar leaf: its actual copy state
and all subsequent real writes, with no future-copy/store result assumed. -/
theorem scalar_empty_returned {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer value : BitVec 64}
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (keySmall : key.toNat≤60) (capSmall : cap.toNat≤2^32) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    returned=.val (.word 1#64) ∧ ∃ copied,ScalarCopiedAt source copied table key cap 1#64 ∧
      LocalEffects.erase post=LocalEffects.erase (scalarStored copied table key cap 1#64 0#64 value) := by
  have fields : ScalarFields source table key:=⟨image.domain,image.geometry.table,image.aligned,
    by simpa only [BitVec.add_zero] using image.fields (table+0#64,key) (by simp [New.scalarWrites]),
    image.fields (table+8#64,New.strideWord key) (by simp [New.scalarWrites]),
    image.fields (table+32#64,New.keysPointer table) (by simp [New.scalarWrites])⟩
  exact scalar_no_grow_returned fields (NewNode.from_scalar_empty image) image.geometry installed tableCell keyCell valueCell keySmall capSmall
    (by change 0≤cap.toNat; omega)
    (image.fields (table+40#64,New.scalarNodesPointer table key cap) (by simp [New.scalarWrites]))
    (image.fields (table+24#64,0#64) (by simp [New.scalarWrites]))
    (image.fields (table+48#64,New.scalarOrderPointer table key cap) (by simp [New.scalarWrites])) returned normal

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


/-- The actual leaf node stores are disjoint from the table/order arrays. -/
theorem scalar_stored_nodes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap value : BitVec 64)
    (geometry : New.ScalarGeometry table key cap) (capSmall : cap.toNat≤2^32) (capLower : 2≤cap.toNat) :
    (scalarStored source table key cap 1#64 0#64 value).memory (FindLeaf.cell (New.scalarNodesPointer table key cap) 1#64 0)=.word 0#64 ∧
    (scalarStored source table key cap 1#64 0#64 value).memory (FindLeaf.cell (New.scalarNodesPointer table key cap) 1#64 8)=.word value ∧
    (scalarStored source table key cap 1#64 0#64 value).memory (FindLeaf.cell (New.scalarNodesPointer table key cap) 1#64 16)=.word 0#64 ∧
    (scalarStored source table key cap 1#64 0#64 value).memory (FindLeaf.cell (New.scalarNodesPointer table key cap) 1#64 24)=.word (key*8#64) := by
  have inside : (1#64 : BitVec 64).toNat≤cap.toNat:=by change 1≤cap.toNat; omega
  have nodes : AllocatedBytes.Arena (New.scalarNodesPointer table key cap) (32*(cap.toNat+1)):=by simpa only [(New.size_numbers cap capSmall).1] using geometry.nodes
  have different (left right : Nat) (li : left<32) (ri : right<32) (ne : left≠right) :
      FindLeaf.cell (New.scalarNodesPointer table key cap) 1#64 left≠FindLeaf.cell (New.scalarNodesPointer table key cap) 1#64 right:=by
    intro same
    exact ne (cell_injective _ _ _ cap left right nodes inside inside li ri same).2
  have headerAway (offset : Nat) (small : offset<32) : FindLeaf.cell (New.scalarNodesPointer table key cap) 1#64 offset≠table+24#64:=
    Ne.symm (geometry.scalar_header_away capSmall 1#64 inside offset 24 small (by decide))
  have orderAway (offset : Nat) (small : offset<32) : FindLeaf.cell (New.scalarNodesPointer table key cap) 1#64 offset≠New.scalarOrderPointer table key cap:=by
    have number:=cell_number _ 1#64 cap offset nodes inside small
    have before:=geometry.nodesBefore
    rw [(New.size_numbers cap capSmall).1] at before
    intro same
    have equal:=congrArg BitVec.toNat same
    rw [number] at equal
    change (New.scalarNodesPointer table key cap).toNat+32*1+offset=(New.scalarOrderPointer table key cap).toNat at equal
    omega
  have orderZero : slot (New.scalarOrderPointer table key cap) 0#64 8=New.scalarOrderPointer table key cap:=by simp [slot]
  repeat' constructor
  all_goals simp [scalarStored,scalarTailStored,scalarPutOrder,putNode,New.putField,StoreWord.put,orderZero,headerAway,orderAway,different]

theorem scalar_stored_order (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap value : BitVec 64)
    (geometry : New.ScalarGeometry table key cap) :
    (scalarStored source table key cap 1#64 0#64 value).memory (New.scalarOrderPointer table key cap)=.word 1#64 := by
  have away : New.scalarOrderPointer table key cap≠table+24#64:=by
    have number:=byteAddress_toNat table 24 (by have upper:=geometry.table.upper; omega)
    change (table+24#64).toNat=table.toNat+24 at number
    have first:=geometry.tableBefore
    have second:=geometry.keysBefore
    have third:=geometry.nodesBefore
    intro same
    have equal:=congrArg BitVec.toNat same
    rw [number] at equal
    omega
  simp [scalarStored,scalarTailStored,scalarPutOrder,New.putField,StoreWord.put,slot,away]

/-- The actual post-copy stores at any available leaf and order position
change only the count word in the real header. -/
theorem scalar_stored_header_at (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap node pos value : BitVec 64)
    (geometry : New.ScalarGeometry table key cap) (capSmall : cap.toNat≤2^32)
    (inside : node.toNat≤cap.toNat) (posInside : pos.toNat≤cap.toNat) (offset : Nat) (small : offset<88) :
    (scalarStored source table key cap node pos value).memory (table+BitVec.ofNat 64 offset)=
      (New.putField source table 24 (pos+1#64)).memory (table+BitVec.ofNat 64 offset) := by
  have nodesAway (field : Nat) (inNode : field<32) : table+BitVec.ofNat 64 offset≠FindLeaf.cell (New.scalarNodesPointer table key cap) node field:=
    geometry.scalar_header_away capSmall node inside field offset inNode small
  have orderArray : AllocatedBytes.Arena (New.scalarOrderPointer table key cap) (8*(cap.toNat+1)):=by
    simpa only [(New.size_numbers cap capSmall).2] using geometry.order
  have orderAway : table+BitVec.ofNat 64 offset≠slot (New.scalarOrderPointer table key cap) pos 8:=by
    have number:=byteAddress_toNat table offset (by have upper:=geometry.table.upper; omega)
    change (table+BitVec.ofNat 64 offset).toNat=table.toNat+offset at number
    have orderNumber:=slot_number _ pos cap 8 orderArray posInside
    have first:=geometry.tableBefore
    have second:=geometry.keysBefore
    have third:=geometry.nodesBefore
    intro same
    have equal:=congrArg BitVec.toNat same
    rw [number,orderNumber] at equal
    omega
  simp only [scalarStored,scalarTailStored,scalarPutOrder,putNode,New.putField,StoreWord.put,
    if_neg orderAway,if_neg (nodesAway 0 (by decide)),if_neg (nodesAway 8 (by decide)),if_neg (nodesAway 16 (by decide)),if_neg (nodesAway 24 (by decide))]

/-- The whole normal original scalar constructor derives its real node,
all final header words and the complete external memory frame. -/
theorem scalar_no_grow_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap next pos pointer value : BitVec 64}
    (fields : ScalarFields source table key) (ready : NewNode.Context source table next cap)
    (geometry : New.ScalarGeometry table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (keySmall : key.toNat≤60) (capSmall : cap.toNat≤2^32) (posInside : pos.toNat≤cap.toNat)
    (nodesCell : source.memory (table+40#64)=.word (New.scalarNodesPointer table key cap))
    (countCell : source.memory (table+24#64)=.word pos)
    (orderCell : source.memory (table+48#64)=.word (New.scalarOrderPointer table key cap))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    returned=.val (.word next) ∧ New.ScalarFrame source post table key cap ∧
      ∀ offset : Nat,offset<88→post.memory (table+BitVec.ofNat 64 offset)=
        (New.putField (New.putField source table 64 (next+1#64)) table 24 (pos+1#64)).memory (table+BitVec.ofNat 64 offset) := by
  obtain ⟨answer,copied,physical,scope⟩:=scalar_no_grow_returned fields ready geometry installed tableCell keyCell valueCell keySmall capSmall posInside nodesCell countCell orderCell returned normal
  have metadata:=MemoryMetadata.of_frame scope
  have finalMetadata:=metadata.trans (scalar_stored_metadata copied table key cap next pos value)
  have memory:=LocalEffects.memory_of_erase (scalarStored copied table key cap next pos value) post scope
  refine ⟨answer,⟨finalMetadata.trans physical.fields,?_⟩,?_⟩
  · intro query outside
    rw [memory]
    exact (scalar_stored_outside copied table key cap next pos value geometry capSmall ready.room posInside query outside).trans (physical.outside query outside)
  · intro offset inside
    rw [memory,scalar_stored_header_at copied table key cap next pos value geometry capSmall ready.room posInside offset inside]
    change (if table+BitVec.ofNat 64 offset=table+24#64 then .word (pos+1#64) else copied.memory (table+BitVec.ofNat 64 offset))=
      (if table+BitVec.ofNat 64 offset=table+24#64 then .word (pos+1#64) else (New.putField source table 64 (next+1#64)).memory (table+BitVec.ofNat 64 offset))
    split
    · rfl
    · exact physical.header offset inside

/-- The actual second scalar leaf supplies the next internal-node call
with node3 and the same real node-array pointer/capacity/free-list metadata. -/
theorem scalar_single_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer root old value : BitVec 64}
    (single : New.ScalarSingle source table key cap root old) (available : 3≤cap.toNat)
    (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    returned=.val (.word 2#64) ∧ New.ScalarFrame source post table key cap ∧
      NewNode.Context post table 3#64 cap ∧ post.memory (table+40#64)=.word (New.scalarNodesPointer table key cap) := by
  have fields : ScalarFields source table key:=⟨single.domain,single.geometry.table,single.aligned,
    by simpa only [BitVec.add_zero] using single.fields (table+0#64,key) (by simp [New.singleHeaderWrites]),
    single.fields (table+8#64,New.strideWord key) (by simp [New.singleHeaderWrites]),
    single.fields (table+32#64,New.keysPointer table) (by simp [New.singleHeaderWrites])⟩
  have ready : NewNode.Context source table 2#64 cap:=⟨single.domain,single.geometry.table,single.aligned,
    single.fields (table+72#64,0#64) (by simp [New.singleHeaderWrites]),
    single.fields (table+64#64,2#64) (by simp [New.singleHeaderWrites]),
    single.fields (table+80#64,cap) (by simp [New.singleHeaderWrites]),single.capLower⟩
  have nodesCell:=single.fields (table+40#64,New.scalarNodesPointer table key cap) (by simp [New.singleHeaderWrites])
  have countCell:=single.fields (table+24#64,1#64) (by simp [New.singleHeaderWrites])
  have orderCell:=single.fields (table+48#64,New.scalarOrderPointer table key cap) (by simp [New.singleHeaderWrites])
  obtain ⟨answer,frame,header⟩:=scalar_no_grow_frame fields ready single.geometry installed tableCell keyCell valueCell single.keySmall single.capSmall
    (pos:=1#64) (by change 1≤cap.toNat; omega) nodesCell countCell orderCell returned normal
  change ∀ offset : Nat,offset<88→post.memory (table+BitVec.ofNat 64 offset)=
    (New.putField (New.putField source table 64 3#64) table 24 2#64).memory (table+BitVec.ofNat 64 offset) at header
  have kept (offset : Nat) (inside : offset<88) (notCount : offset≠24) (notNext : offset≠64) :
      post.memory (table+BitVec.ofNat 64 offset)=source.memory (table+BitVec.ofNat 64 offset):=by
    rw [header offset inside,
      header_other (New.putField source table 64 3#64) table 2#64 24 offset single.geometry.table (by decide) inside notCount,
      header_other source table 3#64 64 offset single.geometry.table (by decide) inside notNext]
  refine ⟨answer,frame,⟨(MemoryMetadata.domain frame.fields).trans single.domain,single.geometry.table,single.aligned,?_,?_,?_,available⟩,
    (kept 40 (by decide) (by decide) (by decide)).trans nodesCell⟩
  · exact (kept 72 (by decide) (by decide) (by decide)).trans (single.fields (table+72#64,0#64) (by simp [New.singleHeaderWrites]))
  · rw [header 64 (by decide),header_other (New.putField source table 64 3#64) table 2#64 24 64 single.geometry.table (by decide) (by decide) (by decide)]
    simp [New.putField,StoreWord.put]
  · exact (kept 80 (by decide) (by decide) (by decide)).trans (single.fields (table+80#64,cap) (by simp [New.singleHeaderWrites]))

/-- The actual second-leaf caller retains its real allocator metadata
and continues with node2; every stopped outcome has the same scalar price. -/
theorem scoped_scalar_single_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table key cap pointer root old value : BitVec 64) (single : New.ScalarSingle source table key cap root old)
    (available : 3≤cap.toNat) (installed : OriginalCode.Installed source.code)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word table),.val (.word pointer),.val (.word value)])
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_new_leaf") arguments continuation)=(outcome,post)) :
    (source.clock-post.clock≤CopyAny.price key.toNat+3 ∧ ∀ returned,outcome≠some (.returned returned)) ∨
      ∃ target inner,New.ScalarFrame source target table key cap ∧ NewNode.Context target table 3#64 cap ∧
        target.memory (table+40#64)=.word (New.scalarNodesPointer table key cap) ∧
        target.clock≤source.clock ∧ source.clock-target.clock≤CopyAny.price key.toNat+3 ∧
        evaluateHOLFiniteState (CallNormal.continuationEntry source target name (.val (.word 2#64))) continuation=(outcome,inner) ∧
        post=restore source name inner := by
  obtain ⟨callee,called,tCell,kCell,vCell⟩:=word_triple_environment source.code.lookup (ofString "htab_new_leaf")
    (ofString "t") (ofString "key") (ofString "value") body .one table pointer value
    (by decide) (by decide) (by decide) (original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have currentSingle : New.ScalarSingle entry table key cap root old:=single.of_erase rfl
  have price:=scalar_single_cost entry table key cap pointer root old currentSingle installed tCell kCell
  rcases CallNormal.scoped_classified source post name .one (ofString "htab_new_leaf") arguments _ body continuation callee .one (CopyAny.price key.toNat+2)
    args called price outcome run with stopped|reached
  · exact Or.inl ⟨by have cost:=stopped.1; omega,stopped.2⟩
  · obtain ⟨target,returned,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩:=reached
    obtain ⟨answer,frame,ready,nodesCell⟩:=scalar_single_frame currentSingle available installed tCell kCell vCell returned bodyRun
    rw [answer] at continued
    exact Or.inr ⟨target,inner,frame.of_erase rfl rfl,ready,nodesCell,forward,by omega,continued,endpoint⟩

/-- Only the count word changes during actual post-copy leaf stores. -/
theorem scalar_stored_header (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap value : BitVec 64)
    (geometry : New.ScalarGeometry table key cap) (capSmall : cap.toNat≤2^32) (capLower : 2≤cap.toNat)
    (offset : Nat) (small : offset<88) :
    (scalarStored source table key cap 1#64 0#64 value).memory (table+BitVec.ofNat 64 offset)=
      (New.putField source table 24 1#64).memory (table+BitVec.ofNat 64 offset) := by
  have inside : (1#64 : BitVec 64).toNat≤cap.toNat:=by change 1≤cap.toNat; omega
  have nodesAway (field : Nat) (inNode : field<32) : table+BitVec.ofNat 64 offset≠FindLeaf.cell (New.scalarNodesPointer table key cap) 1#64 field:=
    geometry.scalar_header_away capSmall 1#64 inside field offset inNode small
  have orderAway : table+BitVec.ofNat 64 offset≠New.scalarOrderPointer table key cap:=by
    have number:=byteAddress_toNat table offset (by have upper:=geometry.table.upper; omega)
    change (table+BitVec.ofNat 64 offset).toNat=table.toNat+offset at number
    have first:=geometry.tableBefore
    have second:=geometry.keysBefore
    have third:=geometry.nodesBefore
    intro same
    have equal:=congrArg BitVec.toNat same
    rw [number] at equal
    omega
  have orderZero : slot (New.scalarOrderPointer table key cap) 0#64 8=New.scalarOrderPointer table key cap:=by simp [slot]
  simp only [scalarStored,scalarTailStored,scalarPutOrder,putNode,New.putField,StoreWord.put,orderZero,
    if_neg orderAway,if_neg (nodesAway 0 (by decide)),if_neg (nodesAway 8 (by decide)),if_neg (nodesAway 16 (by decide)),if_neg (nodesAway 24 (by decide))]
  rfl

/-- Expose the SINGLE actual initialized leaf and header produced by this
same normal helper execution. The copied key bytes are not guessed. -/
theorem scalar_empty_single {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer value : BitVec 64}
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (keySmall : key.toNat≤60) (capSmall : cap.toNat≤2^32) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    returned=.val (.word 1#64) ∧ New.ScalarFrame source post table key cap ∧ New.ScalarSingle post table key cap 0#64 value := by
  obtain ⟨answer,frame⟩:=scalar_empty_frame image installed tableCell keyCell valueCell keySmall capSmall returned normal
  obtain ⟨actual,copied,physical,scope⟩:=scalar_empty_returned image installed tableCell keyCell valueCell keySmall capSmall returned normal
  have memory:=LocalEffects.memory_of_erase (scalarStored copied table key cap 1#64 0#64 value) post scope
  have copiedHeader (offset : Nat) (inside : offset<88) : copied.memory (table+BitVec.ofNat 64 offset)=
      (New.putField source table 64 2#64).memory (table+BitVec.ofNat 64 offset):=by
    simpa only [show (1#64 : BitVec 64)+1#64=2#64 from by decide] using physical.header offset inside
  have nodes:=scalar_stored_nodes copied table key cap value image.geometry capSmall image.capLower
  have order:=scalar_stored_order copied table key cap value image.geometry
  have oldHeader (offset : Nat) (inside : offset<88) (notCount : offset≠24) (notNext : offset≠64) :
      (scalarStored copied table key cap 1#64 0#64 value).memory (table+BitVec.ofNat 64 offset)=source.memory (table+BitVec.ofNat 64 offset) := by
    rw [scalar_stored_header copied table key cap value image.geometry capSmall image.capLower offset inside,
      header_other copied table 1#64 24 offset image.geometry.table (by decide) inside notCount,copiedHeader offset inside,
      header_other source table 2#64 64 offset image.geometry.table (by decide) inside notNext]
  refine ⟨answer,frame,⟨image.geometry,image.aligned,(MemoryMetadata.domain frame.fields).trans image.domain,image.capLower,keySmall,capSmall,?_,?_,?_,?_,?_,?_⟩⟩
  · intro entry member
    rw [memory]
    simp only [New.singleHeaderWrites,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · rw [oldHeader 0 (by decide) (by decide) (by decide)]
      exact image.fields (table+0#64,key) (by simp [New.scalarWrites])
    · rw [oldHeader 8 (by decide) (by decide) (by decide)]
      exact image.fields (table+8#64,New.strideWord key) (by simp [New.scalarWrites])
    · rw [oldHeader 16 (by decide) (by decide) (by decide)]
      exact image.fields (table+16#64,cap) (by simp [New.scalarWrites])
    · rw [scalar_stored_header copied table key cap value image.geometry capSmall image.capLower 24 (by decide)]
      simp [New.putField,StoreWord.put]
    · rw [oldHeader 32 (by decide) (by decide) (by decide)]
      exact image.fields (table+32#64,New.keysPointer table) (by simp [New.scalarWrites])
    · rw [oldHeader 40 (by decide) (by decide) (by decide)]
      exact image.fields (table+40#64,New.scalarNodesPointer table key cap) (by simp [New.scalarWrites])
    · rw [oldHeader 48 (by decide) (by decide) (by decide)]
      exact image.fields (table+48#64,New.scalarOrderPointer table key cap) (by simp [New.scalarWrites])
    · rw [oldHeader 56 (by decide) (by decide) (by decide)]
      exact image.fields (table+56#64,0#64) (by simp [New.scalarWrites])
    · rw [scalar_stored_header copied table key cap value image.geometry capSmall image.capLower 64 (by decide),
        header_other copied table 1#64 24 64 image.geometry.table (by decide) (by decide) (by decide),copiedHeader 64 (by decide)]
      simp [New.putField,StoreWord.put]
    · rw [oldHeader 72 (by decide) (by decide) (by decide)]
      exact image.fields (table+72#64,0#64) (by simp [New.scalarWrites])
    · rw [oldHeader 80 (by decide) (by decide) (by decide)]
      exact image.fields (table+80#64,cap) (by simp [New.scalarWrites])
  · rw [memory]; exact nodes.1
  · rw [memory]; exact nodes.2.1
  · rw [memory]; exact nodes.2.2.1
  · rw [memory]; exact nodes.2.2.2
  · rw [memory]; exact order

end InitECandidate.Solver.Input.CurrentTable.NewLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.NewNode.from_scalar_empty
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.ScalarFields.of_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_tail_quiet
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
    returned=.val (.word 0#64) ∧ New.ScalarFrame source post table key cap ∧ New.ScalarSingle post table key cap 1#64 value := by
  obtain ⟨callee,called,tCell,kCell,vCell⟩:=word_triple_environment source.code.lookup (ofString "htab_new_leaf")
    (ofString "t") (ofString "key") (ofString "value") NewLeaf.body .one table pointer value
    (by decide) (by decide) (by decide) (NewLeaf.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) leafArguments=
      some [.val (.word table),.val (.word pointer),.val (.word value)]:=by
    simp [leafArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,tableCell,keyCell,valueCell]
  rw [guard_shapes.2.1] at normal
  obtain ⟨funded,target,node,inner,leafRun,checked,continued,endpoint⟩:=CallNormal.scoped_normal source post "nl" .one (ofString "htab_new_leaf")
    leafArguments _ NewLeaf.body emptyFinish callee .one args called returned normal
  obtain ⟨nodeEq,leafFrame,single⟩:=NewLeaf.scalar_empty_single (source:=callEntryStateHOLFinite source callee) (post:=target) (image.of_erase rfl) installed tCell kCell vCell keySmall capSmall node leafRun
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
  have currentSingle : New.ScalarSingle current table key cap 0#64 value:=single.of_erase rfl
  exact ⟨answer,storedFrame.of_erase rfl scope,(currentSingle.with_root 1#64).of_erase scope⟩

theorem scalar_after_leaf_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer value : BitVec 64}
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word 0#64)))
    (keySmall : key.toNat≤60) (capSmall : cap.toNat≤2^32) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterLeaf=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ New.ScalarFrame source post table key cap ∧ New.ScalarSingle post table key cap 1#64 value := by
  have keysRead:=NewNode.field_read source table (New.keysPointer table) 32 image.domain image.geometry.table image.aligned (by decide) (by decide) tableCell
    (image.fields (table+32#64,New.keysPointer table) (by simp [New.scalarWrites]))
  rw [entry_shapes.2.2.2.1] at normal
  obtain ⟨inner,continued,endpoint⟩:=ScalarScope.declare_trace source post "keys" _ (New.keysPointer table) afterKeys (some (.returned returned)) keysRead normal
  let current:=bind source "keys" (New.keysPointer table)
  have kept (name : String) (different : ofString "keys"≠ofString name) : current.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    bind_lookup_other source "keys" name (New.keysPointer table) different
  rw [after_keys_empty current ((kept "leaf" (by decide)).trans leafCell)] at continued
  obtain ⟨answer,frame,single⟩:=scalar_empty_leaf_frame (source:=current) (post:=inner) (image.of_erase rfl) installed
    ((kept "t" (by decide)).trans tableCell) ((kept "key" (by decide)).trans keyCell) ((kept "value" (by decide)).trans valueCell)
    keySmall capSmall returned continued
  exact ⟨answer,frame.of_erase rfl (by rw [endpoint] <;> rfl),single.of_erase (by rw [endpoint] <;> rfl)⟩

theorem scalar_after_stride_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer value : BitVec 64}
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (keySmall : key.toNat≤60) (capSmall : cap.toNat≤2^32) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterStride=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ New.ScalarFrame source post table key cap ∧ New.ScalarSingle post table key cap 1#64 value := by
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
    obtain ⟨answer,physical,single⟩:=scalar_after_leaf_frame currentImage (by rw [code]; exact installed)
      ((kept "t" (by decide)).trans tableCell) ((kept "key" (by decide)).trans keyCell) ((kept "value" (by decide)).trans valueCell)
      (CallNormal.continuation_lookup_same source target "leaf" (.val (.word 0#64))) keySmall capSmall returned continued
    exact ⟨answer,physical.of_erase frame.symm (by rw [endpoint] <;> rfl),single.of_erase (by rw [endpoint] <;> rfl)⟩

/-- Whole original first setter normal return, retaining the same full
scalar-table footprint through both declarations and all lexical scopes. -/
theorem scalar_empty_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer value : BitVec 64}
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (keySmall : key.toNat≤60) (capSmall : cap.toNat≤2^32) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ New.ScalarFrame source post table key cap ∧ New.ScalarSingle post table key cap 1#64 value := by
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
  obtain ⟨answer,frame,single⟩:=scalar_after_stride_frame (source:=current) (post:=inner) (image.of_erase rfl) installed
    ((kept "t" (by decide) (by decide)).trans tableCell) ((kept "key" (by decide) (by decide)).trans keyCell)
    ((kept "value" (by decide) (by decide)).trans valueCell) keySmall capSmall returned remaining
  exact ⟨answer,frame.of_erase rfl (by rw [endpoint,innerEq] <;> rfl),single.of_erase (by rw [endpoint,innerEq] <;> rfl)⟩

/-- Actual ordinary first-set caller; its callee return, saved locals and
complete write footprint are derived from the same normally continuing call. -/
theorem scalar_empty_call_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer value : BitVec 64}
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word table),.val (.word pointer),.val (.word value)])
    (keySmall : key.toNat≤60) (capSmall : cap.toNat≤2^32)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htab_set") arguments)=(none,post)) :
    New.ScalarFrame source post table key cap ∧ post.locals=source.locals ∧ New.ScalarSingle post table key cap 1#64 value := by
  obtain ⟨callee,called,tCell,kCell,vCell⟩:=word_triple_environment source.code.lookup (ofString "htab_set")
    (ofString "t") (ofString "key") (ofString "value") body .one table pointer value
    (by decide) (by decide) (by decide) (original_code source.code installed)
  obtain ⟨funded,values,actual,actualCallee,shape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩:=CallNormal.ignored_data source post (ofString "htab_set") arguments normal
  have valuesEq : values=[.val (.word table),.val (.word pointer),.val (.word value)]:=Option.some.inj (actualArgs.symm.trans args)
  subst values
  have entryEq : (actual,actualCallee,shape)=(body,callee,.one):=Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  obtain ⟨answer,frame,single⟩:=scalar_empty_frame (source:=callEntryStateHOLFinite source callee) (post:=target) (image.of_erase rfl) installed tCell kCell vCell keySmall capSmall returned bodyRun
  exact ⟨frame.of_erase rfl (by rw [endpoint] <;> rfl),(by rw [endpoint]),single.of_erase (by rw [endpoint] <;> rfl)⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_empty_finish_quiet
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_after_leaf_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_after_stride_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_empty_cost

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_empty_call_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.account_first_call_cost

#print axioms InitECandidate.Solver.Input.CurrentTable.New.scalar_stride_numbers
#print axioms InitECandidate.Solver.Input.CurrentTable.New.scalar_array_numbers



#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarGeometry.scalar_header_away
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_tail_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_stores_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_stores_returned_frame

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

#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarSingle.of_erase
#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarSingle.with_root
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_stored_nodes
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_stored_order
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_stored_header
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_empty_single

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- The real scalar leaf marker immediately breaks the real traversal,
without evaluating its key-bit branch or reading the query. -/
theorem scalar_leaf_step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base marker : BitVec 64)
    (baseCell : source.locals.lookup (ofString "nodes")=some (.val (.word base)))
    (nodeCell : source.locals.lookup (ofString "n")=some (.val (.word 1#64)))
    (bitsCell : source.locals.lookup (ofString "keybits")=some (.val (.word marker)))
    (mapped : source.memaddrs (cell base 1#64 24))
    (leafCell : source.memory (cell base 1#64 24)=.word marker) :
    evaluateHOLFiniteState source step=(some .break,source) := by
  have read:=Witness.load_word_read source (address 24) (cell base 1#64 24) marker
    (address_read source base 1#64 24 baseCell nodeCell) mapped leafCell
  let entered:=bind source "b" marker
  have bCell : entered.locals.lookup (ofString "b")=some (.val (.word marker)):=bind_lookup_same _ _ _
  have kCell : entered.locals.lookup (ofString "keybits")=some (.val (.word marker)):=
    (bind_lookup_other source "b" "keybits" marker (by decide)).trans bitsCell
  have stopped : evaluateHOLFiniteState entered afterBit=(some .break,entered):=by
    simp [shapes.2.2.1,leafGuard,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_break,
      evalHOLExact,localVar,bCell,kCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [shapes.2.1,ScalarScope.declare_execute source entered "b" (.load .one (address 24)) marker afterBit (some .break) read stopped]
  rw [restore_bound]

/-- Exactly one funded loop tick reaches this actual leaf. Clock-zero
execution follows the original timeout rule. -/
theorem scalar_leaf_loop (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base marker : BitVec 64)
    (baseCell : source.locals.lookup (ofString "nodes")=some (.val (.word base)))
    (nodeCell : source.locals.lookup (ofString "n")=some (.val (.word 1#64)))
    (bitsCell : source.locals.lookup (ofString "keybits")=some (.val (.word marker)))
    (mapped : source.memaddrs (cell base 1#64 24))
    (leafCell : source.memory (cell base 1#64 24)=.word marker) :
    evaluateHOLFiniteState source loop=
      if source.clock=0 then (some .timeOut,emptyLocalsHOLFinite source) else (none,decClockHOLFinite source) := by
  have read:=test_read source 1#64 nodeCell
  simp only [show (1#64 : BitVec 64)≠0#64 from by decide,if_neg] at read
  have stopped:=scalar_leaf_step (decClockHOLFinite source) base marker baseCell nodeCell bitsCell mapped leafCell
  rw [shapes.1,evaluateHOLFiniteState_while_total,read]
  simp only [show (1#64 : BitVec 64)≠0#64 from by decide,if_pos]
  by_cases zero : source.clock=0
  · simp [zero]
  · rw [if_neg zero,stopped]
    simp [fixClockHOLFinite,decClockHOLFinite,zero]

/-- Whole actual singleton traversal: at most one source tick on every
outcome, actual leaf1 on return, and unchanged nonlocal state. -/
theorem body_scalar_single (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap value : BitVec 64)
    (single : New.ScalarSingle source table key cap 1#64 value)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤1 ∧
      LocalEffects.erase (evaluateHOLFiniteState source body).2=LocalEffects.erase source ∧
      ∀ returned,(evaluateHOLFiniteState source body).1=some (.returned returned) →
        returned=.val (.word 1#64) ∧ (evaluateHOLFiniteState source body).2.clock=source.clock-1 := by
  let base:=New.scalarNodesPointer table key cap
  let ready:=scalarRootEntry source key base 1#64
  have inside : (1#64 : BitVec 64).toNat≤cap.toNat:=by have lower:=single.capLower; change 1≤cap.toNat; omega
  have array : AllocatedBytes.Arena base (32*(cap.toNat+1)):=by
    simpa only [base,(New.size_numbers cap single.capSmall).1] using single.geometry.nodes
  have nodeArena:=slot_arena base 1#64 cap 32 array inside
  have aligned:=slot_aligned base 1#64 cap 32 array inside single.geometry.nodesAligned (by decide)
  have mapped : ready.memaddrs (cell base 1#64 24):=
    AllocatedBytes.word_mapped ready (slot base 1#64 32) 32 24 single.domain nodeArena (by decide) aligned (by decide)
  have nodeCell : ready.locals.lookup (ofString "n")=some (.val (.word 1#64)):=bind_lookup_same _ _ _
  have baseCell : ready.locals.lookup (ofString "nodes")=some (.val (.word base)):=
    (bind_lookup_other (scalarNodesEntry source key base) "n" "nodes" 1#64 (by decide)).trans (bind_lookup_same _ _ _)
  have bitsCell : ready.locals.lookup (ofString "keybits")=some (.val (.word (key*8#64))):=
    (bind_lookup_other (scalarNodesEntry source key base) "n" "keybits" 1#64 (by decide)).trans
      ((bind_lookup_other (scalarBitsEntry source key) "nodes" "keybits" base (by decide)).trans (bind_lookup_same _ _ _))
  have loopRun:=scalar_leaf_loop ready base (key*8#64) baseCell nodeCell bitsCell mapped single.leafMarker
  have keyCell : source.memory table=.word key:=by
    simpa only [BitVec.add_zero] using single.fields (table+0#64,key) (by simp [New.singleHeaderWrites])
  have nodesCell:=single.fields (table+40#64,base) (by simp [base,New.singleHeaderWrites])
  have rootCell:=single.fields (table+56#64,1#64) (by simp [New.singleHeaderWrites])
  rw [scalar_setup_execute source table key base 1#64 single.domain single.geometry.table single.aligned tableCell keyCell nodesCell rootCell]
  change source.clock-(scalarRestoreEntry source key base (evaluateHOLFiniteState ready afterRoot).2).clock≤1 ∧
    LocalEffects.erase (scalarRestoreEntry source key base (evaluateHOLFiniteState ready afterRoot).2)=LocalEffects.erase source ∧ _
  rw [body_shapes.2.2.2,evaluateHOLFiniteState_seq_line780,loopRun]
  by_cases zero : source.clock=0
  · have readyZero : ready.clock=0:=zero
    simp only [readyZero,if_pos]
    exact ⟨by change source.clock-source.clock≤1; omega,rfl,by intro returned impossible; cases impossible⟩
  · have readyNonzero : ready.clock≠0:=zero
    simp only [if_neg readyNonzero]
    have tickNode : (decClockHOLFinite ready).locals.lookup (ofString "n")=some (.val (.word 1#64)):=nodeCell
    have returnedRun : evaluateHOLFiniteState (decClockHOLFinite ready) (.return (localVar "n"))=
        (some (.returned (.val (.word 1#64))),emptyLocalsHOLFinite (decClockHOLFinite ready)):=by
      simp [evaluateHOLFiniteState_return,evalHOLExact,localVar,tickNode,shapeOfHOLExact]
    rw [returnedRun]
    refine ⟨?_,rfl,?_⟩
    · change source.clock-(source.clock-1)≤1
      omega
    · intro returned result
      exact ⟨by simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using result.symm,rfl⟩

/-- The original singleton find-leaf caller either stops within two ticks
or enters its actual continuation with leaf1 and all memory retained. -/
theorem scoped_scalar_single_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table key cap value pointer : BitVec 64) (single : New.ScalarSingle source table key cap 1#64 value)
    (installed : OriginalCode.Installed source.code) (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word table),.val (.word pointer)])
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_find_leaf") arguments continuation)=(outcome,post)) :
    (source.clock-post.clock≤2 ∧ ∀ returned,outcome≠some (.returned returned)) ∨ ∃ target inner,
      LocalEffects.erase target=LocalEffects.erase source ∧ target.clock≤source.clock ∧
      source.clock-target.clock≤2 ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name (.val (.word 1#64))) continuation=(outcome,inner) ∧
      post=restore source name inner := by
  obtain ⟨callee,called,tableCell,keyCell⟩:=word_pair_environment source.code.lookup (ofString "htab_find_leaf") (ofString "t") (ofString "key")
    body .one table pointer (by decide) (original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have currentSingle : New.ScalarSingle entry table key cap 1#64 value:=single.of_erase rfl
  obtain ⟨price,physical,answer⟩:=body_scalar_single entry table key cap value currentSingle tableCell
  rcases CallNormal.scoped_classified source post name .one (ofString "htab_find_leaf") arguments _ body continuation callee .one 1 args called price outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,returned,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩:=reached
    rw [bodyRun] at physical answer
    obtain ⟨valueEq,clock⟩:=answer returned rfl
    rw [valueEq] at continued
    exact Or.inr ⟨target,inner,physical,forward,cost,continued,endpoint⟩

end InitECandidate.Solver.Input.CurrentTable.FindLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.scalar_leaf_step
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.scalar_leaf_loop
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.body_scalar_single

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.scoped_scalar_single_trace

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.ScalarFields.after_index
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_copy_arguments_at_node
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_after_node_cost_at_node
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_no_grow_cost

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_single_cost

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
open Flapjack.Compiler.Encoders.Asm

/-- The second insertion search immediately stops at its actual scalar
leaf whenever the real first-difference result is within that marker. -/
theorem scalar_seek_step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base marker difference : BitVec 64)
    (bounded : difference.toNat≤marker.toNat)
    (baseCell : source.locals.lookup (ofString "nodes")=some (.val (.word base)))
    (nodeCell : source.locals.lookup (ofString "n")=some (.val (.word 1#64)))
    (differenceCell : source.locals.lookup (ofString "d")=some (.val (.word difference)))
    (mapped : source.memaddrs (FindLeaf.cell base 1#64 24))
    (leafCell : source.memory (FindLeaf.cell base 1#64 24)=.word marker) :
    evaluateHOLFiniteState source seekStep=(some .break,source) := by
  have read:=Witness.load_word_read source (FindLeaf.address 24) (FindLeaf.cell base 1#64 24) marker
    (FindLeaf.address_read source base 1#64 24 baseCell nodeCell) mapped leafCell
  let entered:=bind source "b" marker
  have bCell : entered.locals.lookup (ofString "b")=some (.val (.word marker)):=bind_lookup_same _ _ _
  have dCell : entered.locals.lookup (ofString "d")=some (.val (.word difference)):=
    (bind_lookup_other source "b" "d" marker (by decide)).trans differenceCell
  have guardRead : eval entered (.cmp .notLower (localVar "b") (localVar "d"))=some (.val (.word 1#64)):=by
    simp [eval,evalHOLExact,localVar,bCell,dCell,wordCmpHOL,BitVec.lt_def,show ¬marker.toNat<difference.toNat from by omega]
  have stopped : evaluateHOLFiniteState entered afterBit=(some .break,entered):=by
    rw [seek_shapes.2.2.2,stopGuard,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
    simp only [eval] at guardRead
    rw [guardRead]
    simp [evaluateHOLFiniteState_break]
  rw [seek_shapes.2.2.1,ScalarScope.declare_execute source entered "b" (.load .one (FindLeaf.address 24)) marker afterBit (some .break) read stopped]
  rw [restore_bound]

/-- Every outcome of the actual singleton insertion search: timeout at
clock0, otherwise exactly one loop tick and no query-bit read. -/
theorem scalar_seek_loop (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base marker difference : BitVec 64)
    (bounded : difference.toNat≤marker.toNat)
    (baseCell : source.locals.lookup (ofString "nodes")=some (.val (.word base)))
    (nodeCell : source.locals.lookup (ofString "n")=some (.val (.word 1#64)))
    (differenceCell : source.locals.lookup (ofString "d")=some (.val (.word difference)))
    (mapped : source.memaddrs (FindLeaf.cell base 1#64 24))
    (leafCell : source.memory (FindLeaf.cell base 1#64 24)=.word marker) :
    evaluateHOLFiniteState source seek=
      if source.clock=0 then (some .timeOut,emptyLocalsHOLFinite source) else (none,decClockHOLFinite source) := by
  have read:=FindLeaf.test_read source 1#64 nodeCell
  simp only [show (1#64 : BitVec 64)≠0#64 from by decide] at read
  have stopped:=scalar_seek_step (decClockHOLFinite source) base marker difference bounded baseCell nodeCell differenceCell mapped leafCell
  rw [seek_shapes.2.1,evaluateHOLFiniteState_while_total,read]
  simp only [show (1#64 : BitVec 64)≠0#64 from by decide,if_pos]
  by_cases zero : source.clock=0
  · simp [zero]
  · rw [if_neg zero,stopped]
    simp [fixClockHOLFinite,decClockHOLFinite,zero]

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_seek_step
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_seek_loop

#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarGeometry.key_copy
#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarGeometry.key_copy_away
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_prefix_execute_at
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_copy_trace_at
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_copied_returned_at

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_copied_state_at
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.ScalarCopiedAt.after_copy_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_no_grow_returned

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_stored_header_at
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_no_grow_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_single_frame

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Complete unchanged second-leaf/internal-node/splice suffix, including
all allocation, copy, query-read and store failures and short-clock stops. -/
theorem scalar_single_fresh_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer root old value difference : BitVec 64)
    (single : New.ScalarSingle source table key cap root old) (available : 3≤cap.toNat)
    (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (differenceCell : source.locals.lookup (ofString "d")=some (.val (.word difference))) :
    source.clock-(evaluateHOLFiniteState source newLeafCall).2.clock≤CopyAny.price key.toNat+5 := by
  let output:=evaluateHOLFiniteState source newLeafCall
  have actual : evaluateHOLFiniteState source newLeafCall=(output.1,output.2):=rfl
  rw [splice_shapes.1] at actual
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) leafArguments=
      some [.val (.word table),.val (.word pointer),.val (.word value)]:=by
    simp [leafArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,tableCell,keyCell,valueCell]
  rcases NewLeaf.scoped_scalar_single_trace source output.2 table key cap pointer root old value single available installed "nl" leafArguments newInternalCall args output.1 actual with stopped|reached
  · change source.clock-output.2.clock≤CopyAny.price key.toNat+5
    have cost:=stopped.1
    omega
  · obtain ⟨target,inner,frame,ready,nodesCell,forward,price,continued,endpoint⟩:=reached
    let current:=CallNormal.continuationEntry source target "nl" (.val (.word 2#64))
    have currentReady : NewNode.Context current table 3#64 cap:=ready.of_frame rfl
    have currentTable : current.locals.lookup (ofString "t")=some (.val (.word table)):=
      (CallNormal.continuation_lookup_other source target "nl" "t" (.val (.word 2#64)) (by decide)).trans tableCell
    have currentDifference : current.locals.lookup (ofString "d")=some (.val (.word difference)):=
      (CallNormal.continuation_lookup_other source target "nl" "d" (.val (.word 2#64)) (by decide)).trans differenceCell
    have currentCode : current.code=source.code:=MemoryMetadata.code frame.fields
    have currentInstalled : OriginalCode.Installed current.code:=by rw [currentCode]; exact installed
    have array : AllocatedBytes.Arena (New.scalarNodesPointer table key cap) (32*(cap.toNat+1)):=by
      simpa only [(New.size_numbers cap single.capSmall).1] using single.geometry.nodes
    obtain ⟨callee,called,tCell,bCell⟩:=word_pair_environment current.code.lookup (ofString "htab_new_internal")
      (ofString "t") (ofString "bit") NewInternal.body .one table difference (by decide) (NewInternal.original_code current.code currentInstalled)
    have internalArgs : evalListHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) [localVar "t",localVar "d"]=
        some [.val (.word table),.val (.word difference)]:=by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,currentTable,currentDifference]
    have internalPrice:=NewInternal.price (callEntryStateHOLFinite current callee) table cap (New.scalarNodesPointer table key cap) 3#64 difference
      (currentReady.of_frame rfl) currentInstalled array single.geometry.nodesAligned tCell bCell nodesCell
    have cost:=ClockCost.scoped_current current (ofString "ni") .one (ofString "htab_new_internal") [localVar "t",localVar "d"] _
      NewInternal.body splice callee .one 1 0 internalArgs called internalPrice (ClockCost.of_quiet current.code splice (splice_quiet current.code))
    rw [splice_shapes.2.1] at continued
    rw [continued] at cost
    change current.clock-inner.clock≤1+0+1 at cost
    have entryClock : current.clock=target.clock:=rfl
    have exitClock : output.2.clock=inner.clock:=by rw [endpoint] <;> rfl
    change source.clock-output.2.clock≤CopyAny.price key.toNat+5
    omega

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scoped_scalar_single_trace
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_fresh_cost

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

structure ScalarSetLocals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key pointer value : BitVec 64) : Prop where
  tableCell : source.locals.lookup (ofString "t")=some (.val (.word table))
  keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer))
  valueCell : source.locals.lookup (ofString "value")=some (.val (.word value))
  lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word key))
  strideCell : source.locals.lookup (ofString "stride")=some (.val (.word (New.strideWord key)))

theorem ScalarSetLocals.with_local {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table key pointer value : BitVec 64}
    (data : ScalarSetLocals source table key pointer value) (name : String) (word : BitVec 64)
    (notTable : ofString name≠ofString "t") (notKey : ofString name≠ofString "key") (notValue : ofString name≠ofString "value")
    (notLength : ofString name≠ofString "klen") (notStride : ofString name≠ofString "stride") :
    ScalarSetLocals (bind source name word) table key pointer value :=
  ⟨(bind_lookup_other source name "t" word notTable).trans data.tableCell,
    (bind_lookup_other source name "key" word notKey).trans data.keyCell,
    (bind_lookup_other source name "value" word notValue).trans data.valueCell,
    (bind_lookup_other source name "klen" word notLength).trans data.lengthCell,
    (bind_lookup_other source name "stride" word notStride).trans data.strideCell⟩

theorem ScalarSetLocals.resume {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table key pointer value : BitVec 64}
    (data : ScalarSetLocals source table key pointer value) (target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (word : ValueHOL 64)
    (notTable : ofString name≠ofString "t") (notKey : ofString name≠ofString "key") (notValue : ofString name≠ofString "value")
    (notLength : ofString name≠ofString "klen") (notStride : ofString name≠ofString "stride") :
    ScalarSetLocals (CallNormal.continuationEntry source target name word) table key pointer value :=
  ⟨(CallNormal.continuation_lookup_other source target name "t" word notTable).trans data.tableCell,
    (CallNormal.continuation_lookup_other source target name "key" word notKey).trans data.keyCell,
    (CallNormal.continuation_lookup_other source target name "value" word notValue).trans data.valueCell,
    (CallNormal.continuation_lookup_other source target name "klen" word notLength).trans data.lengthCell,
    (CallNormal.continuation_lookup_other source target name "stride" word notStride).trans data.strideCell⟩

set_option maxRecDepth 100000 in
theorem scalar_difference_shapes :
    afterDifference=.dec (ofString "nodes") .one (.load .one (NewNode.address 40)) afterNodes ∧
    afterNodes=.dec (ofString "p") .one (.const 0#64) afterParent ∧
    afterParent=.dec (ofString "n") .one (.load .one (NewNode.address 56)) afterNode := by
  simp only [afterDifference,afterNodes,afterParent,afterNode,differenceCall,afterCompare,compareCall,afterKeys,afterLeaf,afterStride,afterLength,body,
    Guest.Software.guestFn_htab_set,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar,NewNode.address,Scalar.plus]
  trivial

/-- The actual bounded first-difference result feeds the original setup,
one-tick singleton seek and complete second-leaf/internal/splice suffix. -/
theorem scalar_single_after_difference_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer old value : BitVec 64) (difference : Nat)
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (data : ScalarSetLocals source table key pointer value) (installed : OriginalCode.Installed source.code)
    (bounded : difference≤8*key.toNat)
    (differenceCell : source.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 difference)))) :
    source.clock-(evaluateHOLFiniteState source afterDifference).2.clock≤CopyAny.price key.toNat+6 := by
  let base:=New.scalarNodesPointer table key cap
  have nodesRead:=NewNode.field_read source table base 40 single.domain single.geometry.table single.aligned (by decide) (by decide) data.tableCell
    (single.fields (table+40#64,base) (by simp [base,New.singleHeaderWrites]))
  rw [scalar_difference_shapes.1]
  apply ClockCost.declared_current source "nodes" _ base _ (CopyAny.price key.toNat+6) nodesRead
  let first:=bind source "nodes" base
  have firstData : ScalarSetLocals first table key pointer value:=data.with_local "nodes" base (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [scalar_difference_shapes.2.1]
  apply ClockCost.declared_current first "p" (.const 0#64) 0#64 _ (CopyAny.price key.toNat+6) rfl
  let second:=bind first "p" 0#64
  have secondData : ScalarSetLocals second table key pointer value:=firstData.with_local "p" 0#64 (by decide) (by decide) (by decide) (by decide) (by decide)
  have rootRead:=NewNode.field_read second table 1#64 56 single.domain single.geometry.table single.aligned (by decide) (by decide) secondData.tableCell
    (single.fields (table+56#64,1#64) (by simp [New.singleHeaderWrites]))
  rw [scalar_difference_shapes.2.2]
  apply ClockCost.declared_current second "n" _ 1#64 _ (CopyAny.price key.toNat+6) rootRead
  let entry:=bind second "n" 1#64
  have entryData : ScalarSetLocals entry table key pointer value:=secondData.with_local "n" 1#64 (by decide) (by decide) (by decide) (by decide) (by decide)
  have entryDifference : entry.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 difference))):=by
    simpa [entry,second,first,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using differenceCell
  have baseCell : entry.locals.lookup (ofString "nodes")=some (.val (.word base)):=
    (bind_lookup_other second "n" "nodes" 1#64 (by decide)).trans
      ((bind_lookup_other first "p" "nodes" 0#64 (by decide)).trans (bind_lookup_same _ _ _))
  have nodeCell : entry.locals.lookup (ofString "n")=some (.val (.word 1#64)):=bind_lookup_same _ _ _
  have inside : (1#64 : BitVec 64).toNat≤cap.toNat:=by change 1≤cap.toNat; omega
  have array : AllocatedBytes.Arena base (32*(cap.toNat+1)):=by
    simpa only [base,(New.size_numbers cap single.capSmall).1] using single.geometry.nodes
  have mapped : entry.memaddrs (FindLeaf.cell base 1#64 24):=
    AllocatedBytes.word_mapped entry (slot base 1#64 32) 32 24 single.domain (slot_arena base 1#64 cap 32 array inside) (by decide)
      (slot_aligned base 1#64 cap 32 array inside single.geometry.nodesAligned (by decide)) (by decide)
  have markerNumber : (key*8#64).toNat=8*key.toNat:=by
    rw [BitVec.toNat_mul]
    change key.toNat*8%18446744073709551616=8*key.toNat
    rw [Nat.mod_eq_of_lt (by have small:=single.keySmall; omega)]
    omega
  have differenceNumber : (BitVec.ofNat 64 difference).toNat=difference:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have small:=single.keySmall; omega)]
  have loopRun:=scalar_seek_loop entry base (key*8#64) (BitVec.ofNat 64 difference) (by rw [markerNumber,differenceNumber]; exact bounded)
    baseCell nodeCell entryDifference mapped single.leafMarker
  rw [seek_shapes.1,evaluateHOLFiniteState_seq_line780,loopRun]
  by_cases zero : entry.clock=0
  · rw [if_pos zero]
    change entry.clock-entry.clock≤CopyAny.price key.toNat+6
    omega
  · rw [if_neg zero]
    simp only
    have tickDifference : (decClockHOLFinite entry).locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 difference))):=entryDifference
    have cost:=scalar_single_fresh_cost (decClockHOLFinite entry) table key cap pointer 1#64 old value (BitVec.ofNat 64 difference)
      (single.of_erase rfl) available installed entryData.tableCell entryData.keyCell entryData.valueCell tickDifference
    change entry.clock-1-(evaluateHOLFiniteState (decClockHOLFinite entry) newLeafCall).2.clock≤CopyAny.price key.toNat+5 at cost
    have forward:=evaluateHOLFiniteState_clock_le (decClockHOLFinite entry) newLeafCall
    change (evaluateHOLFiniteState (decClockHOLFinite entry) newLeafCall).2.clock≤entry.clock-1 at forward
    change entry.clock-(evaluateHOLFiniteState (decClockHOLFinite entry) newLeafCall).2.clock≤CopyAny.price key.toNat+6
    omega

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.ScalarSetLocals.with_local
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.ScalarSetLocals.resume
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_difference_shapes
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_after_difference_cost

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

/-- The real first-difference caller and its complete continuation. The
returned position and memory frame are from this same actual scan. -/
theorem scalar_single_difference_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer old value : BitVec 64)
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (data : ScalarSetLocals source table key pointer value) (installed : OriginalCode.Installed source.code)
    (keysCell : source.locals.lookup (ofString "keys")=some (.val (.word (New.keysPointer table))))
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word 1#64))) :
    source.clock-(evaluateHOLFiniteState source differenceCall).2.clock≤CopyAny.price key.toNat+9*key.toNat+7 := by
  let output:=evaluateHOLFiniteState source differenceCall
  have actual : evaluateHOLFiniteState source differenceCall=(output.1,output.2):=rfl
  rw [entry_shapes.2.2.2.2.2.2] at actual
  let arguments : List (ExpHOL 64):=[localVar "key",.op .add [localVar "keys",.panop .mul [localVar "leaf",localVar "stride"]],localVar "klen"]
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word pointer),.val (.word (New.keysPointer table+New.strideWord key)),.val (.word (BitVec.ofNat 64 key.toNat))]:=by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.keyCell,data.lengthCell,data.strideCell,keysCell,leafCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  rcases FirstDiff.scoped_scalar_trace source output.2 pointer (New.keysPointer table+New.strideWord key) key.toNat single.keySmall installed
    "d" arguments afterDifference args output.1 actual with stopped|reached
  · change source.clock-output.2.clock≤CopyAny.price key.toNat+9*key.toNat+7
    have cost:=stopped.1
    omega
  · obtain ⟨target,inner,position,bounded,frame,forward,price,continued,endpoint⟩:=reached
    let current:=CallNormal.continuationEntry source target "d" (.val (.word (BitVec.ofNat 64 position)))
    have currentData : ScalarSetLocals current table key pointer value:=data.resume target "d" _ (by decide) (by decide) (by decide) (by decide) (by decide)
    have currentSingle : New.ScalarSingle current table key cap 1#64 old:=single.of_erase frame
    have currentInstalled : OriginalCode.Installed current.code:=by rw [LocalEffects.code_of_erase source current frame]; exact installed
    have cost:=scalar_single_after_difference_cost current table key cap pointer old value position currentSingle available currentData currentInstalled bounded
      (CallNormal.continuation_lookup_same source target "d" _)
    rw [continued] at cost
    change current.clock-inner.clock≤CopyAny.price key.toNat+6 at cost
    have entryClock : current.clock=target.clock:=rfl
    have exitClock : output.2.clock=inner.clock:=by rw [endpoint] <;> rfl
    change source.clock-output.2.clock≤CopyAny.price key.toNat+9*key.toNat+7
    omega

/-- A selected existing-key update cannot enter the later insertion scan.
Any actual guard value or guard failure is covered without guessing equality. -/
theorem scalar_single_after_compare_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer old value : BitVec 64)
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (data : ScalarSetLocals source table key pointer value) (installed : OriginalCode.Installed source.code)
    (keysCell : source.locals.lookup (ofString "keys")=some (.val (.word (New.keysPointer table))))
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word 1#64))) :
    source.clock-(evaluateHOLFiniteState source afterCompare).2.clock≤CopyAny.price key.toNat+9*key.toNat+7 := by
  have back:=scalar_single_difference_cost source table key cap pointer old value single available data installed keysCell leafCell
  have stops : NoFallthrough updateBody:=by
    rw [guard_shapes.2.2.2.2.1]
    exact NoFallthrough.sequence _ _ (NoFallthrough.returned _)
  have quiet : QuietClock.Preserves source.code updateBody:=by
    rw [guard_shapes.2.2.2.2.1]
    exact QuietClock.sequence source.code _ _ (QuietClock.store source.code _ _) (QuietClock.returned source.code _)
  have front:=(ClockCost.of_quiet source.code updateBody quiet) source rfl
  have noNormal:=stops source
  rw [entry_shapes.2.2.2.2.2.1,guard_shapes.2.2.2.1,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact (fun query=>Classical.propDecidable (source.memaddrs query))
    (.cmp .notEqual (localVar "eq") (.const 0#64))=read
  cases read with
  | none=>simp
  | some read=>
    cases read with
    | rStruct fields=>simp
    | nStruct name fields=>simp
    | val payload=>
      cases payload with
      | word word=>
        simp only
        by_cases zero : word=0
        · rw [if_pos zero,evaluateHOLFiniteState_skip]
          exact back
        · rw [if_neg zero]
          generalize computed : evaluateHOLFiniteState source updateBody=output at front noNormal ⊢
          obtain ⟨result,target⟩:=output
          cases result with
          | none=>exact (noNormal rfl).elim
          | some result=>exact front.trans (Nat.zero_le _)

/-- The actual scalar memeq caller preserves the complete physical table;
its observed result selects the real update/difference continuation. -/
theorem scalar_single_compare_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer old value : BitVec 64)
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (data : ScalarSetLocals source table key pointer value) (installed : OriginalCode.Installed source.code)
    (keysCell : source.locals.lookup (ofString "keys")=some (.val (.word (New.keysPointer table))))
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word 1#64))) :
    source.clock-(evaluateHOLFiniteState source compareCall).2.clock≤CopyAny.price key.toNat+13*key.toNat+8 := by
  let output:=evaluateHOLFiniteState source compareCall
  have actual : evaluateHOLFiniteState source compareCall=(output.1,output.2):=rfl
  rw [guard_shapes.2.2.2.2.2] at actual
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) compareArguments=
      some [.val (.word (New.keysPointer table+New.strideWord key)),.val (.word pointer),.val (.word (BitVec.ofNat 64 key.toNat))]:=by
    simp [compareArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.keyCell,data.lengthCell,data.strideCell,keysCell,leafCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  obtain ⟨callee,called,aCell,bCell,nCell⟩:=MutableTable.MemeqByteRuntime.environment source.code.lookup (New.keysPointer table+New.strideWord key) pointer key.toNat
    (MutableTable.MemeqAny.original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have price:=MutableTable.MemeqAny.variable_body_cost entry key.toNat (by have small:=single.keySmall; omega) nCell
  rcases CallNormal.scoped_classified source output.2 "eq" .one (ofString "memeq") compareArguments _ Memeq32.body afterCompare callee .one (4*key.toNat)
    args called price output.1 actual with stopped|reached
  · change source.clock-output.2.clock≤CopyAny.price key.toNat+13*key.toNat+8
    have cost:=stopped.1
    omega
  · obtain ⟨target,returned,inner,funded,bodyRun,checked,forward,price,continued,endpoint⟩:=reached
    let current:=CallNormal.continuationEntry source target "eq" returned
    have frame:=MutableTable.MemeqAny.readonly source.code entry rfl
    rw [bodyRun] at frame
    have currentData : ScalarSetLocals current table key pointer value:=data.resume target "eq" returned (by decide) (by decide) (by decide) (by decide) (by decide)
    have currentKeys : current.locals.lookup (ofString "keys")=some (.val (.word (New.keysPointer table))):=
      (CallNormal.continuation_lookup_other source target "eq" "keys" returned (by decide)).trans keysCell
    have currentLeaf : current.locals.lookup (ofString "leaf")=some (.val (.word 1#64)):=
      (CallNormal.continuation_lookup_other source target "eq" "leaf" returned (by decide)).trans leafCell
    have currentInstalled : OriginalCode.Installed current.code:=by rw [LocalEffects.code_of_erase source current frame]; exact installed
    have cost:=scalar_single_after_compare_cost current table key cap pointer old value (single.of_erase frame) available currentData currentInstalled currentKeys currentLeaf
    rw [continued] at cost
    change current.clock-inner.clock≤CopyAny.price key.toNat+9*key.toNat+7 at cost
    have entryClock : current.clock=target.clock:=rfl
    have exitClock : output.2.clock=inner.clock:=by rw [endpoint] <;> rfl
    change source.clock-output.2.clock≤CopyAny.price key.toNat+13*key.toNat+8
    omega

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_difference_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_after_compare_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_compare_cost

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

/-- The real nonzero singleton leaf skips the first-insertion guard. -/
theorem scalar_single_after_keys (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word 1#64))) :
    evaluateHOLFiniteState source afterKeys=evaluateHOLFiniteState source compareCall := by
  rw [entry_shapes.2.2.2.2.1,guard_shapes.1,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
  simp [evalHOLExact,localVar,leafCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]

/-- Actual key-base setup, comparison and both complete current branches. -/
theorem scalar_single_after_leaf_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer old value : BitVec 64)
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (data : ScalarSetLocals source table key pointer value) (installed : OriginalCode.Installed source.code)
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word 1#64))) :
    source.clock-(evaluateHOLFiniteState source afterLeaf).2.clock≤CopyAny.price key.toNat+13*key.toNat+8 := by
  have keysRead:=NewNode.field_read source table (New.keysPointer table) 32 single.domain single.geometry.table single.aligned (by decide) (by decide) data.tableCell
    (single.fields (table+32#64,New.keysPointer table) (by simp [New.singleHeaderWrites]))
  rw [entry_shapes.2.2.2.1]
  apply ClockCost.declared_current source "keys" _ (New.keysPointer table) _ (CopyAny.price key.toNat+13*key.toNat+8) keysRead
  let current:=bind source "keys" (New.keysPointer table)
  have currentData : ScalarSetLocals current table key pointer value:=data.with_local "keys" (New.keysPointer table) (by decide) (by decide) (by decide) (by decide) (by decide)
  have currentLeaf : current.locals.lookup (ofString "leaf")=some (.val (.word 1#64)):=
    (bind_lookup_other source "keys" "leaf" (New.keysPointer table) (by decide)).trans leafCell
  rw [scalar_single_after_keys current currentLeaf]
  exact scalar_single_compare_cost current table key cap pointer old value (single.of_erase rfl) available currentData installed
    (bind_lookup_same _ _ _) currentLeaf

/-- The actual singleton lookup supplies leaf1 and its own read-only
frame before the original setter comparison. No returned leaf is assumed. -/
theorem scalar_single_after_stride_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer old value : BitVec 64)
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (data : ScalarSetLocals source table key pointer value) (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterStride).2.clock≤CopyAny.price key.toNat+13*key.toNat+10 := by
  let output:=evaluateHOLFiniteState source afterStride
  have actual : evaluateHOLFiniteState source afterStride=(output.1,output.2):=rfl
  rw [entry_shapes.2.2.1] at actual
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "t",localVar "key"]=
      some [.val (.word table),.val (.word pointer)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.tableCell,data.keyCell]
  rcases FindLeaf.scoped_scalar_single_trace source output.2 table key cap old pointer single installed "leaf" [localVar "t",localVar "key"] afterLeaf args output.1 actual with stopped|reached
  · change source.clock-output.2.clock≤CopyAny.price key.toNat+13*key.toNat+10
    have cost:=stopped.1
    omega
  · obtain ⟨target,inner,frame,forward,price,continued,endpoint⟩:=reached
    let current:=CallNormal.continuationEntry source target "leaf" (.val (.word 1#64))
    have currentData : ScalarSetLocals current table key pointer value:=data.resume target "leaf" _ (by decide) (by decide) (by decide) (by decide) (by decide)
    have currentInstalled : OriginalCode.Installed current.code:=by rw [LocalEffects.code_of_erase source current frame]; exact installed
    have cost:=scalar_single_after_leaf_cost current table key cap pointer old value (single.of_erase frame) available currentData currentInstalled
      (CallNormal.continuation_lookup_same source target "leaf" _)
    rw [continued] at cost
    change current.clock-inner.clock≤CopyAny.price key.toNat+13*key.toNat+8 at cost
    have entryClock : current.clock=target.clock:=rfl
    have exitClock : output.2.clock=inner.clock:=by rw [endpoint] <;> rfl
    change source.clock-output.2.clock≤CopyAny.price key.toNat+13*key.toNat+10
    omega

/-- Complete unchanged scalar singleton setter, including the actual
lookup/comparison/difference/seek/constructors/splice and every stopped path. -/
theorem scalar_single_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer old value : BitVec 64)
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤CopyAny.price key.toNat+13*key.toNat+10 := by
  have lengthRead:=NewNode.field_read source table key 0 single.domain single.geometry.table single.aligned (by decide) (by decide) tableCell
    (single.fields (table+0#64,key) (by simp [New.singleHeaderWrites]))
  rw [entry_shapes.1]
  apply ClockCost.declared_current source "klen" _ key _ (CopyAny.price key.toNat+13*key.toNat+10) lengthRead
  let first:=bind source "klen" key
  have firstTable : first.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other source "klen" "t" key (by decide)).trans tableCell
  have strideRead:=NewNode.field_read first table (New.strideWord key) 8 single.domain single.geometry.table single.aligned (by decide) (by decide) firstTable
    (single.fields (table+8#64,New.strideWord key) (by simp [New.singleHeaderWrites]))
  rw [entry_shapes.2.1]
  apply ClockCost.declared_current first "stride" _ (New.strideWord key) _ (CopyAny.price key.toNat+13*key.toNat+10) strideRead
  let current:=bind first "stride" (New.strideWord key)
  have kept (name : String) (notStride : ofString "stride"≠ofString name) (notLength : ofString "klen"≠ofString name) :
      current.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    (bind_lookup_other first "stride" name (New.strideWord key) notStride).trans (bind_lookup_other source "klen" name key notLength)
  have data : ScalarSetLocals current table key pointer value:=
    ⟨(kept "t" (by decide) (by decide)).trans tableCell,(kept "key" (by decide) (by decide)).trans keyCell,
      (kept "value" (by decide) (by decide)).trans valueCell,
      (bind_lookup_other first "stride" "klen" (New.strideWord key) (by decide)).trans (bind_lookup_same _ _ _),bind_lookup_same _ _ _⟩
  exact scalar_single_after_stride_cost current table key cap pointer old value (single.of_erase rfl) available data installed

/-- Actual ignored singleton setter caller at its scalar key width. -/
theorem scalar_single_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer old value : BitVec 64)
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (installed : OriginalCode.Installed source.code) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word table),.val (.word pointer),.val (.word value)]) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htab_set") arguments)).2.clock≤CopyAny.price key.toNat+13*key.toNat+11 := by
  obtain ⟨callee,called,tCell,kCell,vCell⟩:=word_triple_environment source.code.lookup (ofString "htab_set")
    (ofString "t") (ofString "key") (ofString "value") body .one table pointer value
    (by decide) (by decide) (by decide) (original_code source.code installed)
  have cost:=ClockCost.call_current source (some none) (ofString "htab_set") arguments _ body callee .one
    (CopyAny.price key.toNat+13*key.toNat+10) args called
    (scalar_single_cost (callEntryStateHOLFinite source callee) table key cap pointer old value (single.of_erase rfl) available installed tCell kCell vCell)
  change source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htab_set") arguments)).2.clock≤
    (CopyAny.price key.toNat+13*key.toNat+10)+1 at cost
  omega

/-- The real repeated20-byte account-access insertion costs at most295
caller ticks, without assuming the key comparison succeeds or is equal. -/
theorem account_second_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap pointer old value : BitVec 64)
    (single : New.ScalarSingle source table 20#64 cap 1#64 old) (available : 3≤cap.toNat)
    (installed : OriginalCode.Installed source.code) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word table),.val (.word pointer),.val (.word value)]) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htab_set") arguments)).2.clock≤295 := by
  simpa [CopyAny.price] using scalar_single_call_cost source table 20#64 cap pointer old value single available installed arguments args

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_after_keys
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_after_leaf_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_after_stride_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_call_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.account_second_call_cost

namespace InitECandidate.Solver.Input.CurrentTable.NewInternal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The same actual no-grow internal-node return writes only its available
slot and the real next-index field, retaining the actual node-array header. -/
theorem scalar_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap node bit : BitVec 64)
    (ready : NewNode.Context source table node cap) (geometry : New.ScalarGeometry table key cap) (capSmall : cap.toNat≤2^32)
    (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (bitCell : source.locals.lookup (ofString "bit")=some (.val (.word bit)))
    (nodesCell : source.memory (table+40#64)=.word (New.scalarNodesPointer table key cap))
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    returned=.val (.word node) ∧ New.ScalarFrame source post table key cap ∧ post.memory (table+40#64)=.word (New.scalarNodesPointer table key cap) := by
  have array : AllocatedBytes.Arena (New.scalarNodesPointer table key cap) (32*(cap.toNat+1)):=by
    simpa only [(New.size_numbers cap capSmall).1] using geometry.nodes
  obtain ⟨answer,funded,clock,scope⟩:=normal source post table cap (New.scalarNodesPointer table key cap) node bit ready installed array geometry.nodesAligned tableCell bitCell nodesCell returned run
  have header:=(New.ScalarFrame.refl source table key cap).put_field geometry 64 (by decide) (node+1#64)
  have zero:=header.put_node geometry capSmall node 0#64 0 ready.room (by decide)
  have one:=zero.put_node geometry capSmall node 0#64 8 ready.room (by decide)
  have two:=one.put_node geometry capSmall node 0#64 16 ready.room (by decide)
  have three:=two.put_node geometry capSmall node bit 24 ready.room (by decide)
  have frame : New.ScalarFrame source post table key cap:=three.of_erase rfl scope
  have memory:=LocalEffects.memory_of_erase (stored (New.putField source table 64 (node+1#64)) (New.scalarNodesPointer table key cap) node bit) post scope
  have away (offset : Nat) (small : offset<32) : table+40#64≠FindLeaf.cell (New.scalarNodesPointer table key cap) node offset:=
    geometry.scalar_header_away capSmall node ready.room offset 40 small (by decide)
  refine ⟨answer,frame,?_⟩
  rw [memory]
  simp only [stored,putNode,StoreWord.put,if_neg (away 0 (by decide)),if_neg (away 8 (by decide)),if_neg (away 16 (by decide)),if_neg (away 24 (by decide))]
  exact (header_other source table (node+1#64) 64 40 geometry.table (by decide) (by decide) (by decide)).trans nodesCell

end InitECandidate.Solver.Input.CurrentTable.NewInternal

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The scalar splice's caller bindings survive every actual word store. -/
theorem SpliceLocals.scalar_keep {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table base node parent leaf internal pointer : BitVec 64} {difference : Nat}
    (data : SpliceLocals source table base node parent leaf internal pointer difference) (same : target.locals=source.locals) :
    SpliceLocals target table base node parent leaf internal pointer difference := by
  rcases data with ⟨t,b,n,p,l,i,k,d⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> rw [same] <;> assumption

/-- Actual normal stores through a known scalar node address protect all
external memory and preserve the same caller locals. -/
theorem scalar_node_store_frame {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap : BitVec 64}
    (frame : New.ScalarFrame origin source table key cap) (geometry : New.ScalarGeometry table key cap) (capSmall : cap.toNat≤2^32)
    (name : String) (node value : BitVec 64) (offset : Nat) (expression : ExpHOL 64)
    (inside : node.toNat≤cap.toNat) (small : offset<32)
    (baseCell : source.locals.lookup (ofString "nodes")=some (.val (.word (New.scalarNodesPointer table key cap))))
    (nodeCell : source.locals.lookup (ofString name)=some (.val (.word node)))
    (valueRead : eval source expression=some (.val (.word value)))
    (normal : evaluateHOLFiniteState source (.store (nodeFor name offset) expression)=(none,post)) :
    New.ScalarFrame origin post table key cap ∧ post.locals=source.locals := by
  have read:=named_node_read source (New.scalarNodesPointer table key cap) node name offset baseCell nodeCell
  obtain ⟨mapped,endpoint⟩:=word_store_normal source post _ _ _ _ read valueRead normal
  have bounds:=geometry.node_in_scalar capSmall node inside offset small
  exact ⟨frame.store_inside _ _ _ _ read valueRead bounds.1 bounds.2 normal,by rw [endpoint]⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarFrame.refl
#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarFrame.trans
#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarFrame.put_word
#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarFrame.put_field
#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarFrame.put_node
#print axioms InitECandidate.Solver.Input.CurrentTable.NewInternal.scalar_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.SpliceLocals.scalar_keep
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_node_store_frame

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

/-- Both real child-link stores use the same available internal node,
regardless of the actual key-bit branch. -/
theorem scalar_child_stores_frame {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap internal left right : BitVec 64}
    (frame : New.ScalarFrame origin source table key cap) (geometry : New.ScalarGeometry table key cap) (capSmall : cap.toNat≤2^32)
    (inside : internal.toNat≤cap.toNat) (leftName rightName : String)
    (baseCell : source.locals.lookup (ofString "nodes")=some (.val (.word (New.scalarNodesPointer table key cap))))
    (internalCell : source.locals.lookup (ofString "ni")=some (.val (.word internal)))
    (leftCell : source.locals.lookup (ofString leftName)=some (.val (.word left)))
    (rightCell : source.locals.lookup (ofString rightName)=some (.val (.word right)))
    (normal : evaluateHOLFiniteState source (.seq (.store (nodeFor "ni" 8) (localVar leftName)) (.store (nodeFor "ni" 16) (localVar rightName)))=(none,post)) :
    New.ScalarFrame origin post table key cap ∧ post.locals=source.locals := by
  obtain ⟨middle,front,back⟩:=sequence_none source post _ _ normal
  obtain ⟨first,locals⟩:=scalar_node_store_frame frame geometry capSmall "ni" internal left 8 (localVar leftName) inside (by decide)
    baseCell internalCell (Request.local_word source leftName left leftCell) front
  obtain ⟨last,lastLocals⟩:=scalar_node_store_frame first geometry capSmall "ni" internal right 16 (localVar rightName) inside (by decide)
    (by rw [locals]; exact baseCell) (by rw [locals]; exact internalCell)
    (Request.local_word middle rightName right (by rw [locals]; exact rightCell)) back
  exact ⟨last,lastLocals.trans locals⟩

end InitECandidate.Solver.Input.CurrentTable.Set

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Variable-index scalar child/root/parent rewiring. Bounds come from the
actual search and node constructors; no fixed second-insertion indices are
assumed. These frames apply before growth changes the array pointers. -/
theorem scalar_split_frame_at {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer node parent leaf internal : BitVec 64} {difference : Nat}
    (frame : New.ScalarFrame origin source table key cap) (geometry : New.ScalarGeometry table key cap) (capSmall : cap.toNat≤2^32)
    (internalInside : internal.toNat≤cap.toNat)
    (data : SpliceLocals source table (New.scalarNodesPointer table key cap) node parent leaf internal pointer difference)
    (normal : evaluateHOLFiniteState source splitChildren=(none,post)) :
    New.ScalarFrame origin post table key cap ∧ post.locals=source.locals := by
  rw [splice_shapes.2.2.2.2.2.2.2.1] at normal
  rcases conditional_none source post _ leftFresh rightFresh normal with chosen|chosen
  · rw [leftFresh] at chosen
    exact scalar_child_stores_frame (internal:=internal) frame geometry capSmall internalInside "nl" "n" data.nodesCell data.internalCell data.leafCell data.nodeCell chosen
  · rw [rightFresh] at chosen
    exact scalar_child_stores_frame (internal:=internal) frame geometry capSmall internalInside "n" "nl" data.nodesCell data.internalCell data.nodeCell data.leafCell chosen

theorem scalar_after_split_frame_at {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table key cap pointer node parent leaf internal : BitVec 64} {difference : Nat}
    (frame : New.ScalarFrame origin source table key cap) (geometry : New.ScalarGeometry table key cap)
    (capSmall : cap.toNat≤2^32) (parentInside : parent.toNat≤cap.toNat)
    (data : SpliceLocals source table (New.scalarNodesPointer table key cap) node parent leaf internal pointer difference)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterSplit=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ New.ScalarFrame origin post table key cap := by
  have safe : LocalPrefix (ofString "nodes") attach:=by
    rw [splice_shapes.2.2.2.2.2.2.2.2.2]
    exact .ite _ (.store _ _) (.ite _ (.store _ _) (.store _ _))
  rw [splice_shapes.2.2.2.2.2.2.2.2.1] at normal
  obtain ⟨middle,attached,returnedRun⟩:=sequence_returned source post attach (.return (.const 0#64)) returned (safe.summary_full source).2.1 normal
  have stored : New.ScalarFrame origin middle table key cap:=by
    rw [splice_shapes.2.2.2.2.2.2.2.2.2] at attached
    rcases conditional_none source middle _ _ _ attached with rootStore|parentStore
    · have addressRead:=Scalar.plus_read source (localVar "t") table 56 (Request.local_word source "t" table data.tableCell)
      have valueRead:=Request.local_word source "ni" internal data.internalCell
      have number:=byteAddress_toNat table 56 (by have upper:=geometry.table.upper; omega)
      change (table+56#64).toNat=table.toNat+56 at number
      exact frame.store_inside _ _ (table+56#64) internal addressRead valueRead (by rw [number]; omega)
        (by rw [number]; have before:=geometry.header_before_end; omega) rootStore
    · rcases conditional_none source middle _ _ _ parentStore with leftStore|rightStore
      · exact (scalar_node_store_frame frame geometry capSmall "p" parent internal 8 (localVar "ni") parentInside (by decide)
          data.nodesCell data.parentCell (Request.local_word source "ni" internal data.internalCell) leftStore).1
      · exact (scalar_node_store_frame frame geometry capSmall "p" parent internal 16 (localVar "ni") parentInside (by decide)
          data.nodesCell data.parentCell (Request.local_word source "ni" internal data.internalCell) rightStore).1
  obtain ⟨value,endpoint⟩:=return_normal middle post (.const 0#64) returned returnedRun
  have answer : returned=.val (.word 0#64):=Option.some.inj value.symm
  exact ⟨answer,stored.of_erase rfl (by rw [endpoint] <;> rfl)⟩

theorem scalar_splice_frame_at {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer node parent leaf internal : BitVec 64} {difference : Nat}
    (frame : New.ScalarFrame origin source table key cap) (geometry : New.ScalarGeometry table key cap) (capSmall : cap.toNat≤2^32)
    (nodeInside : node.toNat≤cap.toNat) (parentInside : parent.toNat≤cap.toNat)
    (leafInside : leaf.toNat≤cap.toNat) (internalInside : internal.toNat≤cap.toNat) (domain : source.memaddrs=InitE.ordinaryDomain) (aligned : table.toNat%8=0)
    (data : SpliceLocals source table (New.scalarNodesPointer table key cap) node parent leaf internal pointer difference)
    (nodesCell : source.memory (table+40#64)=.word (New.scalarNodesPointer table key cap))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source splice=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ New.ScalarFrame origin post table key cap := by
  let base:=New.scalarNodesPointer table key cap
  let start:=bind source "nodes" base
  have nodesRead:=NewNode.field_read source table base 40 domain geometry.table aligned (by decide) (by decide) data.tableCell nodesCell
  have refreshed:=StateSteps.assign_execute source "nodes" _ base base data.nodesCell nodesRead
  change evaluateHOLFiniteState source (.assign .local (ofString "nodes") (.load .one (.op .add [localVar "t",.const 40#64])))=(none,start) at refreshed
  rw [splice_shapes.2.2.1,evaluateHOLFiniteState_seq_line780,refreshed] at normal
  change evaluateHOLFiniteState start afterRefresh=(some (.returned returned),post) at normal
  have startData : SpliceLocals start table base node parent leaf internal pointer difference:=data.with_nodes
  have startFrame : New.ScalarFrame origin start table key cap:=frame.of_erase rfl rfl
  rw [splice_shapes.2.2.2.1] at normal
  obtain ⟨one,firstRun,remaining⟩:=sequence_returned start post (.store (nodeFor "ni" 0) (localVar "p")) afterInternalParent returned
    ((LocalPrefix.store _ _ : LocalPrefix (ofString "nodes") _).summary_full start).2.1 normal
  obtain ⟨first,firstLocals⟩:=scalar_node_store_frame startFrame geometry capSmall "ni" internal parent 0 (localVar "p") internalInside (by decide)
    startData.nodesCell startData.internalCell (Request.local_word start "p" parent startData.parentCell) firstRun
  have firstData:=startData.scalar_keep firstLocals
  rw [splice_shapes.2.2.2.2.1] at remaining
  obtain ⟨two,secondRun,remaining⟩:=sequence_returned one post (.store (nodeFor "nl" 0) (localVar "ni")) afterLeafParent returned
    ((LocalPrefix.store _ _ : LocalPrefix (ofString "nodes") _).summary_full one).2.1 remaining
  obtain ⟨second,secondLocals⟩:=scalar_node_store_frame first geometry capSmall "nl" leaf internal 0 (localVar "ni") leafInside (by decide)
    firstData.nodesCell firstData.leafCell (Request.local_word one "ni" internal firstData.internalCell) secondRun
  have secondData:=firstData.scalar_keep secondLocals
  rw [splice_shapes.2.2.2.2.2.1] at remaining
  obtain ⟨three,thirdRun,remaining⟩:=sequence_returned two post (.store (nodeFor "n" 0) (localVar "ni")) afterOldParent returned
    ((LocalPrefix.store _ _ : LocalPrefix (ofString "nodes") _).summary_full two).2.1 remaining
  obtain ⟨third,thirdLocals⟩:=scalar_node_store_frame second geometry capSmall "n" node internal 0 (localVar "ni") nodeInside (by decide)
    secondData.nodesCell secondData.nodeCell (Request.local_word two "ni" internal secondData.internalCell) thirdRun
  have thirdData:=secondData.scalar_keep thirdLocals
  have safe : LocalPrefix (ofString "nodes") splitChildren:=by
    rw [splice_shapes.2.2.2.2.2.2.2.1,leftFresh,rightFresh]
    exact .ite _ (.seq (.store _ _) (.store _ _)) (.seq (.store _ _) (.store _ _))
  rw [splice_shapes.2.2.2.2.2.2.1] at remaining
  obtain ⟨children,splitRun,finish⟩:=sequence_returned three post splitChildren afterSplit returned (safe.summary_full three).2.1 remaining
  obtain ⟨childrenFrame,childrenLocals⟩:=scalar_split_frame_at third geometry capSmall internalInside thirdData splitRun
  exact scalar_after_split_frame_at childrenFrame geometry capSmall parentInside (thirdData.scalar_keep childrenLocals) returned finish

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_split_frame_at
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_after_split_frame_at
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_splice_frame_at

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The original second-insertion interface now uses the same general
actual rewiring proof as subsequent in-range insertions. -/
theorem scalar_splice_frame {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer : BitVec 64} {difference : Nat}
    (frame : New.ScalarFrame origin source table key cap) (geometry : New.ScalarGeometry table key cap) (capSmall : cap.toNat≤2^32)
    (available : 3≤cap.toNat) (domain : source.memaddrs=InitE.ordinaryDomain) (aligned : table.toNat%8=0)
    (data : SpliceLocals source table (New.scalarNodesPointer table key cap) 1#64 0#64 2#64 3#64 pointer difference)
    (nodesCell : source.memory (table+40#64)=.word (New.scalarNodesPointer table key cap))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source splice=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ New.ScalarFrame origin post table key cap := by
  exact scalar_splice_frame_at (node:=1#64) (parent:=0#64) (leaf:=2#64) (internal:=3#64) frame geometry capSmall
    (by change 1≤cap.toNat; omega) (by change 0≤cap.toNat; omega)
    (by change 2≤cap.toNat; omega) available domain aligned data nodesCell returned normal

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_child_stores_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_splice_frame

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

/-- Normal original second-leaf/internal-node/splice execution retains the
same complete scalar allocation footprint. Both new indices and the old
node/zero-parent locals come from those actual calls and the real seek. -/
theorem scalar_single_fresh_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer old value : BitVec 64} {difference : Nat}
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (data : ScalarSetLocals source table key pointer value) (installed : OriginalCode.Installed source.code)
    (nodesCell : source.locals.lookup (ofString "nodes")=some (.val (.word (New.scalarNodesPointer table key cap))))
    (nodeCell : source.locals.lookup (ofString "n")=some (.val (.word 1#64)))
    (parentCell : source.locals.lookup (ofString "p")=some (.val (.word 0#64)))
    (differenceCell : source.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 difference))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source newLeafCall=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ New.ScalarFrame source post table key cap := by
  rw [splice_shapes.1] at normal
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) leafArguments=
      some [.val (.word table),.val (.word pointer),.val (.word value)]:=by
    simp [leafArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.tableCell,data.keyCell,data.valueCell]
  rcases NewLeaf.scoped_scalar_single_trace source post table key cap pointer 1#64 old value single available installed "nl" leafArguments newInternalCall args (some (.returned returned)) normal with stopped|reached
  · exact (stopped.2 returned rfl).elim
  · obtain ⟨leafTarget,leafInner,leafFrame,ready,baseField,forward,price,continued,outerEndpoint⟩:=reached
    let current:=CallNormal.continuationEntry source leafTarget "nl" (.val (.word 2#64))
    have currentReady : NewNode.Context current table 3#64 cap:=ready.of_frame rfl
    have currentData : ScalarSetLocals current table key pointer value:=data.resume leafTarget "nl" _ (by decide) (by decide) (by decide) (by decide) (by decide)
    have currentDifference : current.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 difference))):=
      (CallNormal.continuation_lookup_other source leafTarget "nl" "d" (.val (.word 2#64)) (by decide)).trans differenceCell
    have currentCode : current.code=source.code:=MemoryMetadata.code leafFrame.fields
    have currentInstalled : OriginalCode.Installed current.code:=by rw [currentCode]; exact installed
    obtain ⟨callee,called,tCell,bCell⟩:=word_pair_environment current.code.lookup (ofString "htab_new_internal")
      (ofString "t") (ofString "bit") NewInternal.body .one table (BitVec.ofNat 64 difference) (by decide) (NewInternal.original_code current.code currentInstalled)
    have internalArgs : evalListHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) [localVar "t",localVar "d"]=
        some [.val (.word table),.val (.word (BitVec.ofNat 64 difference))]:=by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,currentData.tableCell,currentDifference]
    rw [splice_shapes.2.1] at continued
    obtain ⟨funded,internalTarget,index,inner,bodyRun,checked,spliceRun,innerEndpoint⟩:=CallNormal.scoped_normal current leafInner "ni" .one (ofString "htab_new_internal")
      [localVar "t",localVar "d"] _ NewInternal.body splice callee .one internalArgs called returned continued
    obtain ⟨indexEq,internalFrame,internalBase⟩:=NewInternal.scalar_frame (callEntryStateHOLFinite current callee) internalTarget table key cap 3#64 (BitVec.ofNat 64 difference)
      (currentReady.of_frame rfl) single.geometry single.capSmall currentInstalled tCell bCell baseField index bodyRun
    rw [indexEq] at spliceRun
    let finalEntry:=CallNormal.continuationEntry current internalTarget "ni" (.val (.word 3#64))
    have beforeFrame : New.ScalarFrame source current table key cap:=leafFrame.of_erase rfl rfl
    have constructorFrame : New.ScalarFrame current finalEntry table key cap:=internalFrame.of_erase rfl rfl
    have fullFrame:=beforeFrame.trans constructorFrame
    have locals : SpliceLocals finalEntry table (New.scalarNodesPointer table key cap) 1#64 0#64 2#64 3#64 pointer difference:=
      SpliceLocals.from_scoped source leafTarget internalTarget table _ 1#64 0#64 2#64 3#64 pointer difference
        data.tableCell nodesCell nodeCell parentCell data.keyCell differenceCell
    obtain ⟨answer,finished⟩:=scalar_splice_frame fullFrame single.geometry single.capSmall available
      ((MemoryMetadata.domain fullFrame.fields).trans single.domain) single.aligned locals internalBase returned spliceRun
    have scope : LocalEffects.erase post=LocalEffects.erase inner:=by rw [outerEndpoint,innerEndpoint]; rfl
    exact ⟨answer,finished.of_erase rfl scope⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_fresh_frame

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

/-- The same real bounded difference/setup/seek execution supplies n1,p0
and both fresh constructors. Only normal continuations retain a table frame. -/
theorem scalar_single_after_difference_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer old value : BitVec 64} {difference : Nat}
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (data : ScalarSetLocals source table key pointer value) (installed : OriginalCode.Installed source.code)
    (bounded : difference≤8*key.toNat)
    (differenceCell : source.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 difference))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterDifference=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ New.ScalarFrame source post table key cap := by
  let base:=New.scalarNodesPointer table key cap
  have nodesRead:=NewNode.field_read source table base 40 single.domain single.geometry.table single.aligned (by decide) (by decide) data.tableCell
    (single.fields (table+40#64,base) (by simp [base,New.singleHeaderWrites]))
  rw [scalar_difference_shapes.1] at normal
  obtain ⟨nodesInner,continued,nodesEndpoint⟩:=ScalarScope.declare_trace source post "nodes" _ base afterNodes (some (.returned returned)) nodesRead normal
  let first:=bind source "nodes" base
  have firstData : ScalarSetLocals first table key pointer value:=data.with_local "nodes" base (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [scalar_difference_shapes.2.1] at continued
  obtain ⟨parentInner,continued,parentEndpoint⟩:=ScalarScope.declare_trace first nodesInner "p" (.const 0#64) 0#64 afterParent (some (.returned returned)) rfl continued
  let second:=bind first "p" 0#64
  have secondData : ScalarSetLocals second table key pointer value:=firstData.with_local "p" 0#64 (by decide) (by decide) (by decide) (by decide) (by decide)
  have rootRead:=NewNode.field_read second table 1#64 56 single.domain single.geometry.table single.aligned (by decide) (by decide) secondData.tableCell
    (single.fields (table+56#64,1#64) (by simp [New.singleHeaderWrites]))
  rw [scalar_difference_shapes.2.2] at continued
  obtain ⟨nodeInner,continued,nodeEndpoint⟩:=ScalarScope.declare_trace second parentInner "n" _ 1#64 afterNode (some (.returned returned)) rootRead continued
  let entry:=bind second "n" 1#64
  have entryData : ScalarSetLocals entry table key pointer value:=secondData.with_local "n" 1#64 (by decide) (by decide) (by decide) (by decide) (by decide)
  have entryDifference : entry.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 difference))):=by
    simpa [entry,second,first,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using differenceCell
  have baseCell : entry.locals.lookup (ofString "nodes")=some (.val (.word base)):=
    (bind_lookup_other second "n" "nodes" 1#64 (by decide)).trans
      ((bind_lookup_other first "p" "nodes" 0#64 (by decide)).trans (bind_lookup_same _ _ _))
  have nodeCell : entry.locals.lookup (ofString "n")=some (.val (.word 1#64)):=bind_lookup_same _ _ _
  have parentCell : entry.locals.lookup (ofString "p")=some (.val (.word 0#64)):=
    (bind_lookup_other second "n" "p" 1#64 (by decide)).trans (bind_lookup_same _ _ _)
  have inside : (1#64 : BitVec 64).toNat≤cap.toNat:=by change 1≤cap.toNat; omega
  have array : AllocatedBytes.Arena base (32*(cap.toNat+1)):=by
    simpa only [base,(New.size_numbers cap single.capSmall).1] using single.geometry.nodes
  have mapped : entry.memaddrs (FindLeaf.cell base 1#64 24):=
    AllocatedBytes.word_mapped entry (slot base 1#64 32) 32 24 single.domain (slot_arena base 1#64 cap 32 array inside) (by decide)
      (slot_aligned base 1#64 cap 32 array inside single.geometry.nodesAligned (by decide)) (by decide)
  have markerNumber : (key*8#64).toNat=8*key.toNat:=by
    rw [BitVec.toNat_mul]
    change key.toNat*8%18446744073709551616=8*key.toNat
    rw [Nat.mod_eq_of_lt (by have small:=single.keySmall; omega)]
    omega
  have differenceNumber : (BitVec.ofNat 64 difference).toNat=difference:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have small:=single.keySmall; omega)]
  have loopRun:=scalar_seek_loop entry base (key*8#64) (BitVec.ofNat 64 difference) (by rw [markerNumber,differenceNumber]; exact bounded)
    baseCell nodeCell entryDifference mapped single.leafMarker
  have never : ∀ value,(evaluateHOLFiniteState entry seek).1≠some (.returned value):=by
    intro value
    by_cases zero : entry.clock=0 <;> simp [loopRun,zero]
  rw [seek_shapes.1] at continued
  obtain ⟨target,seekRun,tail⟩:=sequence_returned entry nodeInner seek newLeafCall returned never continued
  by_cases zero : entry.clock=0
  · rw [loopRun,if_pos zero] at seekRun
    cases seekRun
  · rw [loopRun,if_neg zero] at seekRun
    have targetEq : target=decClockHOLFinite entry:=(congrArg Prod.snd seekRun).symm
    subst target
    have tickData : ScalarSetLocals (decClockHOLFinite entry) table key pointer value:=
      ⟨entryData.tableCell,entryData.keyCell,entryData.valueCell,entryData.lengthCell,entryData.strideCell⟩
    obtain ⟨answer,frame⟩:=scalar_single_fresh_frame (source:=decClockHOLFinite entry) (single.of_erase rfl) available tickData installed
      baseCell nodeCell parentCell entryDifference returned tail
    have scope : LocalEffects.erase post=LocalEffects.erase nodeInner:=by rw [nodesEndpoint,parentEndpoint,nodeEndpoint]; rfl
    exact ⟨answer,frame.of_erase rfl scope⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_after_difference_frame

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

/-- The real normal first-difference call resumes at its own bounded result;
its read-only frame is composed with the actual insertion stores. -/
theorem scalar_single_difference_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer old value : BitVec 64}
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (data : ScalarSetLocals source table key pointer value) (installed : OriginalCode.Installed source.code)
    (keysCell : source.locals.lookup (ofString "keys")=some (.val (.word (New.keysPointer table))))
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word 1#64)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source differenceCall=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ New.ScalarFrame source post table key cap := by
  rw [entry_shapes.2.2.2.2.2.2] at normal
  let arguments : List (ExpHOL 64):=[localVar "key",.op .add [localVar "keys",.panop .mul [localVar "leaf",localVar "stride"]],localVar "klen"]
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word pointer),.val (.word (New.keysPointer table+New.strideWord key)),.val (.word (BitVec.ofNat 64 key.toNat))]:=by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.keyCell,data.lengthCell,data.strideCell,keysCell,leafCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  rcases FirstDiff.scoped_scalar_trace source post pointer (New.keysPointer table+New.strideWord key) key.toNat single.keySmall installed
    "d" arguments afterDifference args (some (.returned returned)) normal with stopped|reached
  · exact (stopped.2 returned rfl).elim
  · obtain ⟨target,inner,position,bounded,physical,forward,price,continued,endpoint⟩:=reached
    let current:=CallNormal.continuationEntry source target "d" (.val (.word (BitVec.ofNat 64 position)))
    have currentData : ScalarSetLocals current table key pointer value:=data.resume target "d" _ (by decide) (by decide) (by decide) (by decide) (by decide)
    have currentInstalled : OriginalCode.Installed current.code:=by rw [LocalEffects.code_of_erase source current physical]; exact installed
    obtain ⟨answer,frame⟩:=scalar_single_after_difference_frame (source:=current) (single.of_erase physical) available currentData currentInstalled bounded
      (CallNormal.continuation_lookup_same source target "d" _) returned continued
    exact ⟨answer,frame.of_erase physical.symm (by rw [endpoint] <;> rfl)⟩

/-- The actual existing-key branch updates the singleton's real leaf
value and returns zero; no key-copy/equality assertion is needed here. -/
theorem scalar_single_update_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer old value : BitVec 64)
    (single : New.ScalarSingle source table key cap 1#64 old) (data : ScalarSetLocals source table key pointer value)
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word 1#64))) :
    evaluateHOLFiniteState source updateBody=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite (putNode source (New.scalarNodesPointer table key cap) 1#64 8 value)) := by
  let base:=New.scalarNodesPointer table key cap
  let destination : ExpHOL 64:=.op .add [.load .one (.op .add [localVar "t",.const 40#64]),.panop .mul [localVar "leaf",.const 32#64],.const 8#64]
  have nodesRead:=NewNode.field_read source table base 40 single.domain single.geometry.table single.aligned (by decide) (by decide) data.tableCell
    (single.fields (table+40#64,base) (by simp [base,New.singleHeaderWrites]))
  change eval source (.load .one (.op .add [localVar "t",.const 40#64]))=some (.val (.word base)) at nodesRead
  have addressRead : eval source destination=some (.val (.word (FindLeaf.cell base 1#64 8))):=by
    simp only [eval] at nodesRead ⊢
    dsimp only [destination]
    rw [evalHOLExact]
    simp only [evalListHOLExact,nodesRead]
    simp [evalHOLExact,evalListHOLExact,localVar,leafCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,FindLeaf.cell,BitVec.add_assoc]
  have inside : (1#64 : BitVec 64).toNat≤cap.toNat:=by have lower:=single.capLower; change 1≤cap.toNat; omega
  have array : AllocatedBytes.Arena base (32*(cap.toNat+1)):=by
    simpa only [base,(New.size_numbers cap single.capSmall).1] using single.geometry.nodes
  have mapped : source.memaddrs (FindLeaf.cell base 1#64 8):=
    AllocatedBytes.word_mapped source (slot base 1#64 32) 32 8 single.domain (slot_arena base 1#64 cap 32 array inside) (by decide)
      (slot_aligned base 1#64 cap 32 array inside single.geometry.nodesAligned (by decide)) (by decide)
  have stored:=StoreWord.execute source destination (localVar "value") (FindLeaf.cell base 1#64 8) value addressRead
    (Request.local_word source "value" value data.valueCell) mapped
  change evaluateHOLFiniteState source (.store destination (localVar "value"))=(none,putNode source base 1#64 8 value) at stored
  rw [guard_shapes.2.2.2.2.1]
  change evaluateHOLFiniteState source (.seq (.store destination (localVar "value")) (.return (.const 0#64)))=_
  rw [evaluateHOLFiniteState_seq_line780,stored]
  simp [base,evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]

/-- Both actual normal comparison branches retain exactly the same
external memory; a failed condition cannot be a normal returned setter. -/
theorem scalar_single_after_compare_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer old value : BitVec 64}
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (data : ScalarSetLocals source table key pointer value) (installed : OriginalCode.Installed source.code)
    (keysCell : source.locals.lookup (ofString "keys")=some (.val (.word (New.keysPointer table))))
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word 1#64)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterCompare=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ New.ScalarFrame source post table key cap := by
  have updateRun:=scalar_single_update_execute source table key cap pointer old value single data leafCell
  rw [entry_shapes.2.2.2.2.2.1,guard_shapes.2.2.2.1,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite] at normal
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact (fun query=>Classical.propDecidable (source.memaddrs query))
    (.cmp .notEqual (localVar "eq") (.const 0#64))=read at normal
  cases read with
  | none=>cases normal
  | some read=>
    cases read with
    | rStruct fields=>cases normal
    | nStruct name fields=>cases normal
    | val payload=>
      cases payload with
      | word word=>
        simp only at normal
        by_cases zero : word=0
        · rw [if_pos zero,evaluateHOLFiniteState_skip] at normal
          exact scalar_single_difference_frame single available data installed keysCell leafCell returned normal
        · rw [if_neg zero,updateRun] at normal
          have answer : returned=.val (.word 0#64):=by
            simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using (congrArg Prod.fst normal).symm
          have endpoint : post=emptyLocalsHOLFinite (putNode source (New.scalarNodesPointer table key cap) 1#64 8 value):=(congrArg Prod.snd normal).symm
          have frame:=(New.ScalarFrame.refl source table key cap).put_node single.geometry single.capSmall 1#64 value 8
            (by change 1≤cap.toNat; omega) (by decide)
          exact ⟨answer,frame.of_erase rfl (by rw [endpoint] <;> rfl)⟩

/-- Compose the actual memeq return's full read-only frame with whichever
normal setter branch was really run, retaining the same physical table. -/
theorem scalar_single_compare_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer old value : BitVec 64}
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (data : ScalarSetLocals source table key pointer value) (installed : OriginalCode.Installed source.code)
    (keysCell : source.locals.lookup (ofString "keys")=some (.val (.word (New.keysPointer table))))
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word 1#64)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source compareCall=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ New.ScalarFrame source post table key cap := by
  rw [guard_shapes.2.2.2.2.2] at normal
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) compareArguments=
      some [.val (.word (New.keysPointer table+New.strideWord key)),.val (.word pointer),.val (.word (BitVec.ofNat 64 key.toNat))]:=by
    simp [compareArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.keyCell,data.lengthCell,data.strideCell,keysCell,leafCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  obtain ⟨callee,called,aCell,bCell,nCell⟩:=MutableTable.MemeqByteRuntime.environment source.code.lookup (New.keysPointer table+New.strideWord key) pointer key.toNat
    (MutableTable.MemeqAny.original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨funded,target,result,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_normal source post "eq" .one (ofString "memeq")
    compareArguments _ Memeq32.body afterCompare callee .one args called returned normal
  let current:=CallNormal.continuationEntry source target "eq" result
  have physical:=MutableTable.MemeqAny.readonly source.code entry rfl
  rw [bodyRun] at physical
  have currentData : ScalarSetLocals current table key pointer value:=data.resume target "eq" result (by decide) (by decide) (by decide) (by decide) (by decide)
  have currentKeys : current.locals.lookup (ofString "keys")=some (.val (.word (New.keysPointer table))):=
    (CallNormal.continuation_lookup_other source target "eq" "keys" result (by decide)).trans keysCell
  have currentLeaf : current.locals.lookup (ofString "leaf")=some (.val (.word 1#64)):=
    (CallNormal.continuation_lookup_other source target "eq" "leaf" result (by decide)).trans leafCell
  have currentInstalled : OriginalCode.Installed current.code:=by rw [LocalEffects.code_of_erase source current physical]; exact installed
  obtain ⟨answer,frame⟩:=scalar_single_after_compare_frame (source:=current) (single.of_erase physical) available currentData currentInstalled currentKeys currentLeaf returned continued
  exact ⟨answer,frame.of_erase physical.symm (by rw [endpoint] <;> rfl)⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_difference_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_update_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_after_compare_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_compare_frame

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

/-- Real key-base declaration and its lexical restoration retain the same
normal setter frame after the actual nonempty-leaf guard. -/
theorem scalar_single_after_leaf_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer old value : BitVec 64}
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (data : ScalarSetLocals source table key pointer value) (installed : OriginalCode.Installed source.code)
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word 1#64)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterLeaf=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ New.ScalarFrame source post table key cap := by
  have keysRead:=NewNode.field_read source table (New.keysPointer table) 32 single.domain single.geometry.table single.aligned (by decide) (by decide) data.tableCell
    (single.fields (table+32#64,New.keysPointer table) (by simp [New.singleHeaderWrites]))
  rw [entry_shapes.2.2.2.1] at normal
  obtain ⟨inner,continued,endpoint⟩:=ScalarScope.declare_trace source post "keys" _ (New.keysPointer table) afterKeys (some (.returned returned)) keysRead normal
  let current:=bind source "keys" (New.keysPointer table)
  have currentData : ScalarSetLocals current table key pointer value:=data.with_local "keys" (New.keysPointer table) (by decide) (by decide) (by decide) (by decide) (by decide)
  have currentLeaf : current.locals.lookup (ofString "leaf")=some (.val (.word 1#64)):=
    (bind_lookup_other source "keys" "leaf" (New.keysPointer table) (by decide)).trans leafCell
  rw [scalar_single_after_keys current currentLeaf] at continued
  obtain ⟨answer,frame⟩:=scalar_single_compare_frame (source:=current) (single.of_erase rfl) available currentData installed (bind_lookup_same _ _ _) currentLeaf returned continued
  exact ⟨answer,frame.of_erase rfl (by rw [endpoint] <;> rfl)⟩

/-- The real singleton traversal identifies its actual leaf, then the
same normally returning setter supplies the complete write footprint. -/
theorem scalar_single_after_stride_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer old value : BitVec 64}
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (data : ScalarSetLocals source table key pointer value) (installed : OriginalCode.Installed source.code)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterStride=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ New.ScalarFrame source post table key cap := by
  rw [entry_shapes.2.2.1] at normal
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "t",localVar "key"]=
      some [.val (.word table),.val (.word pointer)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.tableCell,data.keyCell]
  rcases FindLeaf.scoped_scalar_single_trace source post table key cap old pointer single installed "leaf" [localVar "t",localVar "key"] afterLeaf args (some (.returned returned)) normal with stopped|reached
  · exact (stopped.2 returned rfl).elim
  · obtain ⟨target,inner,physical,forward,price,continued,endpoint⟩:=reached
    let current:=CallNormal.continuationEntry source target "leaf" (.val (.word 1#64))
    have currentData : ScalarSetLocals current table key pointer value:=data.resume target "leaf" _ (by decide) (by decide) (by decide) (by decide) (by decide)
    have currentInstalled : OriginalCode.Installed current.code:=by rw [LocalEffects.code_of_erase source current physical]; exact installed
    obtain ⟨answer,frame⟩:=scalar_single_after_leaf_frame (source:=current) (single.of_erase physical) available currentData currentInstalled
      (CallNormal.continuation_lookup_same source target "leaf" _) returned continued
    exact ⟨answer,frame.of_erase physical.symm (by rw [endpoint] <;> rfl)⟩

/-- Complete unchanged singleton setter normal return: actual literal zero
and a complete table write footprint, including both real comparison paths. -/
theorem scalar_single_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer old value : BitVec 64}
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ New.ScalarFrame source post table key cap := by
  have lengthRead:=NewNode.field_read source table key 0 single.domain single.geometry.table single.aligned (by decide) (by decide) tableCell
    (single.fields (table+0#64,key) (by simp [New.singleHeaderWrites]))
  rw [entry_shapes.1] at normal
  obtain ⟨middle,continued,endpoint⟩:=ScalarScope.declare_trace source post "klen" _ key afterLength (some (.returned returned)) lengthRead normal
  let first:=bind source "klen" key
  have firstTable : first.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other source "klen" "t" key (by decide)).trans tableCell
  have strideRead:=NewNode.field_read first table (New.strideWord key) 8 single.domain single.geometry.table single.aligned (by decide) (by decide) firstTable
    (single.fields (table+8#64,New.strideWord key) (by simp [New.singleHeaderWrites]))
  rw [entry_shapes.2.1] at continued
  obtain ⟨inner,remaining,innerEndpoint⟩:=ScalarScope.declare_trace first middle "stride" _ (New.strideWord key) afterStride (some (.returned returned)) strideRead continued
  let current:=bind first "stride" (New.strideWord key)
  have kept (name : String) (notStride : ofString "stride"≠ofString name) (notLength : ofString "klen"≠ofString name) :
      current.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    (bind_lookup_other first "stride" name (New.strideWord key) notStride).trans (bind_lookup_other source "klen" name key notLength)
  have data : ScalarSetLocals current table key pointer value:=
    ⟨(kept "t" (by decide) (by decide)).trans tableCell,(kept "key" (by decide) (by decide)).trans keyCell,
      (kept "value" (by decide) (by decide)).trans valueCell,
      (bind_lookup_other first "stride" "klen" (New.strideWord key) (by decide)).trans (bind_lookup_same _ _ _),bind_lookup_same _ _ _⟩
  obtain ⟨answer,frame⟩:=scalar_single_after_stride_frame (source:=current) (single.of_erase rfl) available data installed returned remaining
  exact ⟨answer,frame.of_erase rfl (by rw [endpoint,innerEndpoint] <;> rfl)⟩

/-- The real ignored caller restores its actual saved locals and retains
the complete scalar allocation footprint of the same normal singleton set. -/
theorem scalar_single_call_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer old value : BitVec 64}
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (installed : OriginalCode.Installed source.code) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word table),.val (.word pointer),.val (.word value)])
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htab_set") arguments)=(none,post)) :
    New.ScalarFrame source post table key cap ∧ post.locals=source.locals := by
  obtain ⟨callee,called,tCell,kCell,vCell⟩:=word_triple_environment source.code.lookup (ofString "htab_set")
    (ofString "t") (ofString "key") (ofString "value") body .one table pointer value
    (by decide) (by decide) (by decide) (original_code source.code installed)
  obtain ⟨funded,values,actual,actualCallee,shape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩:=CallNormal.ignored_data source post (ofString "htab_set") arguments normal
  have sameValues : values=[.val (.word table),.val (.word pointer),.val (.word value)]:=Option.some.inj (actualArgs.symm.trans args)
  subst values
  have same : (actual,actualCallee,shape)=(body,callee,.one):=Option.some.inj (actualCalled.symm.trans called)
  cases same
  obtain ⟨answer,frame⟩:=scalar_single_frame (source:=callEntryStateHOLFinite source callee) (single.of_erase rfl) available installed tCell kCell vCell returned bodyRun
  exact ⟨frame.of_erase rfl (by rw [endpoint] <;> rfl),by rw [endpoint]⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_after_leaf_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_after_stride_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_call_frame


namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem ScalarGeometry.node_order_away {table key cap : BitVec 64} (geometry : ScalarGeometry table key cap)
    (capSmall : cap.toNat≤2^32) (node pos : BitVec 64) (inside : node.toNat≤cap.toNat) (posInside : pos.toNat≤cap.toNat)
    (offset : Nat) (small : offset<32) :
    FindLeaf.cell (scalarNodesPointer table key cap) node offset≠slot (scalarOrderPointer table key cap) pos 8 := by
  have nodes : AllocatedBytes.Arena (scalarNodesPointer table key cap) (32*(cap.toNat+1)):=by
    simpa only [(size_numbers cap capSmall).1] using geometry.nodes
  have order : AllocatedBytes.Arena (scalarOrderPointer table key cap) (8*(cap.toNat+1)):=by
    simpa only [(size_numbers cap capSmall).2] using geometry.order
  have cellNumber:=cell_number _ node cap offset nodes inside small
  have orderNumber:=slot_number _ pos cap 8 order posInside
  have before:=geometry.nodesBefore
  rw [(size_numbers cap capSmall).1] at before
  intro same
  have number:=congrArg BitVec.toNat same
  rw [cellNumber,orderNumber] at number
  omega

theorem ScalarGeometry.header_order_away {table key cap : BitVec 64} (geometry : ScalarGeometry table key cap)
    (capSmall : cap.toNat≤2^32) (pos : BitVec 64) (posInside : pos.toNat≤cap.toNat) (offset : Nat) (small : offset<88) :
    table+BitVec.ofNat 64 offset≠slot (scalarOrderPointer table key cap) pos 8 := by
  have order : AllocatedBytes.Arena (scalarOrderPointer table key cap) (8*(cap.toNat+1)):=by
    simpa only [(size_numbers cap capSmall).2] using geometry.order
  have headerNumber : (table+BitVec.ofNat 64 offset).toNat=table.toNat+offset:=
    byteAddress_toNat table offset (by have upper:=geometry.table.upper; omega)
  have orderNumber:=slot_number _ pos cap 8 order posInside
  have a:=geometry.tableBefore
  have b:=geometry.keysBefore
  have c:=geometry.nodesBefore
  intro same
  have number:=congrArg BitVec.toNat same
  rw [headerNumber,orderNumber] at number
  omega

end InitECandidate.Solver.Input.CurrentTable.New

namespace InitECandidate.Solver.Input.CurrentTable.NewLeaf
open Flapjack PanSemStateFiniteExact WitnessRadix
set_option maxHeartbeats 1500000

/-- The actual four leaf stores are retained at any available node and
order index, including the second insertion's node2 and position1. -/
theorem scalar_stored_nodes_at (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap node pos value : BitVec 64)
    (geometry : New.ScalarGeometry table key cap) (capSmall : cap.toNat≤2^32)
    (inside : node.toNat≤cap.toNat) (posInside : pos.toNat≤cap.toNat) :
    (scalarStored source table key cap node pos value).memory (FindLeaf.cell (New.scalarNodesPointer table key cap) node 0)=.word 0#64 ∧
    (scalarStored source table key cap node pos value).memory (FindLeaf.cell (New.scalarNodesPointer table key cap) node 8)=.word value ∧
    (scalarStored source table key cap node pos value).memory (FindLeaf.cell (New.scalarNodesPointer table key cap) node 16)=.word pos ∧
    (scalarStored source table key cap node pos value).memory (FindLeaf.cell (New.scalarNodesPointer table key cap) node 24)=.word (key*8#64) := by
  have nodes : AllocatedBytes.Arena (New.scalarNodesPointer table key cap) (32*(cap.toNat+1)):=by
    simpa only [(New.size_numbers cap capSmall).1] using geometry.nodes
  have different (left right : Nat) (li : left<32) (ri : right<32) (ne : left≠right) :
      FindLeaf.cell (New.scalarNodesPointer table key cap) node left≠FindLeaf.cell (New.scalarNodesPointer table key cap) node right:=by
    intro same
    exact ne (cell_injective _ _ _ cap left right nodes inside inside li ri same).2
  have headerAway (offset : Nat) (small : offset<32) : FindLeaf.cell (New.scalarNodesPointer table key cap) node offset≠table+24#64:=
    Ne.symm (geometry.scalar_header_away capSmall node inside offset 24 small (by decide))
  have orderAway (offset : Nat) (small : offset<32) : FindLeaf.cell (New.scalarNodesPointer table key cap) node offset≠slot (New.scalarOrderPointer table key cap) pos 8:=
    geometry.node_order_away capSmall node pos inside posInside offset small
  repeat' constructor
  all_goals simp [scalarStored,scalarTailStored,scalarPutOrder,putNode,New.putField,StoreWord.put,headerAway,orderAway,different]

/-- Real new-leaf stores preserve every field of an older distinct node. -/
theorem scalar_stored_old_node (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap node pos value other : BitVec 64)
    (geometry : New.ScalarGeometry table key cap) (capSmall : cap.toNat≤2^32)
    (inside : node.toNat≤cap.toNat) (posInside : pos.toNat≤cap.toNat) (otherInside : other.toNat≤cap.toNat)
    (different : other≠node) (offset : Nat) (small : offset<32) :
    (scalarStored source table key cap node pos value).memory (FindLeaf.cell (New.scalarNodesPointer table key cap) other offset)=
      source.memory (FindLeaf.cell (New.scalarNodesPointer table key cap) other offset) := by
  have nodes : AllocatedBytes.Arena (New.scalarNodesPointer table key cap) (32*(cap.toNat+1)):=by
    simpa only [(New.size_numbers cap capSmall).1] using geometry.nodes
  have nodeAway (field : Nat) (fi : field<32) :
      FindLeaf.cell (New.scalarNodesPointer table key cap) other offset≠FindLeaf.cell (New.scalarNodesPointer table key cap) node field:=by
    intro same
    exact different (cell_injective _ _ _ cap offset field nodes otherInside inside small fi same).1
  have headerAway : FindLeaf.cell (New.scalarNodesPointer table key cap) other offset≠table+24#64:=
    Ne.symm (geometry.scalar_header_away capSmall other otherInside offset 24 small (by decide))
  have orderAway:=geometry.node_order_away capSmall other pos otherInside posInside offset small
  simp only [scalarStored,scalarTailStored,scalarPutOrder,putNode,New.putField,StoreWord.put,
    if_neg headerAway,if_neg orderAway,if_neg (nodeAway 0 (by decide)),if_neg (nodeAway 8 (by decide)),
    if_neg (nodeAway 16 (by decide)),if_neg (nodeAway 24 (by decide))]

theorem scalar_stored_order_at (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap node pos value : BitVec 64)
    (geometry : New.ScalarGeometry table key cap) (capSmall : cap.toNat≤2^32) (posInside : pos.toNat≤cap.toNat) :
    (scalarStored source table key cap node pos value).memory (slot (New.scalarOrderPointer table key cap) pos 8)=.word node := by
  have away:=Ne.symm (geometry.header_order_away capSmall pos posInside 24 (by decide))
  simp [scalarStored,scalarTailStored,scalarPutOrder,New.putField,StoreWord.put,away]

/-- A normal second leaf returns its exact actual copy/store snapshot.
The retained copy frame now also protects all older node/order fields. -/
theorem scalar_single_returned {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer root old value : BitVec 64}
    (single : New.ScalarSingle source table key cap root old) (available : 3≤cap.toNat)
    (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "value")=some (.val (.word value)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    returned=.val (.word 2#64) ∧ ∃ copied,ScalarCopiedAt source copied table key cap 2#64 ∧
      LocalEffects.erase post=LocalEffects.erase (scalarStored copied table key cap 2#64 1#64 value) := by
  have fields : ScalarFields source table key:=⟨single.domain,single.geometry.table,single.aligned,
    by simpa only [BitVec.add_zero] using single.fields (table+0#64,key) (by simp [New.singleHeaderWrites]),
    single.fields (table+8#64,New.strideWord key) (by simp [New.singleHeaderWrites]),
    single.fields (table+32#64,New.keysPointer table) (by simp [New.singleHeaderWrites])⟩
  have ready : NewNode.Context source table 2#64 cap:=⟨single.domain,single.geometry.table,single.aligned,
    single.fields (table+72#64,0#64) (by simp [New.singleHeaderWrites]),
    single.fields (table+64#64,2#64) (by simp [New.singleHeaderWrites]),
    single.fields (table+80#64,cap) (by simp [New.singleHeaderWrites]),single.capLower⟩
  exact scalar_no_grow_returned fields ready single.geometry installed tableCell keyCell valueCell single.keySmall single.capSmall
    (by change 1≤cap.toNat; omega) (single.fields (table+40#64,New.scalarNodesPointer table key cap) (by simp [New.singleHeaderWrites]))
    (single.fields (table+24#64,1#64) (by simp [New.singleHeaderWrites]))
    (single.fields (table+48#64,New.scalarOrderPointer table key cap) (by simp [New.singleHeaderWrites])) returned normal

end InitECandidate.Solver.Input.CurrentTable.NewLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarGeometry.node_order_away
#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarGeometry.header_order_away
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_stored_nodes_at
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_stored_old_node
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_stored_order_at
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_single_returned


namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack PanSemStateFiniteExact WitnessRadix

def pairHeaderWrites (table key cap root next : BitVec 64) : List (BitVec 64×BitVec 64):=
  [(table+0#64,key),(table+8#64,strideWord key),(table+16#64,cap),(table+24#64,2#64),
   (table+32#64,keysPointer table),(table+40#64,scalarNodesPointer table key cap),(table+48#64,scalarOrderPointer table key cap),
   (table+56#64,root),(table+64#64,next),(table+72#64,0#64),(table+80#64,cap)]

/-- The actual second leaf before internal-node allocation: its original
root remains, count is2, next is3 and both real leaf/order records are kept. -/
structure ScalarTwoLeaves (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap root old value : BitVec 64) : Prop where
  geometry : ScalarGeometry table key cap
  aligned : table.toNat%8=0
  domain : source.memaddrs=InitE.ordinaryDomain
  capLower : 2≤cap.toNat
  keySmall : key.toNat≤60
  capSmall : cap.toNat≤2^32
  fields : ∀ entry∈pairHeaderWrites table key cap root 3#64,source.memory entry.1=.word entry.2
  oldParent : source.memory (FindLeaf.cell (scalarNodesPointer table key cap) 1#64 0)=.word 0#64
  oldValue : source.memory (FindLeaf.cell (scalarNodesPointer table key cap) 1#64 8)=.word old
  oldPosition : source.memory (FindLeaf.cell (scalarNodesPointer table key cap) 1#64 16)=.word 0#64
  oldMarker : source.memory (FindLeaf.cell (scalarNodesPointer table key cap) 1#64 24)=.word (key*8#64)
  freshParent : source.memory (FindLeaf.cell (scalarNodesPointer table key cap) 2#64 0)=.word 0#64
  freshValue : source.memory (FindLeaf.cell (scalarNodesPointer table key cap) 2#64 8)=.word value
  freshPosition : source.memory (FindLeaf.cell (scalarNodesPointer table key cap) 2#64 16)=.word 1#64
  freshMarker : source.memory (FindLeaf.cell (scalarNodesPointer table key cap) 2#64 24)=.word (key*8#64)
  orderFirst : source.memory (scalarOrderPointer table key cap)=.word 1#64
  orderSecond : source.memory (slot (scalarOrderPointer table key cap) 1#64 8)=.word 2#64

theorem ScalarTwoLeaves.of_erase {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap root old value : BitVec 64}
    (image : ScalarTwoLeaves source table key cap root old value) (same : LocalEffects.erase post=LocalEffects.erase source) :
    ScalarTwoLeaves post table key cap root old value := by
  have memory:=LocalEffects.memory_of_erase source post same
  exact {image with
    domain:=(MemoryMetadata.domain (MemoryMetadata.of_frame same)).trans image.domain,
    fields:=by intro entry member; rw [memory]; exact image.fields entry member,
    oldParent:=by rw [memory]; exact image.oldParent,oldValue:=by rw [memory]; exact image.oldValue,
    oldPosition:=by rw [memory]; exact image.oldPosition,oldMarker:=by rw [memory]; exact image.oldMarker,
    freshParent:=by rw [memory]; exact image.freshParent,freshValue:=by rw [memory]; exact image.freshValue,
    freshPosition:=by rw [memory]; exact image.freshPosition,freshMarker:=by rw [memory]; exact image.freshMarker,
    orderFirst:=by rw [memory]; exact image.orderFirst,orderSecond:=by rw [memory]; exact image.orderSecond}

end InitECandidate.Solver.Input.CurrentTable.New

namespace InitECandidate.Solver.Input.CurrentTable.NewLeaf
open Flapjack PanSemStateFiniteExact WitnessRadix
set_option maxHeartbeats 2000000

theorem scalar_stored_old_order (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap node pos value other : BitVec 64)
    (geometry : New.ScalarGeometry table key cap) (capSmall : cap.toNat≤2^32)
    (inside : node.toNat≤cap.toNat) (posInside : pos.toNat≤cap.toNat) (otherInside : other.toNat≤cap.toNat) (different : other≠pos) :
    (scalarStored source table key cap node pos value).memory (slot (New.scalarOrderPointer table key cap) other 8)=
      source.memory (slot (New.scalarOrderPointer table key cap) other 8) := by
  have order : AllocatedBytes.Arena (New.scalarOrderPointer table key cap) (8*(cap.toNat+1)):=by
    simpa only [(New.size_numbers cap capSmall).2] using geometry.order
  have headerAway:=Ne.symm (geometry.header_order_away capSmall other otherInside 24 (by decide))
  have nodeAway (offset : Nat) (small : offset<32) :
      slot (New.scalarOrderPointer table key cap) other 8≠FindLeaf.cell (New.scalarNodesPointer table key cap) node offset:=
    Ne.symm (geometry.node_order_away capSmall node other inside otherInside offset small)
  have orderAway : slot (New.scalarOrderPointer table key cap) other 8≠slot (New.scalarOrderPointer table key cap) pos 8:=by
    intro same
    have number:=congrArg BitVec.toNat same
    rw [slot_number _ other cap 8 order otherInside,slot_number _ pos cap 8 order posInside] at number
    exact different (BitVec.eq_of_toNat_eq (by omega))
  simp only [scalarStored,scalarTailStored,scalarPutOrder,putNode,New.putField,StoreWord.put,
    if_neg headerAway,if_neg orderAway,if_neg (nodeAway 0 (by decide)),if_neg (nodeAway 8 (by decide)),
    if_neg (nodeAway 16 (by decide)),if_neg (nodeAway 24 (by decide))]

/-- Derive the complete populated two-leaf image from this same original
constructor execution, including the older leaf protected by the key copy. -/
theorem scalar_single_two_leaves {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer root old value : BitVec 64}
    (single : New.ScalarSingle source table key cap root old) (available : 3≤cap.toNat)
    (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "value")=some (.val (.word value)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    returned=.val (.word 2#64) ∧ New.ScalarFrame source post table key cap ∧ New.ScalarTwoLeaves post table key cap root old value := by
  obtain ⟨answer,copied,physical,scope⟩:=scalar_single_returned single available installed tableCell keyCell valueCell returned normal
  obtain ⟨answerAgain,frame,ready,nodesCell⟩:=scalar_single_frame single available installed tableCell keyCell valueCell returned normal
  have memory:=LocalEffects.memory_of_erase (scalarStored copied table key cap 2#64 1#64 value) post scope
  have secondInside : (2#64 : BitVec 64).toNat≤cap.toNat:=single.capLower
  have firstInside : (1#64 : BitVec 64).toNat≤cap.toNat:=by have bound:=single.capLower; change 1≤cap.toNat; omega
  have header (offset : Nat) (inside : offset<88) : post.memory (table+BitVec.ofNat 64 offset)=
      (New.putField (New.putField source table 64 3#64) table 24 2#64).memory (table+BitVec.ofNat 64 offset):=by
    rw [memory,scalar_stored_header_at copied table key cap 2#64 1#64 value single.geometry single.capSmall secondInside firstInside offset inside]
    change (if table+BitVec.ofNat 64 offset=table+24#64 then .word 2#64 else copied.memory (table+BitVec.ofNat 64 offset))=_
    change _=(if table+BitVec.ofNat 64 offset=table+24#64 then .word 2#64 else (New.putField source table 64 3#64).memory (table+BitVec.ofNat 64 offset))
    split
    · rfl
    · exact physical.header offset inside
  have kept (offset : Nat) (inside : offset<88) (notCount : offset≠24) (notNext : offset≠64) :
      post.memory (table+BitVec.ofNat 64 offset)=source.memory (table+BitVec.ofNat 64 offset):=
    (header offset inside).trans ((header_other (New.putField source table 64 3#64) table 2#64 24 offset single.geometry.table (by decide) inside notCount).trans
      (header_other source table 3#64 64 offset single.geometry.table (by decide) inside notNext))
  have fields : ∀ entry∈New.pairHeaderWrites table key cap root 3#64,post.memory entry.1=.word entry.2:=by
    intro entry member
    simp only [New.pairHeaderWrites,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact (kept 0 (by decide) (by decide) (by decide)).trans (single.fields (table+0#64,key) (by simp [New.singleHeaderWrites]))
    · exact (kept 8 (by decide) (by decide) (by decide)).trans (single.fields (table+8#64,New.strideWord key) (by simp [New.singleHeaderWrites]))
    · exact (kept 16 (by decide) (by decide) (by decide)).trans (single.fields (table+16#64,cap) (by simp [New.singleHeaderWrites]))
    · rw [header 24 (by decide)]
      simp [New.putField,StoreWord.put]
    · exact (kept 32 (by decide) (by decide) (by decide)).trans (single.fields (table+32#64,New.keysPointer table) (by simp [New.singleHeaderWrites]))
    · exact (kept 40 (by decide) (by decide) (by decide)).trans (single.fields (table+40#64,New.scalarNodesPointer table key cap) (by simp [New.singleHeaderWrites]))
    · exact (kept 48 (by decide) (by decide) (by decide)).trans (single.fields (table+48#64,New.scalarOrderPointer table key cap) (by simp [New.singleHeaderWrites]))
    · exact (kept 56 (by decide) (by decide) (by decide)).trans (single.fields (table+56#64,root) (by simp [New.singleHeaderWrites]))
    · rw [header 64 (by decide),header_other (New.putField source table 64 3#64) table 2#64 24 64 single.geometry.table (by decide) (by decide) (by decide)]
      simp [New.putField,StoreWord.put]
    · exact (kept 72 (by decide) (by decide) (by decide)).trans (single.fields (table+72#64,0#64) (by simp [New.singleHeaderWrites]))
    · exact (kept 80 (by decide) (by decide) (by decide)).trans (single.fields (table+80#64,cap) (by simp [New.singleHeaderWrites]))
  have nodes : AllocatedBytes.Arena (New.scalarNodesPointer table key cap) (32*(cap.toNat+1)):=by
    simpa only [(New.size_numbers cap single.capSmall).1] using single.geometry.nodes
  have oldMemory (offset : Nat) (small : offset<32) :
      post.memory (FindLeaf.cell (New.scalarNodesPointer table key cap) 1#64 offset)=source.memory (FindLeaf.cell (New.scalarNodesPointer table key cap) 1#64 offset):=by
    rw [memory,scalar_stored_old_node copied table key cap 2#64 1#64 value 1#64 single.geometry single.capSmall secondInside firstInside firstInside (by decide) offset small]
    apply physical.afterNodes
    rw [cell_number _ 1#64 cap offset nodes firstInside small]
    omega
  have fresh:=scalar_stored_nodes_at copied table key cap 2#64 1#64 value single.geometry single.capSmall secondInside firstInside
  have order : AllocatedBytes.Arena (New.scalarOrderPointer table key cap) (8*(cap.toNat+1)):=by
    simpa only [(New.size_numbers cap single.capSmall).2] using single.geometry.order
  have firstOrder : post.memory (New.scalarOrderPointer table key cap)=.word 1#64:=by
    have zero : slot (New.scalarOrderPointer table key cap) 0#64 8=New.scalarOrderPointer table key cap:=by simp [slot]
    rw [←zero,memory,scalar_stored_old_order copied table key cap 2#64 1#64 value 0#64 single.geometry single.capSmall secondInside firstInside (by change 0≤cap.toNat; omega) (by decide)]
    rw [physical.afterNodes _ (by
      rw [slot_number _ 0#64 cap 8 order (by change 0≤cap.toNat; omega)]
      have before:=single.geometry.nodesBefore
      omega),zero]
    exact single.orderFirst
  have secondOrder : post.memory (slot (New.scalarOrderPointer table key cap) 1#64 8)=.word 2#64:=by
    rw [memory]
    exact scalar_stored_order_at copied table key cap 2#64 1#64 value single.geometry single.capSmall firstInside
  exact ⟨answer,frame,single.geometry,single.aligned,(MemoryMetadata.domain frame.fields).trans single.domain,
    single.capLower,single.keySmall,single.capSmall,fields,
    (oldMemory 0 (by decide)).trans single.leafZero,(oldMemory 8 (by decide)).trans single.leafValue,
    (oldMemory 16 (by decide)).trans single.leafPosition,(oldMemory 24 (by decide)).trans single.leafMarker,
    (congrFun memory _).trans fresh.1,(congrFun memory _).trans fresh.2.1,
    (congrFun memory _).trans fresh.2.2.1,(congrFun memory _).trans fresh.2.2.2,firstOrder,secondOrder⟩

end InitECandidate.Solver.Input.CurrentTable.NewLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarTwoLeaves.of_erase
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_stored_old_order
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_single_two_leaves


namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def scalarChildStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (freshLeft : Bool) :=
  putNode (putNode source base 3#64 8 (if freshLeft then 2#64 else 1#64)) base 3#64 16 (if freshLeft then 1#64 else 2#64)

def scalarSpliceStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table base : BitVec 64) (freshLeft : Bool) :=
  New.putField (scalarChildStored
    (putNode (putNode (putNode source base 3#64 0 0#64) base 2#64 0 3#64) base 1#64 0 3#64)
    base freshLeft) table 56 3#64

/-- The observed normal node store fixes its actual full target state;
address mapping is extracted from execution rather than assumed. -/
theorem scalar_node_store_state {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {base node value : BitVec 64}
    (name : String) (offset : Nat) (expression : ExpHOL 64)
    (baseCell : source.locals.lookup (ofString "nodes")=some (.val (.word base)))
    (nodeCell : source.locals.lookup (ofString name)=some (.val (.word node)))
    (valueRead : eval source expression=some (.val (.word value)))
    (normal : evaluateHOLFiniteState source (.store (nodeFor name offset) expression)=(none,post)) :
    post=putNode source base node offset value := by
  obtain ⟨mapped,endpoint⟩:=word_store_normal source post _ _ _ _ (named_node_read source base node name offset baseCell nodeCell) valueRead normal
  exact endpoint

theorem scalar_child_stores_state {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {base left right : BitVec 64}
    (leftName rightName : String)
    (baseCell : source.locals.lookup (ofString "nodes")=some (.val (.word base)))
    (internalCell : source.locals.lookup (ofString "ni")=some (.val (.word 3#64)))
    (leftCell : source.locals.lookup (ofString leftName)=some (.val (.word left)))
    (rightCell : source.locals.lookup (ofString rightName)=some (.val (.word right)))
    (normal : evaluateHOLFiniteState source (.seq (.store (nodeFor "ni" 8) (localVar leftName)) (.store (nodeFor "ni" 16) (localVar rightName)))=(none,post)) :
    post=putNode (putNode source base 3#64 8 left) base 3#64 16 right := by
  obtain ⟨middle,front,back⟩:=sequence_none source post _ _ normal
  have first:=scalar_node_store_state "ni" 8 (localVar leftName) baseCell internalCell (Request.local_word source leftName left leftCell) front
  have last:=scalar_node_store_state "ni" 16 (localVar rightName)
    (by rw [first]; exact baseCell) (by rw [first]; exact internalCell)
    (Request.local_word middle rightName right (by rw [first]; exact rightCell)) back
  rw [last,first]

theorem scalar_split_state {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table base pointer : BitVec 64} {difference : Nat}
    (data : SpliceLocals source table base 1#64 0#64 2#64 3#64 pointer difference)
    (normal : evaluateHOLFiniteState source splitChildren=(none,post)) :
    ∃ freshLeft : Bool,post=scalarChildStored source base freshLeft := by
  rw [splice_shapes.2.2.2.2.2.2.2.1] at normal
  rcases conditional_none source post _ leftFresh rightFresh normal with chosen|chosen
  · rw [leftFresh] at chosen
    exact ⟨true,scalar_child_stores_state "nl" "n" data.nodesCell data.internalCell data.leafCell data.nodeCell chosen⟩
  · rw [rightFresh] at chosen
    exact ⟨false,scalar_child_stores_state "n" "nl" data.nodesCell data.internalCell data.nodeCell data.leafCell chosen⟩

theorem scalar_after_split_state {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table base pointer : BitVec 64} {difference : Nat}
    (data : SpliceLocals source table base 1#64 0#64 2#64 3#64 pointer difference)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterSplit=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ post=emptyLocalsHOLFinite (New.putField source table 56 3#64) := by
  have safe : LocalPrefix (ofString "nodes") attach:=by
    rw [splice_shapes.2.2.2.2.2.2.2.2.2]
    exact .ite _ (.store _ _) (.ite _ (.store _ _) (.store _ _))
  rw [splice_shapes.2.2.2.2.2.2.2.2.1] at normal
  obtain ⟨middle,attached,returnedRun⟩:=sequence_returned source post attach (.return (.const 0#64)) returned (safe.summary_full source).2.1 normal
  have read : eval source (.cmp .equal (localVar "p") (.const 0#64))=some (.val (.word 1#64)):=by
    simp [eval,evalHOLExact,localVar,data.parentCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simp only [eval] at read
  rw [splice_shapes.2.2.2.2.2.2.2.2.2,evaluateHOLFiniteState_ite,read] at attached
  simp only [show (1#64 : BitVec 64)≠0 from by decide,if_neg] at attached
  have addressRead:=Scalar.plus_read source (localVar "t") table 56 (Request.local_word source "t" table data.tableCell)
  obtain ⟨mapped,stored⟩:=word_store_normal source middle _ _ _ _ addressRead (Request.local_word source "ni" 3#64 data.internalCell) attached
  obtain ⟨value,endpoint⟩:=return_normal middle post (.const 0#64) returned returnedRun
  exact ⟨Option.some.inj value.symm,by rw [endpoint,stored]; rfl⟩

/-- The complete actual scalar splice derives its selected orientation and
exact final nonlocal state, including both parents and the root store. -/
theorem scalar_splice_state {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table base pointer : BitVec 64} {difference : Nat}
    (data : SpliceLocals source table base 1#64 0#64 2#64 3#64 pointer difference)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena table 88)
    (aligned : table.toNat%8=0)
    (nodesCell : source.memory (table+40#64)=.word base)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source splice=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ ∃ freshLeft : Bool,
      LocalEffects.erase post=LocalEffects.erase (scalarSpliceStored source table base freshLeft) := by
  let start:=bind source "nodes" base
  have nodesRead:=NewNode.field_read source table base 40 domain arena aligned (by decide) (by decide) data.tableCell nodesCell
  have refreshed:=StateSteps.assign_execute source "nodes" _ base base data.nodesCell nodesRead
  change evaluateHOLFiniteState source (.assign .local (ofString "nodes") (.load .one (.op .add [localVar "t",.const 40#64])))=(none,start) at refreshed
  rw [splice_shapes.2.2.1,evaluateHOLFiniteState_seq_line780,refreshed] at normal
  change evaluateHOLFiniteState start afterRefresh=(some (.returned returned),post) at normal
  have startData : SpliceLocals start table base 1#64 0#64 2#64 3#64 pointer difference:=data.with_nodes
  rw [splice_shapes.2.2.2.1] at normal
  obtain ⟨one,firstRun,remaining⟩:=sequence_returned start post (.store (nodeFor "ni" 0) (localVar "p")) afterInternalParent returned
    ((LocalPrefix.store _ _ : LocalPrefix (ofString "nodes") _).summary_full start).2.1 normal
  have first:=scalar_node_store_state "ni" 0 (localVar "p") startData.nodesCell startData.internalCell (Request.local_word start "p" 0#64 startData.parentCell) firstRun
  have firstData : SpliceLocals one table base 1#64 0#64 2#64 3#64 pointer difference:=startData.scalar_keep (by rw [first]; rfl)
  rw [splice_shapes.2.2.2.2.1] at remaining
  obtain ⟨two,secondRun,remaining⟩:=sequence_returned one post (.store (nodeFor "nl" 0) (localVar "ni")) afterLeafParent returned
    ((LocalPrefix.store _ _ : LocalPrefix (ofString "nodes") _).summary_full one).2.1 remaining
  have second:=scalar_node_store_state "nl" 0 (localVar "ni") firstData.nodesCell firstData.leafCell (Request.local_word one "ni" 3#64 firstData.internalCell) secondRun
  have secondData : SpliceLocals two table base 1#64 0#64 2#64 3#64 pointer difference:=firstData.scalar_keep (by rw [second]; rfl)
  rw [splice_shapes.2.2.2.2.2.1] at remaining
  obtain ⟨three,thirdRun,remaining⟩:=sequence_returned two post (.store (nodeFor "n" 0) (localVar "ni")) afterOldParent returned
    ((LocalPrefix.store _ _ : LocalPrefix (ofString "nodes") _).summary_full two).2.1 remaining
  have third:=scalar_node_store_state "n" 0 (localVar "ni") secondData.nodesCell secondData.nodeCell (Request.local_word two "ni" 3#64 secondData.internalCell) thirdRun
  have thirdData : SpliceLocals three table base 1#64 0#64 2#64 3#64 pointer difference:=secondData.scalar_keep (by rw [third]; rfl)
  have safe : LocalPrefix (ofString "nodes") splitChildren:=by
    rw [splice_shapes.2.2.2.2.2.2.2.1,leftFresh,rightFresh]
    exact .ite _ (.seq (.store _ _) (.store _ _)) (.seq (.store _ _) (.store _ _))
  rw [splice_shapes.2.2.2.2.2.2.1] at remaining
  obtain ⟨children,splitRun,finish⟩:=sequence_returned three post splitChildren afterSplit returned (safe.summary_full three).2.1 remaining
  obtain ⟨freshLeft,childrenEq⟩:=scalar_split_state thirdData splitRun
  have childrenData : SpliceLocals children table base 1#64 0#64 2#64 3#64 pointer difference:=thirdData.scalar_keep (by rw [childrenEq]; rfl)
  obtain ⟨answer,postEq⟩:=scalar_after_split_state childrenData returned finish
  refine ⟨answer,freshLeft,?_⟩
  rw [postEq,childrenEq,third,second,first]
  rfl

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_node_store_state
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_child_stores_state
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_split_state
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_after_split_state
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_splice_state


namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix

def scalarForkStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap : BitVec 64) (difference : Nat) (freshLeft : Bool) :=
  scalarSpliceStored
    (NewInternal.stored (New.putField source table 64 4#64) (New.scalarNodesPointer table key cap) 3#64 (BitVec.ofNat 64 difference))
    table (New.scalarNodesPointer table key cap) freshLeft

theorem scalarSpliceStored.of_erase {source post : PanSemStateFiniteExact 64 Guest.HostMemory} (table base : BitVec 64) (freshLeft : Bool)
    (same : LocalEffects.erase source=LocalEffects.erase post) :
    LocalEffects.erase (scalarSpliceStored source table base freshLeft)=LocalEffects.erase (scalarSpliceStored post table base freshLeft) := by
  exact header_frame _ _ table 3#64 56
    (node_frame _ _ base 3#64 (if freshLeft then 1#64 else 2#64) 16
      (node_frame _ _ base 3#64 (if freshLeft then 2#64 else 1#64) 8
        (node_frame _ _ base 1#64 3#64 0 (node_frame _ _ base 2#64 3#64 0 (node_frame _ _ base 3#64 0#64 0 same)))))

end InitECandidate.Solver.Input.CurrentTable.Set

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Exact observed fork state after adding a genuine second leaf. The
previous two-leaf image is actual, and the bounded difference/orientation
and all final node/root writes are retained as a concrete memory model. -/
def ScalarForkReceipt (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap old value : BitVec 64) : Prop:=
  3≤cap.toNat ∧ ∃ previous difference freshLeft,ScalarTwoLeaves previous table key cap 1#64 old value ∧ difference≤8*key.toNat ∧
    LocalEffects.erase source=LocalEffects.erase (Set.scalarForkStored previous table key cap difference freshLeft)

theorem ScalarForkReceipt.of_erase {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap old value : BitVec 64}
    (image : ScalarForkReceipt source table key cap old value) (same : LocalEffects.erase post=LocalEffects.erase source) :
    ScalarForkReceipt post table key cap old value := by
  obtain ⟨available,previous,difference,freshLeft,leaves,bounded,actual⟩:=image
  exact ⟨available,previous,difference,freshLeft,leaves,bounded,same.trans actual⟩

end InitECandidate.Solver.Input.CurrentTable.New

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The real new-key suffix yields a genuine fork receipt from its actual
second leaf, internal-node return and complete splice. No future populated
lookup or successful allocation is assumed at its entry. -/
theorem scalar_single_fresh_fork {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer old value : BitVec 64} {difference : Nat}
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (data : ScalarSetLocals source table key pointer value) (installed : OriginalCode.Installed source.code)
    (nodesCell : source.locals.lookup (ofString "nodes")=some (.val (.word (New.scalarNodesPointer table key cap))))
    (nodeCell : source.locals.lookup (ofString "n")=some (.val (.word 1#64)))
    (parentCell : source.locals.lookup (ofString "p")=some (.val (.word 0#64)))
    (differenceCell : source.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 difference))))
    (bounded : difference≤8*key.toNat)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source newLeafCall=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ New.ScalarFrame source post table key cap ∧ New.ScalarForkReceipt post table key cap old value := by
  have ordinaryFrame:=scalar_single_fresh_frame single available data installed nodesCell nodeCell parentCell differenceCell returned normal
  obtain ⟨leafCallee,leafCalled,tLeaf,kLeaf,vLeaf⟩:=word_triple_environment source.code.lookup (ofString "htab_new_leaf")
    (ofString "t") (ofString "key") (ofString "value") NewLeaf.body .one table pointer value
    (by decide) (by decide) (by decide) (NewLeaf.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) leafArguments=
      some [.val (.word table),.val (.word pointer),.val (.word value)]:=by
    simp [leafArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.tableCell,data.keyCell,data.valueCell]
  rw [splice_shapes.1] at normal
  obtain ⟨funded,leafTarget,index,leafInner,bodyRun,checked,continued,outerEndpoint⟩:=CallNormal.scoped_normal source post "nl" .one (ofString "htab_new_leaf") leafArguments _
    NewLeaf.body newInternalCall leafCallee .one args leafCalled returned normal
  obtain ⟨indexEq,leafFrame,leaves⟩:=NewLeaf.scalar_single_two_leaves (source:=callEntryStateHOLFinite source leafCallee)
    (single.of_erase rfl) available installed tLeaf kLeaf vLeaf index bodyRun
  rw [indexEq] at continued
  let previous:=CallNormal.continuationEntry source leafTarget "nl" (.val (.word 2#64))
  have previousLeaves : New.ScalarTwoLeaves previous table key cap 1#64 old value:=leaves.of_erase rfl
  have ready : NewNode.Context previous table 3#64 cap:=⟨previousLeaves.domain,previousLeaves.geometry.table,previousLeaves.aligned,
    previousLeaves.fields (table+72#64,0#64) (by simp [New.pairHeaderWrites]),
    previousLeaves.fields (table+64#64,3#64) (by simp [New.pairHeaderWrites]),
    previousLeaves.fields (table+80#64,cap) (by simp [New.pairHeaderWrites]),available⟩
  have currentData : ScalarSetLocals previous table key pointer value:=data.resume leafTarget "nl" _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have currentDifference : previous.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 difference))):=
    (CallNormal.continuation_lookup_other source leafTarget "nl" "d" (.val (.word 2#64)) (by decide)).trans differenceCell
  have previousFields : MemoryMetadata.erase previous=MemoryMetadata.erase source:=leafFrame.fields
  have previousInstalled : OriginalCode.Installed previous.code:=by rw [MemoryMetadata.code previousFields]; exact installed
  obtain ⟨callee,called,tCell,bCell⟩:=word_pair_environment previous.code.lookup (ofString "htab_new_internal")
    (ofString "t") (ofString "bit") NewInternal.body .one table (BitVec.ofNat 64 difference) (by decide) (NewInternal.original_code previous.code previousInstalled)
  have internalArgs : evalListHOLFinite previous (h:=fun query=>Classical.propDecidable (previous.memaddrs query)) [localVar "t",localVar "d"]=
      some [.val (.word table),.val (.word (BitVec.ofNat 64 difference))]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,currentData.tableCell,currentDifference]
  rw [splice_shapes.2.1] at continued
  obtain ⟨funded,internalTarget,index,inner,internalRun,checked,spliceRun,innerEndpoint⟩:=CallNormal.scoped_normal previous leafInner "ni" .one (ofString "htab_new_internal")
    [localVar "t",localVar "d"] _ NewInternal.body splice callee .one internalArgs called returned continued
  let base:=New.scalarNodesPointer table key cap
  have baseField : previous.memory (table+40#64)=.word base:=previousLeaves.fields (table+40#64,base) (by simp [base,New.pairHeaderWrites])
  have array : AllocatedBytes.Arena base (32*(cap.toNat+1)):=by
    simpa only [base,(New.size_numbers cap single.capSmall).1] using single.geometry.nodes
  obtain ⟨internalEq,internalFunded,clock,internalScope⟩:=NewInternal.normal (callEntryStateHOLFinite previous callee) internalTarget table cap base 3#64 (BitVec.ofNat 64 difference)
    (ready.of_frame rfl) previousInstalled array single.geometry.nodesAligned tCell bCell baseField index internalRun
  obtain ⟨internalEqAgain,internalFrame,internalBase⟩:=NewInternal.scalar_frame (callEntryStateHOLFinite previous callee) internalTarget table key cap 3#64 (BitVec.ofNat 64 difference)
    (ready.of_frame rfl) single.geometry single.capSmall previousInstalled tCell bCell baseField index internalRun
  rw [internalEq] at spliceRun
  let finalEntry:=CallNormal.continuationEntry previous internalTarget "ni" (.val (.word 3#64))
  have finalFields : MemoryMetadata.erase finalEntry=MemoryMetadata.erase previous:=internalFrame.fields
  have finalDomain : finalEntry.memaddrs=InitE.ordinaryDomain:=(MemoryMetadata.domain finalFields).trans previousLeaves.domain
  have actualInternal : LocalEffects.erase finalEntry=LocalEffects.erase
      (NewInternal.stored (New.putField previous table 64 4#64) base 3#64 (BitVec.ofNat 64 difference)):=internalScope
  have locals : SpliceLocals finalEntry table base 1#64 0#64 2#64 3#64 pointer difference:=
    SpliceLocals.from_scoped source leafTarget internalTarget table base 1#64 0#64 2#64 3#64 pointer difference
      data.tableCell nodesCell nodeCell parentCell data.keyCell differenceCell
  obtain ⟨answer,freshLeft,actualSplice⟩:=scalar_splice_state locals finalDomain single.geometry.table single.aligned internalBase returned spliceRun
  have restored : LocalEffects.erase post=LocalEffects.erase inner:=by rw [outerEndpoint,innerEndpoint]; rfl
  have actual : LocalEffects.erase post=LocalEffects.erase (scalarForkStored previous table key cap difference freshLeft):=
    restored.trans (actualSplice.trans (scalarSpliceStored.of_erase table base freshLeft actualInternal))
  exact ⟨answer,ordinaryFrame.2,available,previous,difference,freshLeft,previousLeaves,bounded,actual⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalarSpliceStored.of_erase
#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarForkReceipt.of_erase
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_fresh_fork


namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack PanSemStateFiniteExact WitnessRadix
set_option maxHeartbeats 2000000

theorem ScalarSingle.with_value {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap root old : BitVec 64}
    (single : ScalarSingle source table key cap root old) (value : BitVec 64) :
    ScalarSingle (putNode source (scalarNodesPointer table key cap) 1#64 8 value) table key cap root value := by
  have inside : (1#64 : BitVec 64).toNat≤cap.toNat:=by have lower:=single.capLower; change 1≤cap.toNat; omega
  have nodes : AllocatedBytes.Arena (scalarNodesPointer table key cap) (32*(cap.toNat+1)):=by
    simpa only [(size_numbers cap single.capSmall).1] using single.geometry.nodes
  have different (offset : Nat) (small : offset<32) (notValue : offset≠8) :
      FindLeaf.cell (scalarNodesPointer table key cap) 1#64 offset≠FindLeaf.cell (scalarNodesPointer table key cap) 1#64 8:=by
    intro same
    exact notValue (cell_injective _ _ _ cap offset 8 nodes inside inside small (by decide) same).2
  have orderAway : scalarOrderPointer table key cap≠FindLeaf.cell (scalarNodesPointer table key cap) 1#64 8:=by
    simpa only [slot,BitVec.zero_mul,BitVec.add_zero] using
      Ne.symm (single.geometry.node_order_away single.capSmall 1#64 0#64 inside (by change 0≤cap.toNat; omega) 8 (by decide))
  refine {single with
    fields:=?_,leafZero:=?_,leafValue:=?_,leafPosition:=?_,leafMarker:=?_,orderFirst:=?_}
  · intro entry member
    have address : ∃ offset : Nat,offset<88 ∧ entry.1=table+BitVec.ofNat 64 offset:=by
      simp only [singleHeaderWrites,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals exact ⟨_,by decide,rfl⟩
    obtain ⟨offset,small,address⟩:=address
    have away : entry.1≠FindLeaf.cell (scalarNodesPointer table key cap) 1#64 8:=by
      rw [address]
      exact single.geometry.scalar_header_away single.capSmall 1#64 inside 8 offset (by decide) small
    exact (if_neg away).trans (single.fields entry member)
  · exact (if_neg (different 0 (by decide) (by decide))).trans single.leafZero
  · exact if_pos rfl
  · exact (if_neg (different 16 (by decide) (by decide))).trans single.leafPosition
  · exact (if_neg (different 24 (by decide) (by decide))).trans single.leafMarker
  · exact (if_neg orderAway).trans single.orderFirst

/-- The complete observed scalar setter result: either its real existing
leaf was updated, or its second leaf/internal-node/splice yielded a fork. -/
def ScalarSetResult (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap old value : BitVec 64) : Prop:=
  ScalarSingle source table key cap 1#64 value ∨ ScalarForkReceipt source table key cap old value

theorem ScalarSetResult.of_erase {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap old value : BitVec 64}
    (result : ScalarSetResult source table key cap old value) (same : LocalEffects.erase post=LocalEffects.erase source) :
    ScalarSetResult post table key cap old value :=
  result.elim (fun single=>Or.inl (single.of_erase same)) (fun fork=>Or.inr (fork.of_erase same))

end InitECandidate.Solver.Input.CurrentTable.New

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem scalar_single_after_difference_result {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer old value : BitVec 64} {difference : Nat}
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (data : ScalarSetLocals source table key pointer value) (installed : OriginalCode.Installed source.code)
    (bounded : difference≤8*key.toNat)
    (differenceCell : source.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 difference))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterDifference=(some (.returned returned),post)) :
    New.ScalarSetResult post table key cap old value := by
  let base:=New.scalarNodesPointer table key cap
  have nodesRead:=NewNode.field_read source table base 40 single.domain single.geometry.table single.aligned (by decide) (by decide) data.tableCell
    (single.fields (table+40#64,base) (by simp [base,New.singleHeaderWrites]))
  rw [scalar_difference_shapes.1] at normal
  obtain ⟨nodesInner,continued,nodesEndpoint⟩:=ScalarScope.declare_trace source post "nodes" _ base afterNodes (some (.returned returned)) nodesRead normal
  let first:=bind source "nodes" base
  have firstData : ScalarSetLocals first table key pointer value:=data.with_local "nodes" base (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [scalar_difference_shapes.2.1] at continued
  obtain ⟨parentInner,continued,parentEndpoint⟩:=ScalarScope.declare_trace first nodesInner "p" (.const 0#64) 0#64 afterParent (some (.returned returned)) rfl continued
  let second:=bind first "p" 0#64
  have secondData : ScalarSetLocals second table key pointer value:=firstData.with_local "p" 0#64 (by decide) (by decide) (by decide) (by decide) (by decide)
  have rootRead:=NewNode.field_read second table 1#64 56 single.domain single.geometry.table single.aligned (by decide) (by decide) secondData.tableCell
    (single.fields (table+56#64,1#64) (by simp [New.singleHeaderWrites]))
  rw [scalar_difference_shapes.2.2] at continued
  obtain ⟨nodeInner,continued,nodeEndpoint⟩:=ScalarScope.declare_trace second parentInner "n" _ 1#64 afterNode (some (.returned returned)) rootRead continued
  let entry:=bind second "n" 1#64
  have entryData : ScalarSetLocals entry table key pointer value:=secondData.with_local "n" 1#64 (by decide) (by decide) (by decide) (by decide) (by decide)
  have entryDifference : entry.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 difference))):=by
    simpa [entry,second,first,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using differenceCell
  have baseCell : entry.locals.lookup (ofString "nodes")=some (.val (.word base)):=
    (bind_lookup_other second "n" "nodes" 1#64 (by decide)).trans
      ((bind_lookup_other first "p" "nodes" 0#64 (by decide)).trans (bind_lookup_same _ _ _))
  have nodeCell : entry.locals.lookup (ofString "n")=some (.val (.word 1#64)):=bind_lookup_same _ _ _
  have parentCell : entry.locals.lookup (ofString "p")=some (.val (.word 0#64)):=
    (bind_lookup_other second "n" "p" 1#64 (by decide)).trans (bind_lookup_same _ _ _)
  have inside : (1#64 : BitVec 64).toNat≤cap.toNat:=by change 1≤cap.toNat; omega
  have array : AllocatedBytes.Arena base (32*(cap.toNat+1)):=by
    simpa only [base,(New.size_numbers cap single.capSmall).1] using single.geometry.nodes
  have mapped : entry.memaddrs (FindLeaf.cell base 1#64 24):=
    AllocatedBytes.word_mapped entry (slot base 1#64 32) 32 24 single.domain (slot_arena base 1#64 cap 32 array inside) (by decide)
      (slot_aligned base 1#64 cap 32 array inside single.geometry.nodesAligned (by decide)) (by decide)
  have markerNumber : (key*8#64).toNat=8*key.toNat:=by
    rw [BitVec.toNat_mul]
    change key.toNat*8%18446744073709551616=8*key.toNat
    rw [Nat.mod_eq_of_lt (by have small:=single.keySmall; omega)]
    omega
  have differenceNumber : (BitVec.ofNat 64 difference).toNat=difference:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have small:=single.keySmall; omega)]
  have loopRun:=scalar_seek_loop entry base (key*8#64) (BitVec.ofNat 64 difference) (by rw [markerNumber,differenceNumber]; exact bounded)
    baseCell nodeCell entryDifference mapped single.leafMarker
  have never : ∀ value,(evaluateHOLFiniteState entry seek).1≠some (.returned value):=by
    intro value
    by_cases zero : entry.clock=0 <;> simp [loopRun,zero]
  rw [seek_shapes.1] at continued
  obtain ⟨target,seekRun,tail⟩:=sequence_returned entry nodeInner seek newLeafCall returned never continued
  by_cases zero : entry.clock=0
  · rw [loopRun,if_pos zero] at seekRun
    cases seekRun
  · rw [loopRun,if_neg zero] at seekRun
    have targetEq : target=decClockHOLFinite entry:=(congrArg Prod.snd seekRun).symm
    subst target
    have tickData : ScalarSetLocals (decClockHOLFinite entry) table key pointer value:=
      ⟨entryData.tableCell,entryData.keyCell,entryData.valueCell,entryData.lengthCell,entryData.strideCell⟩
    obtain ⟨answer,frame,fork⟩:=scalar_single_fresh_fork (source:=decClockHOLFinite entry) (single.of_erase rfl) available tickData installed
      baseCell nodeCell parentCell entryDifference bounded returned tail
    have scope : LocalEffects.erase post=LocalEffects.erase nodeInner:=by rw [nodesEndpoint,parentEndpoint,nodeEndpoint]; rfl
    exact Or.inr (fork.of_erase scope)

theorem scalar_single_difference_result {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer old value : BitVec 64}
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (data : ScalarSetLocals source table key pointer value) (installed : OriginalCode.Installed source.code)
    (keysCell : source.locals.lookup (ofString "keys")=some (.val (.word (New.keysPointer table))))
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word 1#64)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source differenceCall=(some (.returned returned),post)) :
    New.ScalarSetResult post table key cap old value := by
  rw [entry_shapes.2.2.2.2.2.2] at normal
  let arguments : List (ExpHOL 64):=[localVar "key",.op .add [localVar "keys",.panop .mul [localVar "leaf",localVar "stride"]],localVar "klen"]
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word pointer),.val (.word (New.keysPointer table+New.strideWord key)),.val (.word (BitVec.ofNat 64 key.toNat))]:=by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.keyCell,data.lengthCell,data.strideCell,keysCell,leafCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  rcases FirstDiff.scoped_scalar_trace source post pointer (New.keysPointer table+New.strideWord key) key.toNat single.keySmall installed
    "d" arguments afterDifference args (some (.returned returned)) normal with stopped|reached
  · exact (stopped.2 returned rfl).elim
  · obtain ⟨target,inner,position,bounded,physical,forward,price,continued,endpoint⟩:=reached
    let current:=CallNormal.continuationEntry source target "d" (.val (.word (BitVec.ofNat 64 position)))
    have currentData : ScalarSetLocals current table key pointer value:=data.resume target "d" _ (by decide) (by decide) (by decide) (by decide) (by decide)
    have currentInstalled : OriginalCode.Installed current.code:=by rw [LocalEffects.code_of_erase source current physical]; exact installed
    have result:=scalar_single_after_difference_result (source:=current) (single.of_erase physical) available currentData currentInstalled bounded
      (CallNormal.continuation_lookup_same source target "d" _) returned continued
    exact result.of_erase (by rw [endpoint]; rfl)

theorem scalar_single_after_compare_result {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer old value : BitVec 64}
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (data : ScalarSetLocals source table key pointer value) (installed : OriginalCode.Installed source.code)
    (keysCell : source.locals.lookup (ofString "keys")=some (.val (.word (New.keysPointer table))))
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word 1#64)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterCompare=(some (.returned returned),post)) :
    New.ScalarSetResult post table key cap old value := by
  have updateRun:=scalar_single_update_execute source table key cap pointer old value single data leafCell
  rw [entry_shapes.2.2.2.2.2.1,guard_shapes.2.2.2.1,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite] at normal
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact (fun query=>Classical.propDecidable (source.memaddrs query))
    (.cmp .notEqual (localVar "eq") (.const 0#64))=read at normal
  cases read with
  | none=>cases normal
  | some read=>
    cases read with
    | rStruct fields=>cases normal
    | nStruct name fields=>cases normal
    | val payload=>
      cases payload with
      | word word=>
        simp only at normal
        by_cases zero : word=0
        · rw [if_pos zero,evaluateHOLFiniteState_skip] at normal
          exact scalar_single_difference_result single available data installed keysCell leafCell returned normal
        · rw [if_neg zero,updateRun] at normal
          have answer : returned=.val (.word 0#64):=by
            simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using (congrArg Prod.fst normal).symm
          have endpoint : post=emptyLocalsHOLFinite (putNode source (New.scalarNodesPointer table key cap) 1#64 8 value):=(congrArg Prod.snd normal).symm
          exact Or.inl ((single.with_value value).of_erase (by rw [endpoint]; rfl))

theorem scalar_single_compare_result {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer old value : BitVec 64}
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (data : ScalarSetLocals source table key pointer value) (installed : OriginalCode.Installed source.code)
    (keysCell : source.locals.lookup (ofString "keys")=some (.val (.word (New.keysPointer table))))
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word 1#64)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source compareCall=(some (.returned returned),post)) :
    New.ScalarSetResult post table key cap old value := by
  rw [guard_shapes.2.2.2.2.2] at normal
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) compareArguments=
      some [.val (.word (New.keysPointer table+New.strideWord key)),.val (.word pointer),.val (.word (BitVec.ofNat 64 key.toNat))]:=by
    simp [compareArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.keyCell,data.lengthCell,data.strideCell,keysCell,leafCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  obtain ⟨callee,called,aCell,bCell,nCell⟩:=MutableTable.MemeqByteRuntime.environment source.code.lookup (New.keysPointer table+New.strideWord key) pointer key.toNat
    (MutableTable.MemeqAny.original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨funded,target,result,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_normal source post "eq" .one (ofString "memeq")
    compareArguments _ Memeq32.body afterCompare callee .one args called returned normal
  let current:=CallNormal.continuationEntry source target "eq" result
  have physical:=MutableTable.MemeqAny.readonly source.code entry rfl
  rw [bodyRun] at physical
  have currentData : ScalarSetLocals current table key pointer value:=data.resume target "eq" result (by decide) (by decide) (by decide) (by decide) (by decide)
  have currentKeys : current.locals.lookup (ofString "keys")=some (.val (.word (New.keysPointer table))):=
    (CallNormal.continuation_lookup_other source target "eq" "keys" result (by decide)).trans keysCell
  have currentLeaf : current.locals.lookup (ofString "leaf")=some (.val (.word 1#64)):=
    (CallNormal.continuation_lookup_other source target "eq" "leaf" result (by decide)).trans leafCell
  have currentInstalled : OriginalCode.Installed current.code:=by rw [LocalEffects.code_of_erase source current physical]; exact installed
  have result:=scalar_single_after_compare_result (source:=current) (single.of_erase physical) available currentData currentInstalled currentKeys currentLeaf returned continued
  exact result.of_erase (by rw [endpoint]; rfl)

theorem scalar_single_after_leaf_result {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer old value : BitVec 64}
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (data : ScalarSetLocals source table key pointer value) (installed : OriginalCode.Installed source.code)
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word 1#64)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterLeaf=(some (.returned returned),post)) :
    New.ScalarSetResult post table key cap old value := by
  have keysRead:=NewNode.field_read source table (New.keysPointer table) 32 single.domain single.geometry.table single.aligned (by decide) (by decide) data.tableCell
    (single.fields (table+32#64,New.keysPointer table) (by simp [New.singleHeaderWrites]))
  rw [entry_shapes.2.2.2.1] at normal
  obtain ⟨inner,continued,endpoint⟩:=ScalarScope.declare_trace source post "keys" _ (New.keysPointer table) afterKeys (some (.returned returned)) keysRead normal
  let current:=bind source "keys" (New.keysPointer table)
  have currentData : ScalarSetLocals current table key pointer value:=data.with_local "keys" (New.keysPointer table) (by decide) (by decide) (by decide) (by decide) (by decide)
  have currentLeaf : current.locals.lookup (ofString "leaf")=some (.val (.word 1#64)):=
    (bind_lookup_other source "keys" "leaf" (New.keysPointer table) (by decide)).trans leafCell
  rw [scalar_single_after_keys current currentLeaf] at continued
  have result:=scalar_single_compare_result (source:=current) (single.of_erase rfl) available currentData installed (bind_lookup_same _ _ _) currentLeaf returned continued
  exact result.of_erase (by rw [endpoint]; rfl)

theorem scalar_single_after_stride_result {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer old value : BitVec 64}
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (data : ScalarSetLocals source table key pointer value) (installed : OriginalCode.Installed source.code)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterStride=(some (.returned returned),post)) :
    New.ScalarSetResult post table key cap old value := by
  rw [entry_shapes.2.2.1] at normal
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "t",localVar "key"]=
      some [.val (.word table),.val (.word pointer)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.tableCell,data.keyCell]
  rcases FindLeaf.scoped_scalar_single_trace source post table key cap old pointer single installed "leaf" [localVar "t",localVar "key"] afterLeaf args (some (.returned returned)) normal with stopped|reached
  · exact (stopped.2 returned rfl).elim
  · obtain ⟨target,inner,physical,forward,price,continued,endpoint⟩:=reached
    let current:=CallNormal.continuationEntry source target "leaf" (.val (.word 1#64))
    have currentData : ScalarSetLocals current table key pointer value:=data.resume target "leaf" _ (by decide) (by decide) (by decide) (by decide) (by decide)
    have currentInstalled : OriginalCode.Installed current.code:=by rw [LocalEffects.code_of_erase source current physical]; exact installed
    have result:=scalar_single_after_leaf_result (source:=current) (single.of_erase physical) available currentData currentInstalled
      (CallNormal.continuation_lookup_same source target "leaf" _) returned continued
    exact result.of_erase (by rw [endpoint]; rfl)

theorem scalar_single_result {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer old value : BitVec 64}
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    New.ScalarSetResult post table key cap old value := by
  have lengthRead:=NewNode.field_read source table key 0 single.domain single.geometry.table single.aligned (by decide) (by decide) tableCell
    (single.fields (table+0#64,key) (by simp [New.singleHeaderWrites]))
  rw [entry_shapes.1] at normal
  obtain ⟨middle,continued,endpoint⟩:=ScalarScope.declare_trace source post "klen" _ key afterLength (some (.returned returned)) lengthRead normal
  let first:=bind source "klen" key
  have firstTable : first.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other source "klen" "t" key (by decide)).trans tableCell
  have strideRead:=NewNode.field_read first table (New.strideWord key) 8 single.domain single.geometry.table single.aligned (by decide) (by decide) firstTable
    (single.fields (table+8#64,New.strideWord key) (by simp [New.singleHeaderWrites]))
  rw [entry_shapes.2.1] at continued
  obtain ⟨inner,remaining,innerEndpoint⟩:=ScalarScope.declare_trace first middle "stride" _ (New.strideWord key) afterStride (some (.returned returned)) strideRead continued
  let current:=bind first "stride" (New.strideWord key)
  have kept (name : String) (notStride : ofString "stride"≠ofString name) (notLength : ofString "klen"≠ofString name) :
      current.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    (bind_lookup_other first "stride" name (New.strideWord key) notStride).trans (bind_lookup_other source "klen" name key notLength)
  have data : ScalarSetLocals current table key pointer value:=
    ⟨(kept "t" (by decide) (by decide)).trans tableCell,(kept "key" (by decide) (by decide)).trans keyCell,
      (kept "value" (by decide) (by decide)).trans valueCell,
      (bind_lookup_other first "stride" "klen" (New.strideWord key) (by decide)).trans (bind_lookup_same _ _ _),bind_lookup_same _ _ _⟩
  have result:=scalar_single_after_stride_result (source:=current) (single.of_erase rfl) available data installed returned remaining
  exact result.of_erase (by rw [endpoint,innerEndpoint]; rfl)

/-- The complete actual ignored setter caller retains its observed
update-or-fork state together with the existing external memory frame. -/
theorem scalar_single_call_result {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap pointer old value : BitVec 64}
    (single : New.ScalarSingle source table key cap 1#64 old) (available : 3≤cap.toNat)
    (installed : OriginalCode.Installed source.code) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word table),.val (.word pointer),.val (.word value)])
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htab_set") arguments)=(none,post)) :
    New.ScalarFrame source post table key cap ∧ post.locals=source.locals ∧ New.ScalarSetResult post table key cap old value := by
  obtain ⟨frame,locals⟩:=scalar_single_call_frame single available installed arguments args normal
  obtain ⟨callee,called,tCell,kCell,vCell⟩:=word_triple_environment source.code.lookup (ofString "htab_set")
    (ofString "t") (ofString "key") (ofString "value") body .one table pointer value
    (by decide) (by decide) (by decide) (original_code source.code installed)
  obtain ⟨funded,values,actual,actualCallee,shape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩:=CallNormal.ignored_data source post (ofString "htab_set") arguments normal
  have sameValues : values=[.val (.word table),.val (.word pointer),.val (.word value)]:=Option.some.inj (actualArgs.symm.trans args)
  subst values
  have same : (actual,actualCallee,shape)=(body,callee,.one):=Option.some.inj (actualCalled.symm.trans called)
  cases same
  have result:=scalar_single_result (source:=callEntryStateHOLFinite source callee) (single.of_erase rfl) available installed tCell kCell vCell returned bodyRun
  exact ⟨frame,locals,result.of_erase (by rw [endpoint]; rfl)⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarSingle.with_value
#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarSetResult.of_erase

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_after_difference_result
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_difference_result
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_after_compare_result
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_compare_result
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_after_leaf_result
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_after_stride_result
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_result
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_single_call_result

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The actual node allocation/splice writes preserve the header except
for the genuine next-index and root stores. -/
theorem scalarForkStored.header_eq (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table key cap : BitVec 64) (difference : Nat) (freshLeft : Bool)
    (geometry : New.ScalarGeometry table key cap) (capSmall : cap.toNat ≤ 2^32)
    (available : 3 ≤ cap.toNat) (field : Nat) (small : field < 88) :
    (scalarForkStored source table key cap difference freshLeft).memory (table + BitVec.ofNat 64 field) =
      (New.putField (New.putField source table 64 4#64) table 56 3#64).memory (table + BitVec.ofNat 64 field) := by
  have away1 (offset : Nat) (inside : offset < 32) :=
    geometry.scalar_header_away capSmall 1#64 (by change 1 ≤ cap.toNat; omega) offset field inside small
  have away2 (offset : Nat) (inside : offset < 32) :=
    geometry.scalar_header_away capSmall 2#64 (by change 2 ≤ cap.toNat; omega) offset field inside small
  have away3 (offset : Nat) (inside : offset < 32) :=
    geometry.scalar_header_away capSmall 3#64 (by change 3 ≤ cap.toNat; omega) offset field inside small
  simp only [scalarForkStored, scalarSpliceStored, scalarChildStored, NewInternal.stored,
    New.putField, putNode, StoreWord.put,
    if_neg (away1 0 (by decide)), if_neg (away2 0 (by decide)),
    if_neg (away3 0 (by decide)), if_neg (away3 8 (by decide)),
    if_neg (away3 16 (by decide)), if_neg (away3 24 (by decide))]

/-- The real fork preserves both old leaf markers. Parent stores and the
fresh internal node are proved disjoint from those actual cells. -/
theorem scalarForkStored.leaf_marker (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table key cap : BitVec 64) (difference : Nat) (freshLeft : Bool)
    (geometry : New.ScalarGeometry table key cap) (capSmall : cap.toNat ≤ 2^32)
    (available : 3 ≤ cap.toNat) (node : BitVec 64) (leaf : node = 1#64 ∨ node = 2#64) :
    (scalarForkStored source table key cap difference freshLeft).memory (FindLeaf.cell (New.scalarNodesPointer table key cap) node 24) =
      source.memory (FindLeaf.cell (New.scalarNodesPointer table key cap) node 24) := by
  have array : AllocatedBytes.Arena (New.scalarNodesPointer table key cap) (32 * (cap.toNat + 1)) := by
    simpa only [(New.size_numbers cap capSmall).1] using geometry.nodes
  have inside : node.toNat ≤ cap.toNat := by
    rcases leaf with rfl | rfl
    · change 1 ≤ cap.toNat
      omega
    · change 2 ≤ cap.toNat
      omega
  have notThree : node ≠ 3#64 := by rcases leaf with rfl | rfl <;> decide
  have headerAway (field : Nat) (small : field < 88) :=
    Ne.symm (geometry.scalar_header_away capSmall node inside 24 field (by decide) small)
  have away3 (offset : Nat) (small : offset < 32) :
      FindLeaf.cell (New.scalarNodesPointer table key cap) node 24 ≠ FindLeaf.cell (New.scalarNodesPointer table key cap) 3#64 offset := by
    intro same
    exact notThree (cell_injective _ _ _ cap 24 offset array inside (by change 3 ≤ cap.toNat; omega) (by decide) small same).1
  have awayZero (other : BitVec 64) (otherInside : other.toNat ≤ cap.toNat) :
      FindLeaf.cell (New.scalarNodesPointer table key cap) node 24 ≠ FindLeaf.cell (New.scalarNodesPointer table key cap) other 0 := by
    intro same
    have impossible := (cell_injective _ _ _ cap 24 0 array inside otherInside (by decide) (by decide) same).2
    omega
  simp only [scalarForkStored, scalarSpliceStored, scalarChildStored, NewInternal.stored,
    New.putField, putNode, StoreWord.put,
    if_neg (headerAway 56 (by decide)), if_neg (headerAway 64 (by decide)),
    if_neg (awayZero 1#64 (by change 1 ≤ cap.toNat; omega)), if_neg (awayZero 2#64 (by change 2 ≤ cap.toNat; omega)),
    if_neg (away3 0 (by decide)), if_neg (away3 8 (by decide)),
    if_neg (away3 16 (by decide)), if_neg (away3 24 (by decide))]

/-- The actual allocated internal node retains the observed difference and
its actual orientation's two in-range child indices. -/
theorem scalarForkStored.internal_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table key cap : BitVec 64) (difference : Nat) (freshLeft : Bool)
    (geometry : New.ScalarGeometry table key cap) (capSmall : cap.toNat ≤ 2^32)
    (available : 3 ≤ cap.toNat) :
    (scalarForkStored source table key cap difference freshLeft).memory (FindLeaf.cell (New.scalarNodesPointer table key cap) 3#64 24) = .word (BitVec.ofNat 64 difference) ∧
    (scalarForkStored source table key cap difference freshLeft).memory (FindLeaf.cell (New.scalarNodesPointer table key cap) 3#64 8) = .word (if freshLeft then 2#64 else 1#64) ∧
    (scalarForkStored source table key cap difference freshLeft).memory (FindLeaf.cell (New.scalarNodesPointer table key cap) 3#64 16) = .word (if freshLeft then 1#64 else 2#64) := by
  have array : AllocatedBytes.Arena (New.scalarNodesPointer table key cap) (32 * (cap.toNat + 1)) := by
    simpa only [(New.size_numbers cap capSmall).1] using geometry.nodes
  have inside : (3#64 : BitVec 64).toNat ≤ cap.toNat := by change 3 ≤ cap.toNat; omega
  have headerAway (offset field : Nat) (small : offset < 32) (fieldSmall : field < 88) :=
    Ne.symm (geometry.scalar_header_away capSmall 3#64 inside offset field small fieldSmall)
  have away1 (offset : Nat) (small : offset < 32) :
      FindLeaf.cell (New.scalarNodesPointer table key cap) 3#64 offset ≠ FindLeaf.cell (New.scalarNodesPointer table key cap) 1#64 0 := by
    intro same
    have impossible := (cell_injective _ _ _ cap offset 0 array inside (by change 1 ≤ cap.toNat; omega) small (by decide) same).1
    exact (by decide : (3#64 : BitVec 64) ≠ 1#64) impossible
  have away2 (offset : Nat) (small : offset < 32) :
      FindLeaf.cell (New.scalarNodesPointer table key cap) 3#64 offset ≠ FindLeaf.cell (New.scalarNodesPointer table key cap) 2#64 0 := by
    intro same
    have impossible := (cell_injective _ _ _ cap offset 0 array inside (by change 2 ≤ cap.toNat; omega) small (by decide) same).1
    exact (by decide : (3#64 : BitVec 64) ≠ 2#64) impossible
  have different (offset field : Nat) (small : offset < 32) (fieldSmall : field < 32) (ne : offset ≠ field) :
      FindLeaf.cell (New.scalarNodesPointer table key cap) 3#64 offset ≠ FindLeaf.cell (New.scalarNodesPointer table key cap) 3#64 field := by
    intro same
    exact ne (cell_injective _ _ _ cap offset field array inside inside small fieldSmall same).2
  repeat' constructor
  all_goals simp [scalarForkStored, scalarSpliceStored, scalarChildStored, NewInternal.stored,
    New.putField, putNode, StoreWord.put, headerAway, away1, away2, different]

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalarForkStored.header_eq
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalarForkStored.leaf_marker
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalarForkStored.internal_fields

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Physical facts extracted from the real second insertion, independent
of the earlier memory snapshot. These cells can survive unrelated writes. -/
structure ScalarForkImage (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table key cap : BitVec 64) (difference : Nat) (freshLeft : Bool) : Prop where
  geometry : ScalarGeometry table key cap
  aligned : table.toNat % 8 = 0
  domain : source.memaddrs = InitE.ordinaryDomain
  available : 3 ≤ cap.toNat
  keySmall : key.toNat ≤ 60
  capSmall : cap.toNat ≤ 2^32
  bounded : difference ≤ 8 * key.toNat
  fields : ∀ entry ∈ pairHeaderWrites table key cap 3#64 4#64, source.memory entry.1 = .word entry.2
  oldMarker : source.memory (FindLeaf.cell (scalarNodesPointer table key cap) 1#64 24) = .word (key * 8#64)
  freshMarker : source.memory (FindLeaf.cell (scalarNodesPointer table key cap) 2#64 24) = .word (key * 8#64)
  internalBit : source.memory (FindLeaf.cell (scalarNodesPointer table key cap) 3#64 24) = .word (BitVec.ofNat 64 difference)
  leftChild : source.memory (FindLeaf.cell (scalarNodesPointer table key cap) 3#64 8) = .word (if freshLeft then 2#64 else 1#64)
  rightChild : source.memory (FindLeaf.cell (scalarNodesPointer table key cap) 3#64 16) = .word (if freshLeft then 1#64 else 2#64)

def forkCells (table key cap : BitVec 64) : List (BitVec 64) :=
  [FindLeaf.cell (scalarNodesPointer table key cap) 1#64 24,
   FindLeaf.cell (scalarNodesPointer table key cap) 2#64 24,
   FindLeaf.cell (scalarNodesPointer table key cap) 3#64 24,
   FindLeaf.cell (scalarNodesPointer table key cap) 3#64 8,
   FindLeaf.cell (scalarNodesPointer table key cap) 3#64 16]

theorem ScalarForkImage.of_memory {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table key cap : BitVec 64} {difference : Nat} {freshLeft : Bool}
    (image : ScalarForkImage source table key cap difference freshLeft)
    (domain : target.memaddrs = source.memaddrs)
    (header : ∀ entry ∈ pairHeaderWrites table key cap 3#64 4#64, target.memory entry.1 = source.memory entry.1)
    (nodes : ∀ query ∈ forkCells table key cap, target.memory query = source.memory query) :
    ScalarForkImage target table key cap difference freshLeft := by
  exact {image with
    domain := domain.trans image.domain,
    fields := by intro entry member; exact (header entry member).trans (image.fields entry member),
    oldMarker := (nodes _ (by simp [forkCells])).trans image.oldMarker,
    freshMarker := (nodes _ (by simp [forkCells])).trans image.freshMarker,
    internalBit := (nodes _ (by simp [forkCells])).trans image.internalBit,
    leftChild := (nodes _ (by simp [forkCells])).trans image.leftChild,
    rightChild := (nodes _ (by simp [forkCells])).trans image.rightChild}

theorem ScalarForkImage.of_erase {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table key cap : BitVec 64} {difference : Nat} {freshLeft : Bool}
    (image : ScalarForkImage source table key cap difference freshLeft)
    (same : LocalEffects.erase target = LocalEffects.erase source) :
    ScalarForkImage target table key cap difference freshLeft := by
  have domain := congrArg PanSemStateFiniteExact.memaddrs same
  change target.memaddrs = source.memaddrs at domain
  have memory := LocalEffects.memory_of_erase source target same
  exact image.of_memory domain (by intro entry member; exact congrFun memory _) (by intro query member; exact congrFun memory _)

end InitECandidate.Solver.Input.CurrentTable.New

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- All eleven actual header words after the observed internal allocation
and splice are extracted from the earlier genuine two-leaf image. -/
theorem scalarForkStored.pair_header {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table key cap old value : BitVec 64} (difference : Nat) (freshLeft : Bool)
    (leaves : New.ScalarTwoLeaves source table key cap 1#64 old value) (available : 3 ≤ cap.toNat) :
    ∀ entry ∈ New.pairHeaderWrites table key cap 3#64 4#64,
      (scalarForkStored source table key cap difference freshLeft).memory entry.1 = .word entry.2 := by
  intro entry member
  simp only [New.pairHeaderWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [scalarForkStored.header_eq source table key cap difference freshLeft leaves.geometry leaves.capSmall available 0 (by decide)]
    have prior := leaves.fields (table + 0#64, key) (by simp [New.pairHeaderWrites])
    simpa [New.putField, StoreWord.put] using prior
  · rw [scalarForkStored.header_eq source table key cap difference freshLeft leaves.geometry leaves.capSmall available 8 (by decide)]
    have prior := leaves.fields (table + 8#64, New.strideWord key) (by simp [New.pairHeaderWrites])
    simpa [New.putField, StoreWord.put] using prior
  · rw [scalarForkStored.header_eq source table key cap difference freshLeft leaves.geometry leaves.capSmall available 16 (by decide)]
    have prior := leaves.fields (table + 16#64, cap) (by simp [New.pairHeaderWrites])
    simpa [New.putField, StoreWord.put] using prior
  · rw [scalarForkStored.header_eq source table key cap difference freshLeft leaves.geometry leaves.capSmall available 24 (by decide)]
    have prior := leaves.fields (table + 24#64, 2#64) (by simp [New.pairHeaderWrites])
    simpa [New.putField, StoreWord.put] using prior
  · rw [scalarForkStored.header_eq source table key cap difference freshLeft leaves.geometry leaves.capSmall available 32 (by decide)]
    have prior := leaves.fields (table + 32#64, New.keysPointer table) (by simp [New.pairHeaderWrites])
    simpa [New.putField, StoreWord.put] using prior
  · rw [scalarForkStored.header_eq source table key cap difference freshLeft leaves.geometry leaves.capSmall available 40 (by decide)]
    have prior := leaves.fields (table + 40#64, New.scalarNodesPointer table key cap) (by simp [New.pairHeaderWrites])
    simpa [New.putField, StoreWord.put] using prior
  · rw [scalarForkStored.header_eq source table key cap difference freshLeft leaves.geometry leaves.capSmall available 48 (by decide)]
    have prior := leaves.fields (table + 48#64, New.scalarOrderPointer table key cap) (by simp [New.pairHeaderWrites])
    simpa [New.putField, StoreWord.put] using prior
  · rw [scalarForkStored.header_eq source table key cap difference freshLeft leaves.geometry leaves.capSmall available 56 (by decide)]
    simp [New.putField, StoreWord.put]
  · rw [scalarForkStored.header_eq source table key cap difference freshLeft leaves.geometry leaves.capSmall available 64 (by decide)]
    simp [New.putField, StoreWord.put]
  · rw [scalarForkStored.header_eq source table key cap difference freshLeft leaves.geometry leaves.capSmall available 72 (by decide)]
    have prior := leaves.fields (table + 72#64, 0#64) (by simp [New.pairHeaderWrites])
    simpa [New.putField, StoreWord.put] using prior
  · rw [scalarForkStored.header_eq source table key cap difference freshLeft leaves.geometry leaves.capSmall available 80 (by decide)]
    have prior := leaves.fields (table + 80#64, cap) (by simp [New.pairHeaderWrites])
    simpa [New.putField, StoreWord.put] using prior

end InitECandidate.Solver.Input.CurrentTable.Set

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- The real historical receipt now yields portable actual header/node
cells, including the real allocation capacity retained by its producer. -/
theorem ScalarForkReceipt.image {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table key cap old value : BitVec 64} (receipt : ScalarForkReceipt source table key cap old value) :
    ∃ difference freshLeft, ScalarForkImage source table key cap difference freshLeft := by
  obtain ⟨available, previous, difference, freshLeft, leaves, bounded, actual⟩ := receipt
  have internal := Set.scalarForkStored.internal_fields previous table key cap difference freshLeft leaves.geometry leaves.capSmall available
  have memory := LocalEffects.memory_of_erase (Set.scalarForkStored previous table key cap difference freshLeft) source actual
  have domain : source.memaddrs = previous.memaddrs := by
    have sameDomain := MemoryMetadata.domain (MemoryMetadata.of_frame actual)
    simpa only [Set.scalarForkStored, Set.scalarSpliceStored, Set.scalarChildStored,
      NewInternal.stored, New.putField, putNode] using sameDomain
  refine ⟨difference, freshLeft, leaves.geometry, leaves.aligned, domain.trans leaves.domain,
    available, leaves.keySmall, leaves.capSmall, bounded, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro entry member
    rw [memory]
    exact Set.scalarForkStored.pair_header difference freshLeft leaves available entry member
  · rw [memory]
    exact (Set.scalarForkStored.leaf_marker previous table key cap difference freshLeft leaves.geometry leaves.capSmall available 1#64 (Or.inl rfl)).trans leaves.oldMarker
  · rw [memory]
    exact (Set.scalarForkStored.leaf_marker previous table key cap difference freshLeft leaves.geometry leaves.capSmall available 2#64 (Or.inr rfl)).trans leaves.freshMarker
  · rw [memory]
    exact internal.1
  · rw [memory]
    exact internal.2.1
  · rw [memory]
    exact internal.2.2

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarForkImage.of_memory
#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarForkImage.of_erase
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalarForkStored.pair_header
#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarForkReceipt.image

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack PanSemStateFiniteExact WitnessRadix
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Map an actual allocated scalar node cell at the retained current domain. -/
theorem ScalarGeometry.node_mapped {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table key cap : BitVec 64} (geometry : ScalarGeometry table key cap)
    (domain : source.memaddrs = InitE.ordinaryDomain) (capSmall : cap.toNat ≤ 2^32)
    (node : BitVec 64) (inside : node.toNat ≤ cap.toNat) (offset : Nat)
    (small : offset < 32) (aligned : offset % 8 = 0) :
    source.memaddrs (FindLeaf.cell (scalarNodesPointer table key cap) node offset) := by
  have array : AllocatedBytes.Arena (scalarNodesPointer table key cap) (32 * (cap.toNat + 1)) := by
    simpa only [(size_numbers cap capSmall).1] using geometry.nodes
  exact AllocatedBytes.word_mapped source (slot (scalarNodesPointer table key cap) node 32) 32 offset domain
    (slot_arena _ node cap 32 array inside) small
    (slot_aligned _ node cap 32 array inside geometry.nodesAligned (by decide)) aligned

theorem ScalarSingle.range_context {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table key cap value : BitVec 64} (single : ScalarSingle source table key cap 1#64 value) :
    FindLeaf.RangeContext source table (scalarNodesPointer table key cap) 1#64 key 2
      (fun _ => key * 8#64) (fun _ => 0#64) (fun _ => 0#64) := by
  have one : ∀ node : BitVec 64, node ≠ 0#64 → node.toNat < 2 → node = 1#64 := by
    intro node nonzero inside
    have positive : 0 < node.toNat := by
      by_contra zero
      apply nonzero
      apply BitVec.eq_of_toNat_eq
      change node.toNat = 0
      omega
    apply BitVec.eq_of_toNat_eq
    change node.toNat = 1
    omega
  have nodes : FindLeaf.RangeNodes source (scalarNodesPointer table key cap) (key * 8#64) 2
      (fun _ => key * 8#64) (fun _ => 0#64) (fun _ => 0#64) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro node nonzero inside
      exact single.geometry.node_mapped single.domain single.capSmall node (by have lower := single.capLower; omega) 24 (by decide) (by decide)
    · intro node nonzero inside
      rw [one node nonzero inside]
      exact single.leafMarker
    all_goals intro node nonzero inside different; exact False.elim (different rfl)
  exact ⟨nodes, by decide, single.domain, single.geometry.table, single.aligned,
    by simpa only [BitVec.add_zero] using single.fields (table + 0#64, key) (by simp [singleHeaderWrites]),
    single.fields (table + 40#64, scalarNodesPointer table key cap) (by simp [singleHeaderWrites]),
    single.fields (table + 56#64, 1#64) (by simp [singleHeaderWrites])⟩

def forkBits (key : BitVec 64) (difference : Nat) (node : BitVec 64) : BitVec 64 :=
  if node = 3#64 then BitVec.ofNat 64 difference else key * 8#64

/-- The genuine fork fields supply a usable range context with four
possible controls. It remains valid even if the stored difference equals
its marker; no unproved byte-routing fact is used to exclude that case. -/
theorem ScalarForkImage.range_context {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table key cap : BitVec 64} {difference : Nat} {freshLeft : Bool}
    (image : ScalarForkImage source table key cap difference freshLeft) :
    FindLeaf.RangeContext source table (scalarNodesPointer table key cap) 3#64 key 4
      (forkBits key difference) (fun _ => if freshLeft then 2#64 else 1#64) (fun _ => if freshLeft then 1#64 else 2#64) := by
  have three : ∀ node : BitVec 64, node ≠ 0#64 → node.toNat < 4 → node = 1#64 ∨ node = 2#64 ∨ node = 3#64 := by
    intro node nonzero inside
    have positive : 0 < node.toNat := by
      by_contra zero
      apply nonzero
      apply BitVec.eq_of_toNat_eq
      change node.toNat = 0
      omega
    have cases : node.toNat = 1 ∨ node.toNat = 2 ∨ node.toNat = 3 := by omega
    rcases cases with one | two | three
    · exact Or.inl (BitVec.eq_of_toNat_eq one)
    · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq two))
    · exact Or.inr (Or.inr (BitVec.eq_of_toNat_eq three))
  have internal : ∀ node : BitVec 64, node ≠ 0#64 → node.toNat < 4 → forkBits key difference node ≠ key * 8#64 → node = 3#64 := by
    intro node nonzero inside different
    rcases three node nonzero inside with rfl | rfl | rfl
    · simp [forkBits] at different
    · simp [forkBits] at different
    · rfl
  have nodes : FindLeaf.RangeNodes source (scalarNodesPointer table key cap) (key * 8#64) 4
      (forkBits key difference) (fun _ => if freshLeft then 2#64 else 1#64) (fun _ => if freshLeft then 1#64 else 2#64) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro node nonzero inside
      exact image.geometry.node_mapped image.domain image.capSmall node (by have lower := image.available; omega) 24 (by decide) (by decide)
    · intro node nonzero inside
      rcases three node nonzero inside with rfl | rfl | rfl
      · simpa [forkBits] using image.oldMarker
      · simpa [forkBits] using image.freshMarker
      · simpa [forkBits] using image.internalBit
    · intro node nonzero inside different
      exact image.geometry.node_mapped image.domain image.capSmall node (by have lower := image.available; omega) 8 (by decide) (by decide)
    · intro node nonzero inside different
      exact image.geometry.node_mapped image.domain image.capSmall node (by have lower := image.available; omega) 16 (by decide) (by decide)
    · intro node nonzero inside different
      rw [internal node nonzero inside different]
      exact image.leftChild
    · intro node nonzero inside different
      rw [internal node nonzero inside different]
      exact image.rightChild
    · intro node nonzero inside different
      cases freshLeft <;> decide
    · intro node nonzero inside different
      cases freshLeft <;> decide
  exact ⟨nodes, by decide, image.domain, image.geometry.table, image.aligned,
    by simpa only [BitVec.add_zero] using image.fields (table + 0#64, key) (by simp [pairHeaderWrites]),
    image.fields (table + 40#64, scalarNodesPointer table key cap) (by simp [pairHeaderWrites]),
    image.fields (table + 56#64, 3#64) (by simp [pairHeaderWrites])⟩

/-- Every actual singleton update or fresh fork establishes a real
bounded traversal context at its actual resulting root. -/
theorem ScalarSetResult.find_range {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table key cap old value : BitVec 64} (result : ScalarSetResult source table key cap old value) :
    ∃ root limit bits left right, limit ≤ 4 ∧
      FindLeaf.RangeContext source table (scalarNodesPointer table key cap) root key limit bits left right := by
  rcases result with updated | fork
  · exact ⟨1#64, 2, _, _, _, by decide, updated.range_context⟩
  · obtain ⟨difference, freshLeft, image⟩ := fork.image
    exact ⟨3#64, 4, _, _, _, by decide, image.range_context⟩

theorem ScalarSetResult.find_price {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table key cap old value pointer : BitVec 64} (result : ScalarSetResult source table key cap old value)
    (tableCell : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "t") = some (.val (.word table)))
    (pointerCell : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "key") = some (.val (.word pointer)))
    (notTimeout : (evaluateHOLFiniteState source FindLeaf.body).1 ≠ some .timeOut) :
    source.clock - (evaluateHOLFiniteState source FindLeaf.body).2.clock ≤ 4 := by
  obtain ⟨root, limit, bits, left, right, bounded, ready⟩ := result.find_range
  exact (ready.price tableCell pointerCell notTimeout).trans bounded

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarGeometry.node_mapped
#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarSingle.range_context
#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarForkImage.range_context
#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarSetResult.find_range
#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarSetResult.find_price

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack PanSemStateFiniteExact WitnessRadix
set_option maxHeartbeats 2000000

/-- A portable actual fork image survives agreement on its complete
allocation, without preserving an obsolete whole-state insertion receipt. -/
theorem ScalarForkImage.of_interval {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table key cap : BitVec 64} {difference : Nat} {freshLeft : Bool}
    (image : ScalarForkImage source table key cap difference freshLeft)
    (domain : post.memaddrs=source.memaddrs)
    (memory : ∀ query : BitVec 64,table.toNat≤query.toNat → query.toNat<(scalarNextHeap table key cap).toNat →
      post.memory query=source.memory query) : ScalarForkImage post table key cap difference freshLeft := by
  have headerEnd:=image.geometry.header_before_end
  have node (index : BitVec 64) (inside : index.toNat≤cap.toNat) (offset : Nat) (small : offset<32) :
      post.memory (FindLeaf.cell (scalarNodesPointer table key cap) index offset)=
        source.memory (FindLeaf.cell (scalarNodesPointer table key cap) index offset):=by
    have bounds:=image.geometry.node_in_scalar image.capSmall index inside offset small
    exact memory _ bounds.1 bounds.2
  apply image.of_memory domain
  · intro entry member
    have address : ∃ offset : Nat,offset<88 ∧ entry.1=table+BitVec.ofNat 64 offset:=by
      simp only [pairHeaderWrites,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals exact ⟨_,by decide,rfl⟩
    obtain ⟨offset,inside,address⟩:=address
    have number : entry.1.toNat=table.toNat+offset:=by
      rw [address]
      exact byteAddress_toNat table offset (by have upper:=image.geometry.table.upper; omega)
    exact memory entry.1 (by omega) (by omega)
  · intro query member
    simp only [forkCells,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl
    · exact node 1#64 (by have enough:=image.available; change 1≤cap.toNat; omega) 24 (by decide)
    · exact node 2#64 (by have enough:=image.available; change 2≤cap.toNat; omega) 24 (by decide)
    · exact node 3#64 image.available 24 (by decide)
    · exact node 3#64 image.available 8 (by decide)
    · exact node 3#64 image.available 16 (by decide)

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarForkImage.of_interval
