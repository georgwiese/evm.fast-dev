import InitECandidate.Solver.Mpt.WitnessDecodeRows
import InitECandidate.Solver.Mpt.WitnessStackRank

namespace InitECandidate.Solver.Mpt.WitnessRecord
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Analysis data for the two actual activation-record stages. Branch
counters describe the current continuing iteration, including its occupancy. -/
inductive Payload where
  | extension (nibbles length : BitVec 64)
  | branch (node : BitVec 64) (index : Fin 16) (occupied : Fin 17)
def Payload.stage : Payload→BitVec 64 | .extension ..=>1#64 | .branch ..=>2#64
def Payload.count : Payload→Nat | .extension ..=>2 | .branch ..=>17
def Payload.frame : Payload→WitnessStackRank.Frame
  | .extension ..=>.extension | .branch _ index _=>.branch index
def Payload.startAddress : Payload→Nat
  | .extension nibbles _=>nibbles.toNat | .branch node _ _=>node.toNat
def Payload.endAddress : Payload→Nat
  | .extension nibbles length=>nibbles.toNat+length.toNat
  | .branch node _ _=>node.toNat+176
def Payload.Owned (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Payload→Prop
  | .extension nibbles length=>0<length.toNat ∧ length.toNat≤2048 ∧ AllocatedBytes.Arena nibbles length.toNat
  | .branch node _ _=>AllocatedBytes.Arena node 176 ∧ node.toNat%8=0 ∧ source.memory node=.word 3#64

structure Description where
  array : BitVec 64
  pointer : BitVec 64
  length : BitVec 64
  listPointer : BitVec 64
  bytes : Nat
  items : List Rlp.ListItem
  payload : Payload

/-- Only initialized stage fields are asserted. The core installs PREV at0
on push and HASH at80 after resolution; neither is presumed initialized here. -/
def Description.cells (data : Description) : List (Nat×BitVec 64):=
  match data.payload with
  | .extension nibbles length=>
      [(8,1#64),(24,data.array),(48,data.pointer),(56,data.length),(64,nibbles),(72,length)]
  | .branch node index occupied=>
      [(8,2#64),(16,node),(24,data.array),(32,BitVec.ofNat 64 index.val),(40,BitVec.ofNat 64 occupied.val),(48,data.pointer),(56,data.length)]
def Description.BeforeHeap (data : Description) (frontier : Nat) : Prop:=
  data.array.toNat+16*data.items.length≤frontier ∧ data.payload.endAddress≤frontier

/-- Physical ownership of a real live record, its row array and its stage
data. Input slices stay bounded before the actual immutable node database;
the record remains in the scratch band while arrays are persistent. -/
structure View (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db : BitVec 64) (data : Description) : Prop where
  arena : AllocatedBytes.Arena record 88
  aligned : record.toNat%8=0
  ceiling : record.toNat+88≤2713717616
  arrayFloor : 2713731432≤data.array.toNat
  payloadFloor : 2713731432≤data.payload.startAddress
  cells : ∀ entry∈data.cells,source.memory (record+BitVec.ofNat 64 entry.1)=.word entry.2
  rows : WitnessDecode.Rows source data.array data.listPointer data.bytes data.items
  count : data.items.length=data.payload.count
  parentBound : data.length.toNat≤1024
  parentLower : 2713731432≤data.pointer.toNat
  parentBeforeDb : data.pointer.toNat+data.length.toNat≤db.toNat
  payloadLower : data.pointer.toNat≤data.listPointer.toNat
  payloadUpper : data.listPointer.toNat+data.bytes≤data.pointer.toNat+data.length.toNat
  owned : data.payload.Owned source

theorem Description.BeforeHeap.mono (data : Description) (first second : Nat) (before : data.BeforeHeap first) (grows : first≤second) : data.BeforeHeap second:=
  ⟨before.1.trans grows,before.2.trans grows⟩

theorem View.nonzero (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db : BitVec 64) (data : Description)
    (view : View source record db data) : record≠0#64 := by
  intro zero
  have lower:=view.arena.lower
  rw [zero] at lower
  change 2701131776≤0 at lower
  omega

theorem View.mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db : BitVec 64) (data : Description)
    (view : View source record db data) (offset : Nat) (inside : offset<88) (aligned : offset%8=0) : source.memaddrs (byteAddress record offset):=
  AllocatedBytes.word_mapped source record 88 offset view.rows.domain view.arena inside view.aligned aligned

theorem View.stage (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db : BitVec 64) (data : Description)
    (view : View source record db data) : source.memory (record+8#64)=.word data.payload.stage := by
  have member : (8,data.payload.stage)∈data.cells:=by
    cases payloadEq : data.payload <;> simp [Description.cells,Payload.stage,payloadEq]
  exact view.cells _ member

end InitECandidate.Solver.Mpt.WitnessRecord

#print axioms InitECandidate.Solver.Mpt.WitnessRecord.Description.BeforeHeap.mono
#print axioms InitECandidate.Solver.Mpt.WitnessRecord.View.nonzero
#print axioms InitECandidate.Solver.Mpt.WitnessRecord.View.mapped
#print axioms InitECandidate.Solver.Mpt.WitnessRecord.View.stage
