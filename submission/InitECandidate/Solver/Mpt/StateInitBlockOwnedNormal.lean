import InitECandidate.Solver.Mpt.StateInitBlockModels
import InitECandidate.Solver.Mpt.StateInitBlockFieldValues
import InitECandidate.Solver.Mpt.StateInitBlockGlobals

namespace InitECandidate.Solver.Mpt.StateInit.Block
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable MutableTable.NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch GasBudget.Journal

theorem TableEntry.pointer (entry : TableEntry) : entry.object.pointer=BitVec.ofNat 64 entry.start:=by
  simp [TableEntry.object,TableFamily.Object.pointer,cell,fresh]

theorem action_offset_positive (action : Action) (member : action∈actions) : 0<action.offset:=by
  simp only [actions,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
theorem initialized_from_tables (post tables : PanSemStateFiniteExact 64 Guest.HostMemory) (heap workspace : BitVec 64)
    (lower : 2701131776≤heap.toNat) (aligned : heap.toNat%8=0) (nextNumber : (PersistentAlloc.rounded heap 80#64).toNat=heap.toNat+80)
    (bound : heap.toNat+16848200≤33806089496) (same : post=completed tables ((PersistentAlloc.rounded heap 80#64).toNat+70840))
    (blockCell : post.globals.lookup (ofString "bs")=some (.val (.word heap)))
    (family : TableFamily.Model tables ((PersistentAlloc.rounded heap 80#64).toNat+70840) (objects (PersistentAlloc.rounded heap 80#64).toNat))
    (pointers : ∀ entry∈entries (PersistentAlloc.rounded heap 80#64).toNat actions,tables.memory (MemoryRegion.address ⟨heap.toNat,80⟩ entry.offset)=.word (BitVec.ofNat 64 entry.start))
    (values : ∀ site∈fields (PersistentAlloc.rounded heap 80#64).toNat actions,tables.memory (MemoryRegion.address ⟨heap.toNat,80⟩ site.1)=.word site.2)
    (olderWorkspace : tables.memory heap=.word workspace) : Initialized post heap workspace:=by
  let start:=(PersistentAlloc.rounded heap 80#64).toNat
  let finalCursor:=heap.toNat+16848200
  let journalBase:=start+70840+64
  have endEq : start+70840+64+Initialization.bytes=finalCursor:=block_end_arithmetic heap.toNat start nextNumber
  have finalAligned : finalCursor%8=0:=by omega
  have journalAligned : journalBase%8=0:=by dsimp only [journalBase]; omega
  have memory : post.memory=tables.memory:=by rewrite [same]; rfl
  have postDomain : post.memaddrs=tables.memaddrs:=by rewrite [same]; rfl
  have postEndian : post.be=tables.be:=by rewrite [same]; rfl
  have journalGlobals:=Initialization.globals (scratchState tables (start+70840)) journalBase
  have postHeap : post.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 finalCursor))):=by
    rewrite [same]
    change (Initialization.initialized (scratchState tables (start+70840)) journalBase).globals.lookup _=_
    rewrite [←endEq]
    exact journalGlobals.1
  have postFamily : TableFamily.Model post finalCursor (objects start):=
    family.advance_cursor postHeap (by omega) bound finalAligned memory postDomain postEndian
  have journalValid : MemoryRegion.Valid ⟨journalBase,32*Initialization.capacity⟩:=by
    have byteNumber : 32*Initialization.capacity=Initialization.bytes:=by decide
    constructor
    · change 2701131776≤journalBase; dsimp only [journalBase]; omega
    · change journalBase+32*Initialization.capacity≤33806089496
      rewrite [byteNumber]
      change start+70840+64+Initialization.bytes≤33806089496
      rewrite [endEq]; exact bound
    · exact journalAligned
  have zone : Zone (objects start) journalBase Initialization.capacity finalCursor:=by
    refine ⟨journalValid,?_,?_⟩
    · have byteNumber : 32*Initialization.capacity=Initialization.bytes:=by decide
      rewrite [byteNumber]
      exact Nat.le_of_eq endEq
    · intro index inside field table
      apply TableFootprint.Outside.of_regions (objects start table).kind (objects start table).plan (family.tables table).valid
      intro pool
      right
      rewrite [entry_number journalBase Initialization.capacity index field journalValid inside]
      have earlier:=(family.tables table).earlier pool
      change (objects start table).plan.base pool+size (objects start table).kind (objects start table).plan pool≤start+70840 at earlier
      dsimp only [journalBase]
      omega
  refine ⟨?_,?_,?_,?_,postFamily,?_,zone,?_,?_,?_,?_,?_⟩
  · exact blockCell
  · exact (congrFun memory heap).trans olderWorkspace
  · exact (congrFun memory _).trans (values _ (ancestor_sites start).1)
  · exact (congrFun memory _).trans (values _ (ancestor_sites start).2)
  · intro index
    rewrite [congrFun memory _]
    rewrite [objects,TableEntry.pointer]
    exact pointers _ (List.getElem_mem index.isLt)
  · intro entries; exact Image.empty post (objects start) journalBase entries
  · rewrite [same]; exact journalGlobals.2.1
  · rewrite [same]; exact journalGlobals.2.2.1
  · rewrite [same]; exact journalGlobals.2.2.2.1
  · rewrite [same]; exact journalGlobals.2.2.2.2


set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
/-- Build the full physical block/journal model from the exact real normal
suffix result, its derived layouts and final bound. -/
theorem initialized_of_result (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap workspace : BitVec 64)
    (lower : 2701131776≤heap.toNat) (aligned : heap.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false)
    (bound : heap.toNat+16848200≤33806089496)
    (layouts : Layouts (PersistentAlloc.rounded heap 80#64).toNat actions)
    (same : post=resultState source heap workspace) : Initialized post heap workspace:=by
  let start:=(PersistentAlloc.rounded heap 80#64).toNat
  let entered:=ready source heap workspace
  have arena : AllocatedBytes.Arena heap 80:=⟨lower,by omega⟩
  have nextNumber : start=heap.toNat+80:=by
    have number:=PersistentAlloc.rounded_nat heap 80#64 (by change heap.toNat+80+7<2^64; omega)
    change start=(heap.toNat+80+7)/8*8 at number
    omega
  have recordValid : MemoryRegion.Valid ⟨heap.toNat,80⟩:=⟨lower,arena.upper,aligned⟩
  have family:=entries_family actions entered heap.toNat start recordValid actions_valid layouts (by omega) domain little
  have pointers:=entries_fields actions entered heap.toNat start recordValid actions_valid action_offsets_distinct layouts (by omega)
  have values:=fields_values actions entered heap.toNat start recordValid actions_valid action_offsets_distinct layouts (by omega)
  have olderWorkspace : (walk entered heap.toNat start actions).memory heap=.word workspace:=by
    have retained:=walk_word_away actions entered heap.toNat start layouts heap (by omega) (by
      intro action member equal
      have numeric:=congrArg BitVec.toNat equal
      have valid:=actions_valid action member
      have offsetBound : action.offset≤80:=by
        cases action with
        | scalar offset value=>have h:=valid.1; change offset≤80; omega
        | table kind bits offset=>have h:=valid.2.2.1; change offset≤80; omega
      rewrite [MemoryRegion.address_number ⟨heap.toNat,80⟩ recordValid action.offset offsetBound] at numeric
      have positive:=action_offset_positive action member
      change heap.toNat=heap.toNat+action.offset at numeric
      omega)
    exact retained.trans (if_pos rfl)
  rewrite [cursor_all] at family
  generalize tablesEq : walk entered heap.toNat start actions=tables at family pointers values olderWorkspace
  apply initialized_from_tables post tables heap workspace lower aligned nextNumber bound
  · rewrite [same,resultState,tablesEq]; rfl
  · rewrite [same]; exact result_block_pointer source heap workspace
  · exact family
  · exact pointers
  · exact values
  · exact olderWorkspace

end InitECandidate.Solver.Mpt.StateInit.Block

#print axioms InitECandidate.Solver.Mpt.StateInit.Block.TableEntry.pointer
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.action_offset_positive
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.initialized_from_tables
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.initialized_of_result
