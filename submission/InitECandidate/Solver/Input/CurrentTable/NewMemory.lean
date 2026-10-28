import InitECandidate.Solver.Input.CurrentTable.NewReturned
import InitECandidate.Solver.WitnessRadix.WordWrites
import Mathlib.Data.List.Nodup

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Exactly the eleven actual current table metadata stores, in order. -/
def writes (table cap : BitVec 64) : List (BitVec 64×BitVec 64) :=
  [(table+0#64,32#64),(table+8#64,32#64),(table+16#64,cap),(table+24#64,0#64),
   (table+32#64,keysPointer table),(table+40#64,nodesPointer table cap),(table+48#64,orderPointer table cap),
   (table+56#64,0#64),(table+64#64,1#64),(table+72#64,0#64),(table+80#64,cap)]

/-- The derived successful constructor state has exactly those writes;
its four allocations change only the heap global. No array clearing or
uninitialized array contents are smuggled into the current representation. -/
theorem finish_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap : BitVec 64) :
    (finishSource source table cap).memory=WordWrites.write source.memory (writes table cap) := by
  rfl

theorem write_addresses (table cap : BitVec 64) :
    (writes table cap).map Prod.fst=([0#64,8#64,16#64,24#64,32#64,40#64,48#64,56#64,64#64,72#64,80#64] : List (BitVec 64)).map (fun offset=>table+offset) := rfl

theorem writes_distinct (table cap : BitVec 64) : ((writes table cap).map Prod.fst).Nodup := by
  rw [write_addresses]
  apply List.Nodup.map (fun left right same=>(BitVec.add_right_inj table).mp same)
  decide

set_option maxHeartbeats 1000000 in
/-- Every actual current metadata field has its stored value after the
same normal constructor return. -/
theorem finish_field (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap : BitVec 64)
    (entry : BitVec 64×BitVec 64) (member : entry∈writes table cap) :
    (finishSource source table cap).memory entry.1=.word entry.2 := by
  rw [finish_memory]
  exact WordWrites.write_unique source.memory (writes table cap) entry (writes_distinct table cap) member

/-- All original input memory before the fresh table remains intact. -/
theorem finish_before (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap query : BitVec 64)
    (arena : AllocatedBytes.Arena table 88) (before : query.toNat<table.toNat) :
    (finishSource source table cap).memory query=source.memory query := by
  rw [finish_memory]
  apply WordWrites.write_away
  intro member
  rw [write_addresses] at member
  obtain ⟨offset,inside,same⟩:=List.mem_map.mp member
  have small : offset.toNat<88 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  have number : (table+offset).toNat=table.toNat+offset.toNat := BitVec.toNat_add_of_lt (by have upper:=arena.upper; omega)
  have equal:=congrArg BitVec.toNat same
  rw [number] at equal
  omega

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.finish_memory
#print axioms InitECandidate.Solver.Input.CurrentTable.New.writes_distinct
#print axioms InitECandidate.Solver.Input.CurrentTable.New.finish_field
#print axioms InitECandidate.Solver.Input.CurrentTable.New.finish_before
