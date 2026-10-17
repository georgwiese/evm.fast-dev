import InitECandidate.Solver.MutableTable.GrowRuntime.Reads
import InitECandidate.Solver.MutableTable.MemoryModelInsertCall

namespace InitECandidate.Solver.MutableTable.GrowRuntime
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Snapshot preservation for the old arrays read by the original rehash
loop. The header deliberately is excluded because growth replaces it. -/
def OldArrays (source snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan) : Prop :=
  ∀ pool : Pool, pool ≠ .header → ∀ offset < size kind old pool, source.memory (cell old pool offset) = snapshot.memory (cell old pool offset)

theorem OldArrays.of_memory (source target snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (same : source.memory = target.memory) (frame : OldArrays source snapshot kind old) : OldArrays target snapshot kind old := by
  intro pool array offset inside
  rw [← same]
  exact frame pool array offset inside

theorem old_order_cell (source snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (valid : Valid kind old) (slots : List Nat) (bounded : slots.length ≤ old.capacity)
    (occupied : MemoryModel.Occupied snapshot kind old slots) (frame : OldArrays source snapshot kind old) (index : Fin slots.length) :
    source.memory (cell old .order 0 + BitVec.ofNat 64 index.val * 8#64) = .word (BitVec.ofNat 64 (slots.get index)) := by
  have small : index.val < 2 ^ 64 := by
    have capHigh := capacity_small kind old valid
    have high := index.isLt
    omega
  rw [scaled_cell, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, Nat.mul_comm]
  rw [frame .order (by decide) _ (by change 8 * index.val < 8 * old.capacity; have high := index.isLt; omega)]
  exact occupied.order index

theorem LoopLocals.bind_i (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan) (count index : Nat)
    (locals : LoopLocals source kind old count index) (slot : BitVec 64) :
    LoopLocals (WitnessRadix.QueryBranch.bind source "i" slot) kind old count index := by
  refine ⟨(bind_lookup_other source "i" "t" slot (by decide)).trans locals.table,
    (bind_lookup_other source "i" "stride" slot (by decide)).trans locals.stride,
    (bind_lookup_other source "i" "keys" slot (by decide)).trans locals.keys,
    (bind_lookup_other source "i" "vals" slot (by decide)).trans locals.vals,
    (bind_lookup_other source "i" "order" slot (by decide)).trans locals.order,
    (bind_lookup_other source "i" "nitems" slot (by decide)).trans locals.countLocal,
    (bind_lookup_other source "i" "k" slot (by decide)).trans locals.indexLocal⟩

theorem LoopLocals.next (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan) (count index : Nat)
    (locals : LoopLocals source kind old count index) (memory : WordWrites.Memory) (paid : Nat) :
    LoopLocals (WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - paid} "k" (BitVec.ofNat 64 (index + 1))) kind old count (index + 1) := by
  refine ⟨(bind_lookup_other {source with memory := memory, clock := source.clock - paid} "k" "t" _ (by decide)).trans locals.table,
    (bind_lookup_other {source with memory := memory, clock := source.clock - paid} "k" "stride" _ (by decide)).trans locals.stride,
    (bind_lookup_other {source with memory := memory, clock := source.clock - paid} "k" "keys" _ (by decide)).trans locals.keys,
    (bind_lookup_other {source with memory := memory, clock := source.clock - paid} "k" "vals" _ (by decide)).trans locals.vals,
    (bind_lookup_other {source with memory := memory, clock := source.clock - paid} "k" "order" _ (by decide)).trans locals.order,
    (bind_lookup_other {source with memory := memory, clock := source.clock - paid} "k" "nitems" _ (by decide)).trans locals.countLocal,
    bind_lookup_same _ _ _⟩

/-- Actual complete raw insertion retains the old rehash snapshot while
producing the next physical new-table model. -/
theorem inserted_old_arrays (source snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (oldValid : Valid kind old) (start capacity : Nat) (newValid : Valid kind (relocated kind (old.base .header) start capacity))
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start) (frame : OldArrays source snapshot kind old)
    (query index count value : BitVec 64) (inside : index.toNat < capacity) (countInside : count.toNat < capacity) :
    OldArrays {source with memory := MemoryModel.insertedMemory source.memory source.be kind (relocated kind (old.base .header) start capacity) query index count value}
      snapshot kind old := by
  intro pool array offset oldInside
  change MemoryModel.insertedMemory source.memory source.be kind (relocated kind (old.base .header) start capacity) query index count value (cell old pool offset) = snapshot.memory (cell old pool offset)
  rw [MemoryModel.rehash_old_array source.memory source.be kind old oldValid start capacity newValid earlier query index count value inside countInside pool array offset oldInside]
  exact frame pool array offset oldInside

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.OldArrays.of_memory
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.old_order_cell
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.LoopLocals.bind_i
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.LoopLocals.next
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.inserted_old_arrays
