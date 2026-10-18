import InitECandidate.Solver.MutableTable.CopyWalkContents

namespace InitECandidate.Solver.MutableTable.TableCopy
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

theorem copied_header_at (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old next : Plan)
    (oldValid : Valid kind old) (nextValid : Valid kind next) (sameCapacity : next.capacity = old.capacity)
    (earlier : ∀ first second, old.base first + size kind old first ≤ next.base second)
    (query : Nat) (inside : query < 72) (aligned : query % 8 = 0) :
    (walk source kind old next pools).memory (cell next .header query) =
      headerWord (source.memory (cell old .header query)) next query [.keys, .values, .used, .order, .position] := by
  rw [pools, walk]
  rw [walk_header_at (stageState source kind old next .header) kind old next nextValid sameCapacity [.keys, .values, .used, .order, .position] (by simp) query inside, stage_memory]
  exact congrArg (fun value => headerWord value next query [.keys, .values, .used, .order, .position])
    (stage_word_at source.memory source.be kind old next oldValid nextValid sameCapacity earlier .header (by decide) query inside aligned)

/-- Copying the old header and rewriting exactly its five array pointers
establishes all nine meanings in the new physical header. -/
theorem copied_header (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old next : Plan)
    (oldValid : Valid kind old) (nextValid : Valid kind next) (sameCapacity : next.capacity = old.capacity)
    (earlier : ∀ first second, old.base first + size kind old first ≤ next.base second)
    (count : BitVec 64) (header : MemoryModel.Header source.memory kind old count) :
    MemoryModel.Header (walk source kind old next pools).memory kind next count := by
  intro offset value member
  simp only [MemoryModel.headerEntries, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals rw [copied_header_at source kind old next oldValid nextValid sameCapacity earlier _ (by decide) (by decide)]
  all_goals simp only [headerWord, headerOffset, Nat.reduceEqDiff, ite_false, ite_true]
  all_goals first | rfl | exact header _ _ (by simp [MemoryModel.headerEntries, sameCapacity])

theorem used_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (valid : Valid kind plan) (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slot : Nat) (inside : slot < plan.capacity) :
    Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 slot) = some (CopyContents.byte source.memory (cell plan .used slot)) := by
  have mapped : source.memaddrs (panByteAlignHOL (width := 64) (cell plan .used slot)) := by
    rw [domain]
    exact NaturalLayout.byte_mapped kind plan valid .used slot (used_offset_inside kind plan slot inside)
  change @panMemLoadByteHOL 64 _ source.memory source.memaddrs
    (fun address => Classical.propDecidable (source.memaddrs address)) source.be (cell plan .used 0 + BitVec.ofNat 64 slot) = _
  rw [constant_cell, little]
  cases stored : source.memory (panByteAlignHOL (width := 64) (cell plan .used slot)) with
  | word value => simp [panMemLoadByteHOL, mapped, stored, CopyContents.byte, MemoryBytes.wordBits]

/-- The real copied order/position words and used bytes establish the
same occupied-slot representation at the cloned layout. -/
theorem copied_occupied (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old next : Plan)
    (oldValid : Valid kind old) (nextValid : Valid kind next) (sameCapacity : next.capacity = old.capacity)
    (earlier : ∀ first second, old.base first + size kind old first ≤ next.base second)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (shape : old.capacity = 4 ∨ old.capacity % 8 = 0) (slots : List Nat) (occupied : MemoryModel.Occupied source kind old slots) :
    MemoryModel.Occupied (walk source kind old next pools) kind next slots := by
  let target := walk source kind old next pools
  have frame := walk_frame source kind old next pools
  have domainKept := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) frame
  have endianKept := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) frame
  have nextDomain : target.memaddrs = InitE.ordinaryDomain := domainKept.trans domain
  have nextLittle : target.be = false := endianKept.trans little
  have lengthBound := MemoryModel.Occupied.length_le source kind old slots occupied
  refine ⟨occupied.distinct, ?_, ?_, ?_, ?_⟩
  · intro slot member
    rw [sameCapacity]
    exact occupied.inside slot member
  · intro slot inside
    have oldInside : slot < old.capacity := by rw [← sameCapacity]; exact inside
    rw [used_read target kind next nextValid nextDomain nextLittle slot inside]
    have actual := occupied.used slot oldInside
    rw [used_read source kind old oldValid domain little slot oldInside] at actual
    rw [walk_used_at source kind old next oldValid nextValid sameCapacity earlier shape little pools (by simp [pools]) slot oldInside]
    exact actual
  · intro index
    exact (walk_word_at source kind old next oldValid nextValid sameCapacity earlier pools .order (by simp [pools]) (by decide) (by decide)
      (8 * index.val) (by change 8 * index.val < 8 * old.capacity; have := index.isLt; omega) (by omega)).trans (occupied.order index)
  · intro index
    have slotInside := occupied.inside _ (List.get_mem slots index)
    exact (walk_word_at source kind old next oldValid nextValid sameCapacity earlier pools .position (by simp [pools]) (by decide) (by decide)
      (8 * slots.get index) (by change 8 * slots.get index < 8 * old.capacity; omega) (by omega)).trans (occupied.position index)

end InitECandidate.Solver.MutableTable.TableCopy

#print axioms InitECandidate.Solver.MutableTable.TableCopy.copied_header_at
#print axioms InitECandidate.Solver.MutableTable.TableCopy.copied_header
#print axioms InitECandidate.Solver.MutableTable.TableCopy.used_read
#print axioms InitECandidate.Solver.MutableTable.TableCopy.copied_occupied
