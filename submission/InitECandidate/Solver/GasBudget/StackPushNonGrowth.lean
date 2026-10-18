import InitECandidate.Solver.GasBudget.StackPushNonGrowthEntry
import InitECandidate.Solver.GasBudget.StackPushWrites

namespace InitECandidate.Solver.GasBudget.StackPush
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Full unchanged stack_push on an existing free slot. Incoming stack/header
ownership remains explicit; reached destination mappings and the complete
guard/store/return execution follow from the real normal body. Zero source
clocks here means no calls/loops, not zero straight-line target work. -/
theorem non_growth_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base sp capacity : BitVec 64)
    (storedValue returned : ValueHOL 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (vLocal : source.locals.lookup (ofString "v") = some storedValue)
    (valueShape : shapeOfHOLExact storedValue = .comb [.one, .one, .one, .one])
    (spCell : source.memory (frame + 16#64) = .word sp) (capCell : source.memory (frame + 232#64) = .word capacity)
    (baseMapped : source.memaddrs (frame + 8#64)) (baseCell : source.memory (frame + 8#64) = .word base)
    (room : sp < capacity) (bounded : capacity.toNat ≤ 1024)
    (separate : ∀ offset ∈ ([64, 184, 192] : List Nat), ∀ index < 4,
      frame + BitVec.ofNat 64 offset ≠ (base + sp * 32#64) + BitVec.ofNat 64 (8 * index))
    (normal : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ post.clock = source.clock ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory} ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      post.memory (frame + 16#64) = .word (sp + 1#64) ∧
      (wordAt post.memory (frame + 16#64)).toNat = sp.toNat + 1 ∧
      post.memory (frame + 184#64) = source.memory (frame + 184#64) ∧
      (∀ address, address ≠ frame + 16#64 →
        (∀ index < 4, address ≠ (base + sp * 32#64) + BitVec.ofNat 64 (8 * index)) →
        post.memory address = source.memory address) := by
  obtain ⟨inner, spMapped, capMapped, writesRun, postEq⟩ :=
    non_growth_entry source post frame sp capacity ev spCell capCell room bounded returned normal
  have storedLocal : (entered source sp capacity).locals.lookup (ofString "v") = some storedValue :=
    (bind_lookup_other _ "cap" "v" _ (by decide)).trans ((bind_lookup_other _ "sp" "v" _ (by decide)).trans vLocal)
  have spLocal : (entered source sp capacity).locals.lookup (ofString "sp") = some (.val (.word sp)) :=
    (bind_lookup_other _ "cap" "sp" _ (by decide)).trans (bind_lookup_same _ _ _)
  obtain ⟨valueEq, clock, frameEq, spFinal, outside⟩ := writes_normal (entered source sp capacity) inner frame base sp storedValue returned
    ev spLocal storedLocal valueShape baseMapped baseCell writesRun
  have postMemory : post.memory = inner.memory := by rw [postEq]; rfl
  have retained (offset : Nat) (member : offset ∈ ([64, 184, 192] : List Nat)) :
      post.memory (frame + BitVec.ofNat 64 offset) = source.memory (frame + BitVec.ofNat 64 offset) := by
    rw [postMemory]
    apply outside
    · apply offsets_ne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide
    · exact separate offset member
  have postFrame : emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory} := by
    rw [postEq]
    exact frameEq
  have postClock : post.clock = source.clock := by rw [postEq]; exact clock
  have finalSP : post.memory (frame + 16#64) = .word (sp + 1#64) := by rw [postMemory]; exact spFinal
  have spFits : sp.toNat + (1#64 : BitVec 64).toNat < 2 ^ 64 := by change sp.toNat < capacity.toNat at room; change sp.toNat + 1 < 2 ^ 64; omega
  refine ⟨valueEq, postClock, postFrame, ?_, finalSP, ?_, retained 184 (by simp), ?_⟩
  · simp only [regularBudget, wordAt, retained 64 (by simp), retained 184 (by simp), retained 192 (by simp)]
  · simp only [wordAt, finalSP, WitnessRadix.MemoryBytes.wordBits, BitVec.toNat_add_of_lt spFits]
    rfl
  · intro address notSP away
    rw [postMemory]
    exact outside address notSP away

end InitECandidate.Solver.GasBudget.StackPush

#print axioms InitECandidate.Solver.GasBudget.StackPush.non_growth_normal
