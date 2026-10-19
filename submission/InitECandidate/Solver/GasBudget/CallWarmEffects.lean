import InitECandidate.Solver.GasBudget.CallWarmStage
import InitECandidate.Solver.GasBudget.MemoryBufferHeapEffect

namespace InitECandidate.Solver.GasBudget.CallOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

theorem warm_normal_effects (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base current capacity pointer scratch query warm : BitVec 64)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (plan : Plan) (slots : List Nat) (cursor floor : Nat) (table : TableState source .account plan slots cursor floor)
    (separate : frame.toNat + 280 ≤ floor)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (tableMapped : source.memaddrs (frame + 168#64)) (tableCell : source.memory (frame + 168#64) = .word (cell plan .header 0))
    (warmCell : source.locals.lookup (ofString "warm") = some (.val (.word warm)))
    (queryCell : source.locals.lookup (ofString "to") = some (.val (.word query)))
    (queryFits : query.toNat + 20 < 2^64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)))
    (run : evaluateHOLFiniteState source warmGuard = (none, post)) :
    ∃ paid nextPlan nextSlots nextCursor, paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      paid + GrowRuntime.growthPotential .account plan.capacity ≤ 9 * slots.length + 13 + GrowRuntime.growthPotential .account nextPlan.capacity ∧
      TableState post .account nextPlan nextSlots nextCursor floor ∧ WarmKeys.Environment post ∧
      MemoryExtend.View post frame base current capacity pointer scratch ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      post.memory (frame + 184#64) = source.memory (frame + 184#64) ∧
      post.memory (frame + 168#64) = .word (cell nextPlan .header 0) ∧
      slots.length ≤ nextSlots.length ∧ nextSlots.length ≤ slots.length + 1 ∧
      nextPlan.capacity ≤ max plan.capacity (4 * (nextSlots.length + 1)) ∧
      HeapGlobals source post ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite
        {source with globals := post.globals, memory := post.memory, clock := post.clock} ∧
      (∀ address : BitVec 64, address.toNat < floor → post.memory address = source.memory address) ∧ post.locals = source.locals := by
  obtain ⟨paid, nextPlan, nextSlots, nextCursor, funded, clock, amortized, nextTable, nextEnvironment,
    countLower, countUpper, capacityBound, header, globals, fields, outside, locals⟩ :=
    warm_normal source post frame query warm plan slots cursor floor table environment installed ev tableMapped tableCell
      warmCell queryCell queryFits queryMapped run
  have cell (offset : Nat) (small : offset < 280) :
      post.memory (frame + BitVec.ofNat 64 offset) = source.memory (frame + BitVec.ofNat 64 offset) := by
    apply outside
    have offsetBound : offset < 2^64 := by omega
    have number : (frame + BitVec.ofNat 64 offset).toNat = frame.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt offsetBound]; have bound := view.frameFits; omega),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt offsetBound]
    rw [number]
    omega
  have canonical : emptyLocalsHOLFinite post = emptyLocalsHOLFinite
      {source with globals := post.globals, memory := post.memory, clock := post.clock} := by rw [clock]; exact fields
  have postView := view.after_heap_effect canonical globals (by
    intro offset member
    apply cell
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    omega)
  have budget : regularBudget post.memory frame = regularBudget source.memory frame := by
    simp only [regularBudget, wordAt, cell 64 (by decide), cell 184 (by decide), cell 192 (by decide)]
  refine ⟨paid, nextPlan, nextSlots, nextCursor, funded, clock, amortized, nextTable, nextEnvironment,
    postView, budget, cell 184 (by decide), ?_, countLower, countUpper, capacityBound, globals, canonical, outside, locals⟩
  rw [cell 168 (by decide), header, tableCell]

end InitECandidate.Solver.GasBudget.CallOpcode

#print axioms InitECandidate.Solver.GasBudget.CallOpcode.warm_normal_effects
