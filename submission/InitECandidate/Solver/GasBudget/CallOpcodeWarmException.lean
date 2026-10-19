import InitECandidate.Solver.GasBudget.CallOpcodeWarmPrefix
import InitECandidate.Solver.GasBudget.CallOpcodeFirstChargeException
import InitECandidate.Solver.Input.ExceptionControl

namespace InitECandidate.Solver.GasBudget.CallOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout Input.RlpWrite MemoryWriter

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 10000 in
theorem exception_warm_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch message sp gas used : BitVec 64)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (aligned : frame.toNat % 8 = 0) (queryMapped : BytesMapped source (frame + 240#64) 20)
    (plan : Plan) (slots : List Nat) (cursor floor : Nat) (table : TableState source .account plan slots cursor floor)
    (environment : WarmKeys.Environment source) (separate : frame.toNat + 280 ≤ floor)
    (messageMapped : source.memaddrs (frame + 112#64)) (messageCell : source.memory (frame + 112#64) = .word message)
    (tableMapped : source.memaddrs (frame + 168#64)) (tableCell : source.memory (frame + 168#64) = .word (cell plan .header 0))
    (spMapped : source.memaddrs (frame + 16#64)) (spCell : source.memory (frame + 16#64) = .word sp)
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (shape : source.eshapes.lookup (ofString "EvmErr") = some .one) (cap : regularBudget source.memory frame ≤ 16777216)
    (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source body = (some (.exception (ofString "EvmErr") payload), post)) :
    ((payload = .val (.word 2#64) ∨ payload = .val (.word 8#64) ∨ payload = .val (.word 4#64)) ∧
      ∃ paid, paid ≤ 8 * slots.length + 65 ∧ FramePrefixEffect source post frame paid) ∨
    ∃ (value inStart inSize outStart outSize : U256Value.Words) (warm : BitVec 64) (paid : Nat)
      (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory) (nextPlan : Plan) (nextSlots : List Nat) (nextCursor : Nat),
      paid ≤ source.clock ∧ ready.clock = source.clock - paid ∧
      paid + GrowRuntime.growthPotential .account plan.capacity ≤
        17 * slots.length + 78 + GrowRuntime.growthPotential .account nextPlan.capacity ∧
      TableState ready .account nextPlan nextSlots nextCursor floor ∧ WarmKeys.Environment ready ∧
      MemoryExtend.View ready frame base current capacity pointer scratch ∧
      regularBudget ready.memory frame = regularBudget source.memory frame ∧
      (wordAt ready.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat +
        (CallFirstFee.amount warm (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current).1 value).toNat ∧
      (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current).1.toNat + (CallGas.stipend value).toNat + 100 ≤
        (CallFirstFee.amount warm (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current).1 value).toNat ∧
      ready.memory (frame + 168#64) = .word (cell nextPlan .header 0) ∧
      slots.length ≤ nextSlots.length ∧ nextSlots.length ≤ slots.length + 1 ∧
      nextPlan.capacity ≤ max plan.capacity (4 * (nextSlots.length + 1)) ∧
      HeapGlobals source ready ∧
      emptyLocalsHOLFinite ready = emptyLocalsHOLFinite
        {source with globals := ready.globals, memory := ready.memory, clock := ready.clock} ∧
      ChargedLocals ready frame message current value inStart inSize outStart outSize warm ∧
      evaluateHOLFiniteState ready afterWarm = (some (.exception (ofString "EvmErr") payload), inner) ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase inner ∧ post.clock = inner.clock := by
  rcases exception_first_charge source post frame base current capacity pointer scratch message sp gas used view aligned queryMapped
      plan slots cursor floor table environment separate messageMapped messageCell tableMapped tableCell spMapped spCell gasMapped usedMapped
      gasCell usedCell shape cap (ofString "EvmErr") payload run with failed | charged
  · obtain ⟨actualId, actualPayload, paid, bound, effect⟩ := failed
    exact Or.inl ⟨actualPayload, paid, bound, effect⟩
  · obtain ⟨value, inStart, inSize, outStart, outSize, warm, firstPaid, first, inner, firstBound, event, surplus, feeRun, scope, postClock, cells⟩ := charged
    have firstView := event.buffer_view view aligned
    have firstTable := event.table .account plan slots cursor floor table aligned view.frameFits separate
    have codes := congrArg PanSemStateFiniteExact.code event.fields
    have domain := congrArg PanSemStateFiniteExact.memaddrs event.fields
    have endian := congrArg PanSemStateFiniteExact.be event.fields
    have globals := congrArg PanSemStateFiniteExact.globals event.fields
    change first.code = source.code at codes
    change first.memaddrs = source.memaddrs at domain
    change first.be = source.be at endian
    change first.globals = source.globals at globals
    have firstEnvironment := environment.of_fields codes domain endian
    have firstMapped : first.memaddrs (frame + 168#64) := by rw [domain]; exact tableMapped
    have firstCell : first.memory (frame + 168#64) = .word (cell plan .header 0) :=
      (event.header aligned view.frameFits 168 (by decide) (by decide) (by decide) (by decide)).trans tableCell
    have queryFits : (frame + 240#64).toNat + 20 < 2^64 := by
      have number : (frame + 240#64).toNat = frame.toNat + 240 := BitVec.toNat_add_of_lt (by change frame.toNat + 240 < 2^64; have bound := view.frameFits; omega)
      have bound := view.frameFits
      omega
    have firstQueryMapped : ∀ offset < 20, first.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress (frame + 240#64) offset)) := by
      intro offset inside
      rw [domain]
      exact queryMapped offset inside
    rw [warm_shape] at feeRun
    rcases Input.sequence_exception first inner warmGuard afterWarm (ofString "EvmErr") payload feeRun with failed | continued
    · have excluded := warm_no_evm_error first firstEnvironment firstView.installed first rfl payload
      rw [failed] at excluded
      exact False.elim (excluded rfl)
    · obtain ⟨ready, warmRun, tailRun⟩ := continued
      obtain ⟨warmPaid, nextPlan, nextSlots, nextCursor, warmFits, warmClock, amortized, nextTable, nextEnvironment,
        nextView, budget, used, header, countLower, countUpper, capacityBound, heapGlobals, fields, outside, sameLocals⟩ :=
        warm_normal_effects first ready frame base current capacity pointer scratch (frame + 240#64) warm firstView plan slots cursor floor firstTable separate
          firstEnvironment firstView.installed firstView.ev firstMapped firstCell cells.warmCell cells.toCell queryFits firstQueryMapped warmRun
      have funded : firstPaid + warmPaid ≤ source.clock := by have fits := event.fits; rw [event.clock] at warmFits; omega
      have clock : ready.clock = source.clock - (firstPaid + warmPaid) := by rw [warmClock, event.clock]; omega
      have credit : (wordAt ready.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat +
          (CallFirstFee.amount warm (MemoryExpansionCost2.resultPair inStart inSize outStart outSize current).1 value).toNat := by
        simpa only [wordAt, used] using event.credit
      have beforeGlobals : HeapGlobals source first := by intro key different; rw [globals]
      have lift := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
        emptyLocalsHOLFinite {state with globals := ready.globals, memory := ready.memory, clock := ready.clock}) event.fields
      exact Or.inr ⟨value, inStart, inSize, outStart, outSize, warm, firstPaid + warmPaid, ready, inner, nextPlan, nextSlots, nextCursor,
        funded, clock, by omega, nextTable, nextEnvironment, nextView, budget.trans event.budget, credit, surplus, header,
        countLower, countUpper, capacityBound, beforeGlobals.trans heapGlobals, fields.trans lift, cells.of_locals sameLocals,
        tailRun, scope, postClock⟩

end InitECandidate.Solver.GasBudget.CallOpcode

#print axioms InitECandidate.Solver.GasBudget.CallOpcode.exception_warm_prefix
