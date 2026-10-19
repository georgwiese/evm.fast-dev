import InitECandidate.Solver.GasBudget.ForwardCalculator
import InitECandidate.Solver.GasBudget.MemoryBufferLedgerView
import InitECandidate.Solver.GasBudget.MemoryExtendFrameSums
import InitECandidate.Solver.GasBudget.MemoryExtendGlobals
import InitECandidate.Solver.GasBudget.MemoryExtendAmortized

namespace InitECandidate.Solver.GasBudget.ForwardPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def expansionProgram (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) : ProgHOL 64 :=
  calculatorProgram arguments (.seq (.call (some (none, none)) (ofString "extend_memory") [.rfield 1 (localVar "x")]) continuation)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
/-- Actual calculator, forward charge/debit and physical memory expansion.
The current pending-cost/stipend coverage is the link supplied by the first
fee; every later helper run, funding and buffer model is derived here. -/
theorem expansion_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base current capacity pointer scratch left used requested memoryCost expand amount : BitVec 64) (oldUsed : Nat)
    (words : U256Zero.Quad) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (view : MemoryExtend.View source frame base current capacity pointer scratch)
    (advance : MemoryExpansionCost.Advance current expand amount oldUsed)
    (coverage : (MemoryGasCost.resultWord (MemoryExtend.newLength current expand)).toNat + (CallGas.stipend words).toNat ≤ used.toNat)
    (gasCell : source.memory (frame + 64#64) = .word left) (usedCell : source.memory (frame + 184#64) = .word used)
    (xCell : source.locals.lookup (ofString "x") = some (.rStruct [.val (.word memoryCost), .val (.word expand)]))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (CallGas.values words requested left))
    (calculatorCode : source.code.lookup (ofString "calculate_message_call_gas") = some (CallGas.formals, CallGas.body, CallGas.returnShape))
    (zeroCode : source.code.lookup (ofString "u256_is_zero") = some (U256Zero.formals, U256Zero.body, .one))
    (addCode : source.code.lookup (ofString "add_sat") = some (AddExact.formals, AddExact.body, .one))
    (chargeCode : source.code.lookup (ofString "charge_gas") = some (RegularCharge.formals, RegularCharge.body, .one))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (run : evaluateHOLFiniteState source (expansionProgram arguments continuation) = (some (.returned returned), post)) :
    ∃ ready inner, MemoryExtend.price current capacity expand + 5 ≤ source.clock ∧
      ready.clock = source.clock - (MemoryExtend.price current capacity expand + 5) ∧
      MemoryExtend.View ready frame base (MemoryExtend.newLength current expand) (MemoryExtend.nextCapacity current capacity expand)
        (base + MemoryExtend.nextCapacity current capacity expand) scratch ∧
      regularBudget ready.memory frame + (CallGas.capped requested left + CallGas.stipend words).toNat = regularBudget source.memory frame ∧
      (wordAt ready.memory (frame + 184#64)).toNat + (CallGas.stipend words).toNat = used.toNat ∧
      (MemoryGasCost.resultWord (MemoryExtend.newLength current expand)).toNat ≤ (wordAt ready.memory (frame + 184#64)).toNat ∧
      evaluateHOLFiniteState ready continuation = (some (.returned returned), inner) ∧ post = restore source "mcg" inner ∧
      MemoryExtend.price current capacity expand + 5 + MemoryExtend.potential current capacity ≤
        MemoryExtend.potential (MemoryExtend.newLength current expand) (MemoryExtend.nextCapacity current capacity expand) + 8 ∧
      (∀ query, Arenas.Outside base scratch query → query ≠ frame + 32#64 → query ≠ frame + 40#64 →
        query ≠ frame + 64#64 → query ≠ frame + 184#64 → ready.memory query = source.memory query) ∧
      (∀ key, key ≠ ofString "frame_mem_ptr" → ready.globals.lookup key = source.globals.lookup key) := by
  have funded : CallGas.stipend words ≤ used := by change (CallGas.stipend words).toNat ≤ used.toNat; omega
  obtain ⟨forwarded, inner, fits, fields, tailRun, scope, budget, usedReady, gasReady, debit, outside, locals⟩ :=
    calculator_normal source post frame left used requested words arguments _ returned view.ev gasCell usedCell args calculatorCode zeroCode addCode chargeCode cap funded run
  have forwardClock := congrArg PanSemStateFiniteExact.clock fields
  change forwarded.clock = source.clock - 4 at forwardClock
  have canonical : emptyLocalsHOLFinite forwarded = emptyLocalsHOLFinite {source with memory := forwarded.memory, clock := forwarded.clock} := by
    rw [forwardClock]
    exact fields
  have buffer := view.after_ledger canonical outside
  have xReady : forwarded.locals.lookup (ofString "x") = some (.rStruct [.val (.word memoryCost), .val (.word expand)]) := by
    rw [locals]
    simpa [CallGas.callerPost, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "x" ≠ ofString "mcg" from by decide, show ofString "mcg" ≠ ofString "x" from by decide] using xCell
  have expansionArgs : evalListHOLFinite forwarded (h := fun address => Classical.propDecidable (forwarded.memaddrs address)) [.rfield 1 (localVar "x")] = some [.val (.word expand)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, xReady]
  have safe : Input.LocalPrefix (ofString "setup") (.call (some (none, none)) (ofString "extend_memory") [.rfield 1 (localVar "x")]) :=
    .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨ready, expansionRun, restRun, saved⟩ := safe.normal_continue forwarded inner continuation returned tailRun
  obtain ⟨extensionFits, clock, postView, extensionLocals, away⟩ :=
    MemoryExtend.call_normal forwarded ready frame base current capacity pointer scratch expand amount oldUsed [.rfield 1 (localVar "x")] buffer advance expansionArgs expansionRun
  obtain ⟨unusedFits, unusedClock, unusedView, budgetSame, usedSame⟩ :=
    MemoryExtend.call_sums forwarded ready frame base current capacity pointer scratch expand amount oldUsed [.rfield 1 (localVar "x")]
      buffer advance expansionArgs [] (by simp) (by simp) expansionRun
  have parentBudget : regularBudget ready.memory frame = regularBudget forwarded.memory frame := by
    simpa only [FrameSums.budget, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] using budgetSame
  have parentUsed : (wordAt ready.memory (frame + 184#64)).toNat = (wordAt forwarded.memory (frame + 184#64)).toNat := by
    simpa only [FrameSums.used, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] using usedSame
  have amortized := MemoryExtend.price_potential forwarded frame base current capacity pointer scratch expand amount oldUsed buffer advance
  have globals := congrArg PanSemStateFiniteExact.globals fields
  change forwarded.globals = source.globals at globals
  refine ⟨ready, inner, by omega, by rw [clock, forwardClock]; omega, postView, by rw [parentBudget]; exact budget,
    by rw [parentUsed]; exact debit, by rw [parentUsed]; omega, restRun, scope, by omega, ?_, ?_⟩
  · intro query owned notLength notCapacity notGas notUsed
    exact (away query owned notLength notCapacity).trans (outside query notGas notUsed)
  · intro key other
    rw [MemoryExtend.call_global_other forwarded ready frame base current capacity pointer scratch expand amount oldUsed
      [.rfield 1 (localVar "x")] buffer advance expansionArgs expansionRun key other, globals]

end InitECandidate.Solver.GasBudget.ForwardPrefix

#print axioms InitECandidate.Solver.GasBudget.ForwardPrefix.expansion_normal
