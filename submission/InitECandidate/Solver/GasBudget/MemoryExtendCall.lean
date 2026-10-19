import InitECandidate.Solver.GasBudget.MemoryExtendBody
import InitECandidate.Solver.Input.IgnoredCallData
import InitECandidate.Solver.Input.UnaryCallData

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch expand amount : BitVec 64) (used : Nat) (arguments : List (ExpHOL 64))
    (view : View source frame base length capacity pointer scratch)
    (advance : MemoryExpansionCost.Advance length expand amount used)
    (argsRead : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word expand)])
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "extend_memory") arguments) = (none, post)) :
    price length capacity expand + 1 ≤ source.clock ∧
      post.clock = source.clock - (price length capacity expand + 1) ∧
      View post frame base (newLength length expand) (nextCapacity length capacity expand) (base + nextCapacity length capacity expand) scratch ∧
      post.locals = source.locals ∧
      (∀ query, Arenas.Outside base scratch query → query ≠ frame + 32#64 → query ≠ frame + 40#64 → post.memory query = source.memory query) := by
  obtain ⟨positive, values, actual, callee, shape, target, returned, args, called, bodyRun, checked, postEq, fields⟩ :=
    Input.CallNormal.ignored_data source post (ofString "extend_memory") arguments normal
  have valuesEq := Option.some.inj (args.symm.trans argsRead)
  rw [valuesEq] at called
  obtain ⟨argument, argumentsEq, bodyEq, shapeEq, typed, binding⟩ :=
    Input.CallNormal.unary_lookup_data source.code.lookup (ofString "extend_memory") (ofString "expand_by") .one body .one
      (original_code source.code view.installed) [.val (.word expand)] actual callee shape called
  have argumentEq : argument = .val (.word expand) := (List.cons.inj argumentsEq).1.symm
  rw [argumentEq] at binding
  rw [bodyEq] at bodyRun
  have entryView : View (callEntryStateHOLFinite source callee) frame base length capacity pointer scratch := view.after_erase rfl
  obtain ⟨value, funded, clock, targetView, footprint, away⟩ :=
    body_normal (callEntryStateHOLFinite source callee) target frame base length capacity pointer scratch expand amount used returned entryView advance binding bodyRun
  have entryClock : (callEntryStateHOLFinite source callee).clock = source.clock - 1 := rfl
  rw [entryClock] at funded clock
  have postClock : post.clock = source.clock - (price length capacity expand + 1) := by
    rw [postEq]
    change target.clock = _
    rw [clock]
    omega
  refine ⟨by omega, postClock, targetView.after_erase (by rw [postEq]; rfl), ?_, ?_⟩
  · rw [postEq]
  · intro query outside notLength notCapacity
    rw [postEq]
    exact away query outside notLength notCapacity

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.call_normal
