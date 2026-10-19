import InitECandidate.Solver.GasBudget.MemoryExtendCall

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

theorem expanded_global_other (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer expand : BitVec 64) (key : MlS) (other : key ≠ ofString "frame_mem_ptr") :
    (expandedState source frame base length capacity pointer expand).globals.lookup key = source.globals.lookup key := by
  unfold expandedState capacityState
  split
  · simp [growthState, Arenas.post, Arenas.pointerName, HolFiniteMapExact.update, FUPDATE, other, Ne.symm other, emptyLocalsHOLFinite]
  · rfl

set_option maxHeartbeats 1000000 in
theorem call_global_other (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch expand amount : BitVec 64) (used : Nat) (arguments : List (ExpHOL 64))
    (view : View source frame base length capacity pointer scratch)
    (advance : MemoryExpansionCost.Advance length expand amount used)
    (argsRead : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word expand)])
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "extend_memory") arguments) = (none, post))
    (key : MlS) (other : key ≠ ofString "frame_mem_ptr") : post.globals.lookup key = source.globals.lookup key := by
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
  obtain ⟨value, funded, clock, targetView, footprint, away⟩ := body_normal (callEntryStateHOLFinite source callee) target
    frame base length capacity pointer scratch expand amount used returned (view.after_erase rfl) advance binding bodyRun
  have globals := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals.lookup key) footprint
  rw [postEq]
  change target.globals.lookup key = source.globals.lookup key
  change target.globals.lookup key = (if expand = 0#64 then callEntryStateHOLFinite source callee else
    expandedState (callEntryStateHOLFinite source callee) frame base length capacity pointer expand).globals.lookup key at globals
  rw [globals]
  by_cases zero : expand = 0#64
  · rw [if_pos zero]; rfl
  · rw [if_neg zero]
    exact expanded_global_other (callEntryStateHOLFinite source callee) frame base length capacity pointer expand key other

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.expanded_global_other
#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.call_global_other
