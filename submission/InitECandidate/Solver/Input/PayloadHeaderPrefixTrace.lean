import InitECandidate.Solver.Input.PayloadHeaderPrefixCost
import InitECandidate.Solver.Input.CallPrefixTrace
import InitECandidate.Solver.Input.PayloadHeaderPrefixControl

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack PanSemStateFiniteExact

/-- On every original payload_header outcome, derive its real block-length
caller after all eight allocations, stores, clears and the ommer hash, or
bound the earlier stopping path. No successful prefix is assumed. -/
theorem prefix_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code) (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source body=(outcome,post)) :
    (source.clock-post.clock≤1035 ∧ ∀ value,outcome≠some (.returned value)) ∨ ∃ current inner,CallPrefix.Execution source actions current ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤1035 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current lengthCall=(outcome,inner) := by
  rw [body_shape] at run
  have price:=prefix_cost source.code installed .skip 0 (ClockCost.skip source.code) source rfl
  rcases CallPrefix.priced_trace source post actions lengthCall 1035 price outcome run with stopped|reached
  · obtain ⟨spent,resultEq⟩:=stopped
    exact Or.inl ⟨spent,by intro value; rw [resultEq]; exact prefix_sink_never source value⟩
  · exact Or.inr reached

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.prefix_trace

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack PanSemStateFiniteExact

theorem prefix_frame_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code) (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source body=(outcome,post)) :
    (source.clock-post.clock≤1035 ∧ ∀ value,outcome≠some (.returned value)) ∨ ∃ current inner,CallPrefix.Execution source actions current ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤1035 ∧ CallPrefix.ScopeFrame post inner ∧
      evaluateHOLFiniteState current lengthCall=(outcome,inner) := by
  rw [body_shape] at run
  have price:=prefix_cost source.code installed .skip 0 (ClockCost.skip source.code) source rfl
  rcases CallPrefix.priced_frame_trace source post actions lengthCall 1035 price outcome run with stopped|reached
  · obtain ⟨spent,resultEq⟩:=stopped
    exact Or.inl ⟨spent,by intro value; rw [resultEq]; exact prefix_sink_never source value⟩
  · exact Or.inr reached

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.prefix_frame_trace
