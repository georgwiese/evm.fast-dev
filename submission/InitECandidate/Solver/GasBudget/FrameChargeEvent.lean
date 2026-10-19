import InitECandidate.Solver.GasBudget.ChargeEvent
import InitECandidate.Solver.GasBudget.AddressMaskedProgram

namespace InitECandidate.Solver.GasBudget
open Flapjack PanSemStateFiniteExact MemoryWriter

/-- A real first-charge event allowing the original CALL address scratch
writes as well as SP/gas fields. The older narrow ChargeEvent excludes these
writes and cannot represent the complete unchanged CALL entry. -/
structure FrameChargeEvent (source ready : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64) (paid amount : Nat) : Prop where
  fits : paid ≤ source.clock
  clock : ready.clock = source.clock - paid
  fields : emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with memory := ready.memory, clock := ready.clock}
  budget : regularBudget ready.memory frame = regularBudget source.memory frame
  credit : (wordAt ready.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + amount
  positive : 0 < amount
  outside : ∀ query, query ≠ frame + 16#64 → query ≠ frame + 64#64 → query ≠ frame + 184#64 →
    BytesAway (frame + 240#64) query 20 → ready.memory query = source.memory query

theorem ChargeEvent.prepend_frame {source middle ready : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame : BitVec 64} {first paid amount : Nat}
    (event : ChargeEvent middle ready frame paid amount)
    (funded : first ≤ source.clock) (clock : middle.clock = source.clock - first)
    (fields : emptyLocalsHOLFinite middle = emptyLocalsHOLFinite {source with memory := middle.memory, clock := middle.clock})
    (budget : regularBudget middle.memory frame = regularBudget source.memory frame)
    (used : middle.memory (frame + 184#64) = source.memory (frame + 184#64))
    (outside : ∀ query, query ≠ frame + 16#64 → BytesAway (frame + 240#64) query 20 → middle.memory query = source.memory query) :
    FrameChargeEvent source ready frame (first + paid) amount := by
  have lift := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    emptyLocalsHOLFinite {state with memory := ready.memory, clock := ready.clock}) fields
  refine ⟨?_, by rw [event.clock, clock]; omega, event.fields.trans lift, event.budget.trans budget, ?_, event.positive, ?_⟩
  · have fits := event.fits
    rw [clock] at fits
    omega
  · rw [event.credit]
    simp only [wordAt, used]
  · intro query notSP notGas notUsed away
    exact (event.outside query notSP notGas notUsed).trans (outside query notSP away)

end InitECandidate.Solver.GasBudget

#print axioms InitECandidate.Solver.GasBudget.ChargeEvent.prepend_frame
