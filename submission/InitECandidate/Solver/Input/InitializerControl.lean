import InitECandidate.Solver.Input.InitializerAllocations
import InitECandidate.Solver.WitnessRadix.KeccakAbsorbState

namespace InitECandidate.Solver.Input.InitializerAllocations
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix

/-- Fields unaffected by pure initialization allocations and ordinary stores. -/
def context (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  emptyLocalsHOLFinite {source with globals := HolFiniteMapExact.empty, memory := (fun _ => .word 0#64), clock := 0}

theorem context_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (clock : Nat) :
    context {source with clock := clock} = context source := rfl

theorem context_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (memory : WordWrites.Memory) :
    context {source with memory := memory} = context source := rfl

theorem context_code (source : PanSemStateFiniteExact 64 Guest.HostMemory) : (context source).code = source.code := rfl
theorem context_domain (source : PanSemStateFiniteExact 64 Guest.HostMemory) : (context source).memaddrs = source.memaddrs := rfl
theorem context_oracle (source : PanSemStateFiniteExact 64 Guest.HostMemory) : (context source).ffi.oracle = source.ffi.oracle := rfl

theorem template_context (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cursor : Nat) (actions : List Action) : context (template source cursor actions) = context source := by
  induction actions generalizing source cursor with
  | nil => rfl
  | cons action rest ih => exact (ih (reserve source action cursor) (cursor + action.bytes)).trans (by rfl)

/-- The fixed allocation plan changes only its recorded global bindings.
Erasing local work, clock, memory and accumulated events commutes with it. -/
theorem template_hash_control (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cursor : Nat) (actions : List Action)
    (same : KeccakAbsorb.hashControl target = KeccakAbsorb.hashControl source) :
    KeccakAbsorb.hashControl (template target cursor actions) = KeccakAbsorb.hashControl (template source cursor actions) := by
  induction actions generalizing source target cursor with
  | nil => exact same
  | cons action rest ih =>
    have next : KeccakAbsorb.hashControl (reserve target action cursor) = KeccakAbsorb.hashControl (reserve source action cursor) :=
      congrArg (fun state => reserve state action cursor) same
    exact ih (reserve source action cursor) (reserve target action cursor) (cursor + action.bytes) next

end InitECandidate.Solver.Input.InitializerAllocations

#print axioms InitECandidate.Solver.Input.InitializerAllocations.template_context
#print axioms InitECandidate.Solver.Input.InitializerAllocations.context_clock
#print axioms InitECandidate.Solver.Input.InitializerAllocations.context_memory
#print axioms InitECandidate.Solver.Input.InitializerAllocations.context_code
#print axioms InitECandidate.Solver.Input.InitializerAllocations.context_domain
#print axioms InitECandidate.Solver.Input.InitializerAllocations.context_oracle
#print axioms InitECandidate.Solver.Input.InitializerAllocations.template_hash_control
