import InitECandidate.Solver.Input.WordTableFields
import InitECandidate.Solver.WitnessRadix.ZeroCost

namespace InitECandidate.Solver.Input.InitializerZeroBuffer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def call (action : InitializerAllocations.Action) : ProgHOL 64 :=
  .call (some (none,none)) (ofString "memzero") [.var .global (ofString action.name),.const (BitVec.ofNat 64 action.bytes)]
def program (action : InitializerAllocations.Action) (tail : ProgHOL 64) := InitializerAllocations.withTail [action] (.seq (call action) tail)
def cost (action : InitializerAllocations.Action) := Zero.price action.bytes + 2
def template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (action : InitializerAllocations.Action) :=
  let allocated := InitializerAllocations.template source cursor [action]
  {allocated with memory := Zero.finalMemory allocated.memory (BitVec.ofNat 64 cursor) action.bytes}

theorem execute_prefix (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (action : InitializerAllocations.Action) (tail : ProgHOL 64)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (valid : InitializerAllocations.Valid action) (domain : source.memaddrs = InitE.ordinaryDomain)
    (lower : 2701131776 ≤ cursor) (room : cursor + action.bytes ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : cost action ≤ source.clock) :
    evaluateHOLFiniteState source (program action tail) =
      evaluateHOLFiniteState {template source cursor action with clock := source.clock - cost action} tail := by
  have allocated := InitializerAllocations.execute_prefix source cursor [action] (.seq (call action) tail) installed scalars heap
    (by intro current member; have same := List.mem_singleton.mp member; subst current; exact valid)
    (by simpa only [InitializerAllocations.totalBytes,Nat.add_zero] using room) aligned (by change 1 ≤ source.clock; unfold cost at enough; omega)
  let ready := {InitializerAllocations.template source cursor [action] with clock := source.clock - 1}
  have context : InitializerAllocations.context ready = InitializerAllocations.context source :=
    (InitializerAllocations.context_clock _ _).trans (InitializerAllocations.template_context source cursor [action])
  have currentInstalled := InitializerAllocations.installed_of_context source ready context installed
  have currentDomain := (InitializerAllocations.domain_of_context source ready context).trans domain
  have binding : ready.globals.lookup (ofString action.name) = some (.val (.word (BitVec.ofNat 64 cursor))) := WordTableInitialization.allocated_binding source cursor action
  have args : evalListHOLFinite ready (h := fun query => Classical.propDecidable (ready.memaddrs query))
      [.var .global (ofString action.name),.const (BitVec.ofNat 64 action.bytes)] = some (Zero.values (BitVec.ofNat 64 cursor) action.bytes) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,binding,Zero.values]
  have number : (BitVec.ofNat 64 cursor).toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have arena : AllocatedBytes.Arena (BitVec.ofNat 64 cursor) action.bytes := ⟨by rw [number]; exact lower,by rw [number]; exact room⟩
  have pointerAligned : (BitVec.ofNat 64 cursor).toNat % 8 = 0 := by rw [number]; exact aligned
  have cleared := Zero.call_execute ready _ (BitVec.ofNat 64 cursor) action.bytes args (Zero.original_code ready.code currentInstalled)
    (by omega) valid.aligned pointerAligned
    (by intro offset inside multiple; exact AllocatedBytes.word_mapped ready _ action.bytes offset currentDomain arena (by omega) pointerAligned multiple)
    (by change Zero.price action.bytes + 1 ≤ source.clock - 1; unfold cost at enough; omega)
  have clock : source.clock - 1 - (Zero.price action.bytes + 1) = source.clock - cost action := by unfold cost; omega
  have zeroRun : evaluateHOLFiniteState ready (call action) = (none,{template source cursor action with clock := source.clock - cost action}) := by
    simpa only [call,ready,template,clock] using cleared
  rw [program,allocated]
  change evaluateHOLFiniteState ready (.seq (call action) tail) = _
  exact StateSteps.next_sequence ready _ _ _ zeroRun (by change source.clock - cost action ≤ source.clock - 1; unfold cost; omega)

theorem template_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (action : InitializerAllocations.Action) :
    InitializerAllocations.context (template source cursor action) = InitializerAllocations.context source := by
  unfold template
  rw [InitializerAllocations.context_memory,InitializerAllocations.template_context]

theorem template_control (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (action : InitializerAllocations.Action) :
    KeccakAbsorb.hashControl (template source cursor action) = KeccakAbsorb.hashControl (InitializerAllocations.template source cursor [action]) := rfl

theorem template_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (action : InitializerAllocations.Action) (clock : Nat) :
    (template source cursor action).clock = source.clock ∧ template {source with clock := clock} cursor action = {template source cursor action with clock := clock} := by
  constructor
  · exact InitializerAllocations.template_clock_value source cursor [action]
  · unfold template
    rw [InitializerAllocations.template_clock source cursor [action] clock]

end InitECandidate.Solver.Input.InitializerZeroBuffer

#print axioms InitECandidate.Solver.Input.InitializerZeroBuffer.execute_prefix
#print axioms InitECandidate.Solver.Input.InitializerZeroBuffer.template_context
#print axioms InitECandidate.Solver.Input.InitializerZeroBuffer.template_control
#print axioms InitECandidate.Solver.Input.InitializerZeroBuffer.template_clock
