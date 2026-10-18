import InitECandidate.Solver.GasBudget.DispatchArithmeticStack

namespace InitECandidate.Solver.GasBudget.ArithmeticStackOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def call_next_entry (kind : Kind) (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (entry : DirectStackOpcode.Entry source frame) (owned : DirectStackOpcode.HeaderApart frame entry.base entry.capacity.toNat)
    (environment : ArithmeticEffects.Environment source.code)
    (code : source.code.lookup kind.function = some ([], kind.site.body, .one))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) kind.function []) = (none, target)) : DirectStackOpcode.Entry target frame := by
  have effects : target = {source with memory := target.memory, clock := target.clock} ∧
      regularBudget target.memory frame = regularBudget source.memory frame ∧
      (wordAt target.memory (frame + 16#64)).toNat ≤ entry.capacity.toNat ∧
      DirectStackOpcode.Footprint source.memory target.memory frame entry.base entry.sp kind.site.names.length ∧
      kind.site.names.length ≤ entry.sp.toNat := by
    obtain ⟨paid, bounded, fits, clock, canonical, budget, credit, depth, depthBound, footprint, popsFit⟩ := call_normal kind source target frame entry environment code normal
    exact ⟨by simpa only [clock] using canonical, budget, depthBound, footprint, popsFit⟩
  obtain ⟨canonical, budget, depthBound, footprint, popsFit⟩ := effects
  exact DirectStackOpcode.Entry.after_footprint source target frame entry kind.site.names.length (by cases kind <;> decide) popsFit owned canonical budget depthBound footprint

def dispatch_next_entry (kind : Kind) (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (entry : DirectStackOpcode.Entry source frame) (owned : DirectStackOpcode.HeaderApart frame entry.base entry.capacity.toNat)
    (environment : ArithmeticEffects.Environment source.code) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word kind.opcode)])
    (dispatchCode : source.code.lookup (ofString "op_dispatch") = some (OpcodeDispatch.formals, OpcodeDispatch.body, .one))
    (code : source.code.lookup kind.function = some ([], kind.site.body, .one))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "op_dispatch") arguments) = (none, target)) : DirectStackOpcode.Entry target frame := by
  have effects : target = {source with memory := target.memory, clock := target.clock} ∧
      regularBudget target.memory frame = regularBudget source.memory frame ∧
      (wordAt target.memory (frame + 16#64)).toNat ≤ entry.capacity.toNat ∧
      DirectStackOpcode.Footprint source.memory target.memory frame entry.base entry.sp kind.site.names.length ∧
      kind.site.names.length ≤ entry.sp.toNat := by
    obtain ⟨paid, bounded, fits, clock, canonical, budget, credit, depth, depthBound, footprint, popsFit⟩ :=
      OpcodeDispatch.arithmetic_stack_call_normal kind source target frame entry environment arguments args dispatchCode code normal
    exact ⟨by simpa only [clock] using canonical, budget, depthBound, footprint, popsFit⟩
  obtain ⟨canonical, budget, depthBound, footprint, popsFit⟩ := effects
  exact DirectStackOpcode.Entry.after_footprint source target frame entry kind.site.names.length (by cases kind <;> decide) popsFit owned canonical budget depthBound footprint

end InitECandidate.Solver.GasBudget.ArithmeticStackOpcode

#print axioms InitECandidate.Solver.GasBudget.ArithmeticStackOpcode.call_next_entry
#print axioms InitECandidate.Solver.GasBudget.ArithmeticStackOpcode.dispatch_next_entry
