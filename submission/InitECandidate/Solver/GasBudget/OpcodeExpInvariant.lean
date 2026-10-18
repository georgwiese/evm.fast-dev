import InitECandidate.Solver.GasBudget.DispatchExpNormal

namespace InitECandidate.Solver.GasBudget.OpcodeExp
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def call_next_entry (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (entry : DirectStackOpcode.Entry source frame) (owned : DirectStackOpcode.HeaderApart frame entry.base entry.capacity.toNat)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "op_exp") []) = (none, target)) : DirectStackOpcode.Entry target frame := by
  have effects : target = {source with memory := target.memory, clock := target.clock} ∧
      regularBudget target.memory frame = regularBudget source.memory frame ∧
      (wordAt target.memory (frame + 16#64)).toNat ≤ entry.capacity.toNat ∧
      DirectStackOpcode.Footprint source.memory target.memory frame entry.base entry.sp 2 ∧
      2 ≤ entry.sp.toNat := by
    obtain ⟨bytes, paid, small, bounded, fits, clock, canonical, budget, credit, depth, depthBound, footprint, popsFit⟩ := call_normal source target frame entry installed normal
    exact ⟨by simpa only [clock] using canonical, budget, depthBound, footprint, popsFit⟩
  obtain ⟨canonical, budget, depthBound, footprint, popsFit⟩ := effects
  exact DirectStackOpcode.Entry.after_footprint source target frame entry 2 (by decide) popsFit owned canonical budget depthBound footprint

def dispatch_next_entry (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (entry : DirectStackOpcode.Entry source frame) (owned : DirectStackOpcode.HeaderApart frame entry.base entry.capacity.toNat)
    (installed : Input.OriginalCode.Installed source.code) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word 10#64)])
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "op_dispatch") arguments) = (none, target)) : DirectStackOpcode.Entry target frame := by
  have effects : target = {source with memory := target.memory, clock := target.clock} ∧
      regularBudget target.memory frame = regularBudget source.memory frame ∧
      (wordAt target.memory (frame + 16#64)).toNat ≤ entry.capacity.toNat ∧
      DirectStackOpcode.Footprint source.memory target.memory frame entry.base entry.sp 2 ∧
      2 ≤ entry.sp.toNat := by
    obtain ⟨bytes, paid, small, bounded, fits, clock, canonical, budget, credit, depth, depthBound, footprint, popsFit⟩ :=
      OpcodeDispatch.exp_call_normal source target frame entry installed arguments args normal
    exact ⟨by simpa only [clock] using canonical, budget, depthBound, footprint, popsFit⟩
  obtain ⟨canonical, budget, depthBound, footprint, popsFit⟩ := effects
  exact DirectStackOpcode.Entry.after_footprint source target frame entry 2 (by decide) popsFit owned canonical budget depthBound footprint

end InitECandidate.Solver.GasBudget.OpcodeExp

#print axioms InitECandidate.Solver.GasBudget.OpcodeExp.call_next_entry
#print axioms InitECandidate.Solver.GasBudget.OpcodeExp.dispatch_next_entry
