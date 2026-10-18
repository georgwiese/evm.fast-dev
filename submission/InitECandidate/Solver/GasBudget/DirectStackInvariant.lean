import InitECandidate.Solver.GasBudget.DirectStackFootprint
import InitECandidate.Solver.GasBudget.DispatchDirectStack

namespace InitECandidate.Solver.GasBudget.DirectStackOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Rebuild the physical stack/code/gas entry model from actual effects.
The next sp is the actual stored word, not a fresh assumed stack model. -/
def Entry.advance (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (entry : Entry source frame)
    (canonical : target = {source with memory := target.memory, clock := target.clock})
    (budget : regularBudget target.memory frame = regularBudget source.memory frame)
    (capCell : target.memory (frame + 232#64) = .word entry.capacity)
    (baseCell : target.memory (frame + 8#64) = .word entry.base)
    (depthBound : (wordAt target.memory (frame + 16#64)).toNat ≤ entry.capacity.toNat) : Entry target frame :=
  { base := entry.base
    sp := wordAt target.memory (frame + 16#64)
    capacity := entry.capacity
    ev := by rw [canonical]; exact entry.ev
    popCode := by rw [canonical]; exact entry.popCode
    chargeCode := by rw [canonical]; exact entry.chargeCode
    pushCode := by rw [canonical]; exact entry.pushCode
    pcCode := by rw [canonical]; exact entry.pcCode
    spCell := by
      cases actual : target.memory (frame + 16#64) with
      | word word => simp only [wordAt, actual, WitnessRadix.MemoryBytes.wordBits]
    capCell := capCell
    baseMapped := by rw [canonical]; exact entry.baseMapped
    baseCell := baseCell
    depthBound := depthBound
    capBound := entry.capBound
    gasCap := by rw [budget]; exact entry.gasCap
    separate := entry.separate }

def Entry.after_footprint (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (entry : Entry source frame) (pops : Nat) (positive : 0 < pops) (popsFit : pops ≤ entry.sp.toNat)
    (owned : HeaderApart frame entry.base entry.capacity.toNat)
    (canonical : target = {source with memory := target.memory, clock := target.clock})
    (budget : regularBudget target.memory frame = regularBudget source.memory frame)
    (depthBound : (wordAt target.memory (frame + 16#64)).toNat ≤ entry.capacity.toNat)
    (footprint : Footprint source.memory target.memory frame entry.base entry.sp pops) : Entry target frame := by
  have header := footprint.header_words source.memory target.memory frame entry.base entry.sp entry.capacity.toNat pops entry.depthBound positive popsFit owned
  have capCell : target.memory (frame + 232#64) = .word entry.capacity :=
    (header 232 (by decide) (by decide) (by decide) (by decide) (by decide)).trans entry.capCell
  have baseCell : target.memory (frame + 8#64) = .word entry.base :=
    (header 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans entry.baseCell
  exact Entry.advance source target frame entry canonical budget capCell baseCell depthBound

/-- The actual helper caller establishes the next physical entry model.
Owned frame/stack separation remains a current-state geometric obligation. -/
def call_next_entry (kind : Kind) (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (entry : Entry source frame) (owned : HeaderApart frame entry.base entry.capacity.toNat)
    (code : source.code.lookup kind.function = some ([], kind.site.body, .one))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) kind.function []) = (none, target)) : Entry target frame := by
  obtain ⟨fits, clock, canonical, budget, credit, depth, depthBound, footprint, popsFit⟩ := call_normal kind source target frame entry code normal
  have same : target = {source with memory := target.memory, clock := target.clock} := by simpa only [clock] using canonical
  exact Entry.after_footprint source target frame entry kind.site.names.length (by cases kind <;> decide) popsFit owned same budget depthBound footprint

/-- The actual original dispatcher also establishes that model, so a later
iteration can use actual post-state code, stack and gas facts. -/
def dispatch_next_entry (kind : Kind) (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (entry : Entry source frame) (owned : HeaderApart frame entry.base entry.capacity.toNat) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word kind.opcode)])
    (dispatchCode : source.code.lookup (ofString "op_dispatch") = some (OpcodeDispatch.formals, OpcodeDispatch.body, .one))
    (code : source.code.lookup kind.function = some ([], kind.site.body, .one))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "op_dispatch") arguments) = (none, target)) : Entry target frame := by
  obtain ⟨fits, clock, canonical, budget, credit, depth, depthBound, footprint, popsFit⟩ := OpcodeDispatch.direct_stack_call_normal kind source target frame entry arguments args dispatchCode code normal
  have same : target = {source with memory := target.memory, clock := target.clock} := by simpa only [clock] using canonical
  exact Entry.after_footprint source target frame entry kind.site.names.length (by cases kind <;> decide) popsFit owned same budget depthBound footprint

end InitECandidate.Solver.GasBudget.DirectStackOpcode

#print axioms InitECandidate.Solver.GasBudget.DirectStackOpcode.Entry.advance
#print axioms InitECandidate.Solver.GasBudget.DirectStackOpcode.Entry.after_footprint
#print axioms InitECandidate.Solver.GasBudget.DirectStackOpcode.call_next_entry
#print axioms InitECandidate.Solver.GasBudget.DirectStackOpcode.dispatch_next_entry
