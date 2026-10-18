import InitECandidate.Solver.GasBudget.DirectStackOpcode

namespace InitECandidate.Solver.GasBudget.DirectStackOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def Kind.label : Kind → String
  | .op_and => "op_and" | .op_or => "op_or" | .op_xor => "op_xor" | .op_not => "op_not"

def Kind.function (kind : Kind) : MlS := ofString kind.label

def Entry.call_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (entry : Entry source frame) (callee : HolFiniteMapExact MlS (ValueHOL 64)) : Entry (callEntryStateHOLFinite source callee) frame :=
  ⟨entry.base, entry.sp, entry.capacity, entry.ev, entry.popCode, entry.chargeCode, entry.pushCode, entry.pcCode,
    entry.spCell, entry.capCell, entry.baseMapped, entry.baseCell, entry.depthBound, entry.capBound, entry.gasCap, entry.separate⟩

/-- Actual ignored caller of the unchanged AND/OR/XOR/NOT helper. Its
available clocks, full real body execution and caller restoration are derived.
The final gas counter grows3 and stack depth stays within original capacity. -/
theorem call_normal (kind : Kind) (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (entry : Entry source frame)
    (code : source.code.lookup kind.function = some ([], kind.site.body, .one))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) kind.function []) = (none, target)) :
    kind.site.names.length + 4 ≤ source.clock ∧ target.clock = source.clock - (kind.site.names.length + 4) ∧
      target = {source with memory := target.memory, clock := source.clock - (kind.site.names.length + 4)} ∧
      regularBudget target.memory frame = regularBudget source.memory frame ∧
      (wordAt target.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + 3 ∧
      (wordAt target.memory (frame + 16#64)).toNat + kind.site.names.length = entry.sp.toNat + 1 ∧
      (wordAt target.memory (frame + 16#64)).toNat ≤ entry.capacity.toNat := by
  have raw : lookupCodeHOLExact source.code.lookup kind.function [] = some (kind.site.body, (fun _ => none), .one) := by
    simp [lookupCodeHOLExact, code]
  obtain ⟨callee, called, locals⟩ := CodeEnvironment.finite_lookup source.code.lookup kind.function [] kind.site.body (fun _ => none) .one raw
  obtain ⟨positive, post, value, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target kind.function [] [] kind.site.body callee .one rfl called normal
  let incoming := entry.call_entry source frame callee
  obtain ⟨fits, returned, clock, frameEq, budget, credit, depth, depthBound⟩ := body_normal kind (callEntryStateHOLFinite source callee) post frame incoming value bodyRun
  rw [returned] at bodyRun
  have sub : source.clock - 1 - (kind.site.names.length + 3) = source.clock - (kind.site.names.length + 4) := by omega
  have callerFrame : emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - (kind.site.names.length + 4)} := by
    change emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - 1 - (kind.site.names.length + 3)} at frameEq
    simpa only [sub] using frameEq
  have actual := ignored_return source post kind.function [] [] kind.site.body callee (kind.site.names.length + 4) rfl called positive bodyRun callerFrame
  have same := congrArg Prod.snd (normal.symm.trans actual)
  change target = {source with memory := post.memory, clock := source.clock - (kind.site.names.length + 4)} at same
  refine ⟨by change kind.site.names.length + 3 ≤ source.clock - 1 at fits; omega, by rw [same], ?_, ?_, ?_, ?_, ?_⟩
  · rw [same]
  · rw [same]; exact budget
  · rw [same]; exact credit
  · rw [same]; exact depth
  · rw [same]; exact depthBound

end InitECandidate.Solver.GasBudget.DirectStackOpcode

#print axioms InitECandidate.Solver.GasBudget.DirectStackOpcode.Entry.call_entry
#print axioms InitECandidate.Solver.GasBudget.DirectStackOpcode.call_normal
