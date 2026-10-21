import InitECandidate.Solver.Mpt.KeyToNibblesSpanLoops
import InitECandidate.Solver.Mpt.KeyToNibblesAnyCall
import InitECandidate.Solver.Input.IgnoredCallNormal

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine normal original converter returns0 and mutates only backing
words in the actual variable-length output, preserving every nonmemory
field apart from caller locals/clock. No input mapping/view is assumed. -/
theorem body_span_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (out : BitVec 64) (length : Nat)
    (small : length+4<2^64) (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    value=.val (.word 0#64) ∧ SpanFrame source target out (2*length) := by
  rw [body_shape] at normal
  obtain ⟨declared,inner,read,checked,continued,endpoint⟩:=Input.CallNormal.declaration_normal_entry source target "i" .one (.const 0#64) _ value normal
  have valueEq : declared=.val (.word 0#64):=Option.some.inj read.symm
  subst declared
  let current:=QueryBranch.bind source "i" 0#64
  have currentOut : current.locals.lookup (ofString "out")=some (.val (.word out)):=
    (bind_lookup_other source "i" "out" 0#64 (by decide)).trans outCell
  have currentN : current.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))):=
    (bind_lookup_other source "i" "n" 0#64 (by decide)).trans nCell
  have valid : Input.CounterFlow.StrideInvariant length current:=⟨0#64,bind_lookup_same _ _ _,currentN,by change 0≤length; omega⟩
  obtain ⟨answer,frame⟩:=loops_span_frame current inner out length small currentOut valid value continued
  exact ⟨answer,⟨by rw [endpoint]; exact frame.fields,by intro query outside; rw [endpoint]; exact frame.memory query outside⟩⟩

/-- The same physical frame at the real original ignored caller. Its actual
callee return, checked scalar result and restored caller locals are derived
from the observed normal call, not supplied as future-success premises. -/
theorem call_span_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (key out : BitVec 64) (length : Nat)
    (small : length+4<2^64) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (anyValues key (BitVec.ofNat 64 length) out))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "key_to_nibbles") arguments)=(none,post)) :
    SpanFrame source post out (2*length) := by
  obtain ⟨callee,called,keyCell,nCell,outCell⟩:=any_environment source.code.lookup key (BitVec.ofNat 64 length) out (original_code source.code installed)
  obtain ⟨positive,target,returned,bodyRun⟩:=Input.CallNormal.ignored_callee_return source post (ofString "key_to_nibbles") arguments _ body callee .one args called normal
  obtain ⟨valueEq,frame⟩:=body_span_frame (callEntryStateHOLFinite source callee) target out length small outCell nCell returned bodyRun
  rw [valueEq] at bodyRun
  have actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "key_to_nibbles") arguments)=(none,{target with locals:=source.locals}):=by
    rw [evaluateHOLFiniteState_call,args]
    simp only [called]
    rw [if_neg (show source.clock≠0 from by omega),bodyRun]
    simp [shapeOfHOLExact,shapeEqHOL]
  have postEq:=congrArg Prod.snd (normal.symm.trans actual)
  change post={target with locals:=source.locals} at postEq
  exact ⟨by rw [postEq]; exact frame.fields,by intro query outside; rw [postEq]; exact frame.memory query outside⟩

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.body_span_frame
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.call_span_frame
