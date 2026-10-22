import InitECandidate.Solver.Input.Copy32SpanLoops
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.IgnoredCallData
import InitECandidate.Solver.WitnessRadix.CopyGeneralCode

namespace InitECandidate.Solver.Input.Copy32Span
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch CounterFlow

/-- Complete real normal memcpy32 body: actual reads/writes supply the
return and frame. Neither source/destination mapping nor allocation room
is an entry premise. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64)
    (dstCell : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word 32#64)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source Copy32.body=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ Frame source post dst 32:=by
  rw [Copy32.body_shape] at normal
  obtain ⟨inner,remaining,endpoint⟩:=declaration_return_word source post "i" (.const 0#64) 0#64 _ value rfl normal
  let entry:=bind source "i" 0#64
  have entryDst : entry.locals.lookup (ofString "dst")=some (.val (.word dst)):=
    (bind_lookup_other source "i" "dst" 0#64 (by decide)).trans dstCell
  have initial : StrideInvariant 32 entry:=⟨0#64,bind_lookup_same _ _ _,(bind_lookup_other source "i" "n" 0#64 (by decide)).trans lengthCell,by decide⟩
  obtain ⟨large,word,byte,tail⟩:=loops source.code
  have aligned:=Normal.sequence source.code Copy32.loop32 Copy32.loopWord large word
  have choice:=Normal.conditional source.code Copy32.alignment _ .skip aligned (Normal.skip source.code)
  obtain ⟨middle,choiceRun,byteTail⟩:=sequence_returned entry inner _ _ value (fun returned=>(choice.summary entry).2.1 returned) remaining
  obtain ⟨front,middleDst,middleValid⟩:=choice.run entry middle dst rfl entryDst initial choiceRun
  have middleCode:=(evaluation_fields entry middle _ none choiceRun).2.2.2
  obtain ⟨last,byteRun,tailReturn⟩:=sequence_returned middle inner _ _ value (fun returned=>(byte.summary middle).2.1 returned) byteTail
  obtain ⟨bytesFrame,lastDst,lastValid⟩:=byte.run middle last dst middleCode middleDst middleValid byteRun
  have lastCode:=(evaluation_fields middle last _ none byteRun).2.2.2.trans middleCode
  obtain ⟨finish,tailRun,returned⟩:=sequence_returned last inner _ _ value (fun returned=>(tail.summary last).2.1 returned) tailReturn
  obtain ⟨tailFrame,finishDst,finishValid⟩:=tail.run last finish dst lastCode lastDst lastValid tailRun
  obtain ⟨read,innerEq⟩:=return_normal finish inner (.const 0#64) value returned
  have valueEq : value=.val (.word 0#64):=Option.some.inj read.symm
  have full:=(front.trans entry middle last dst 32 bytesFrame).trans entry last finish dst 32 tailFrame
  refine ⟨valueEq,⟨?_,?_⟩⟩
  · rw [endpoint,innerEq]; exact full.fields
  · intro query away
    rw [endpoint,innerEq]
    exact full.memory query away

/-- Whole original ignored copy call at its actual operands. The genuine
ABI supplies its destination/length words and restores all caller locals. -/
theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (dst src : BitVec 64)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (CopyGeneral.values dst src 32))
    (installed : OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") arguments)=(none,post)) :
    Frame source post dst 32 ∧ post.locals=source.locals:=by
  obtain ⟨callee,called,dstCell,srcCell,lengthCell⟩:=CopyGeneral.environment source.code.lookup dst src 32 (CopyGeneral.original_code source.code installed)
  obtain ⟨funded,values,actual,actualCallee,shape,target,value,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩:=CallNormal.ignored_data source post (ofString "memcpy") arguments normal
  have sameValues : values=CopyGeneral.values dst src 32:=Option.some.inj (actualArgs.symm.trans args)
  subst values
  have same : (actual,actualCallee,shape)=(Copy32.body,callee,.one):=Option.some.inj (actualCalled.symm.trans called)
  cases same
  obtain ⟨valueEq,frame⟩:=body_normal (callEntryStateHOLFinite source callee) target dst dstCell lengthCell value bodyRun
  refine ⟨⟨?_,?_⟩,?_⟩
  · rw [endpoint]; exact frame.fields
  · intro query away
    rw [endpoint]
    exact frame.memory query away
  · rw [endpoint]

theorem Frame.globals {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {dst : BitVec 64} {length : Nat}
    (frame : Frame source target dst length) : target.globals=source.globals:=by
  have fields:=congrArg PanSemStateFiniteExact.globals frame.fields
  exact fields

theorem Frame.domain {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {dst : BitVec 64} {length : Nat}
    (frame : Frame source target dst length) : target.memaddrs=source.memaddrs:=by
  have fields:=congrArg PanSemStateFiniteExact.memaddrs frame.fields
  exact fields

theorem Frame.endian {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {dst : BitVec 64} {length : Nat}
    (frame : Frame source target dst length) : target.be=source.be:=by
  have fields:=congrArg PanSemStateFiniteExact.be frame.fields
  exact fields

end InitECandidate.Solver.Input.Copy32Span

#print axioms InitECandidate.Solver.Input.Copy32Span.body_normal
#print axioms InitECandidate.Solver.Input.Copy32Span.call_normal
#print axioms InitECandidate.Solver.Input.Copy32Span.Frame.globals
#print axioms InitECandidate.Solver.Input.Copy32Span.Frame.domain
#print axioms InitECandidate.Solver.Input.Copy32Span.Frame.endian
