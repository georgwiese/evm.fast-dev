import InitECandidate.Solver.Mpt.NibbleKeyAllocation
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.IgnoredCallTarget
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Mpt.NibbleKey
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def output (pointer : BitVec 64) (length : Nat) : ValueHOL 64:=
  .rStruct [.val (.word pointer),.val (.word (BitVec.ofNat 64 (2*length)))]

/-- The actual unsecured converter tail returns its fresh pointer/length,
physical nibble view and precise allocation footprint. Its input and output
mapping follow from current ordinary-memory arenas and allocation order. -/
theorem tail_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key out : BitVec 64) (length : Nat)
    (small : length≤32) (installed : Input.OriginalCode.Installed source.code)
    (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false)
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 length))))
    (outCell : source.locals.lookup (ofString "nb2")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena key length) (outputArena : AllocatedBytes.Arena out (2*length))
    (aligned : out.toNat%8=0) (before : key.toNat+length≤out.toNat)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source tail=(some (.returned value),target)) :
    value=output out length ∧ TrieWalk.KeyView target.memory target.memaddrs target.be out (2*length) ∧
      source.clock-target.clock≤length/4+4 ∧ KeyToNibbles.writeMetadata target=KeyToNibbles.writeMetadata source ∧
      ∀ query : BitVec 64,query.toNat<out.toNat ∨ out.toNat+2*length≤query.toNat→target.memory query=source.memory query := by
  rw [tail] at normal
  obtain ⟨middle,convertRun,returnRun⟩:=Input.sequence_returned source target convert (.return result) value
    (Input.NoReturn.ignored_call (ofString "key_to_nibbles") convertArguments source) normal
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) convertArguments=
      some (KeyToNibbles.anyValues key (BitVec.ofNat 64 length) out):=by
    simp [convertArguments,KeyToNibbles.anyValues,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,keyCell,lengthCell,outCell]
  obtain ⟨callee,called,childKey,childLength,childOut⟩:=KeyToNibbles.any_environment source.code.lookup key (BitVec.ofNat 64 length) out
    (KeyToNibbles.original_code source.code installed)
  obtain ⟨funded,childTarget,returned,childRun⟩:=Input.CallNormal.ignored_callee_return source middle (ofString "key_to_nibbles") convertArguments _
    KeyToNibbles.body callee .one args called convertRun
  obtain ⟨answer,view,cost,frame⟩:=KeyToNibbles.small_body_normal (callEntryStateHOLFinite source callee) childTarget key out length small
    childKey childOut childLength little (by have upper:=outputArena.upper; omega)
    (fun offset inside=>AllocatedBytes.byte_mapped source key length offset domain inputArena inside)
    (fun offset inside=>AllocatedBytes.byte_mapped source out (2*length) offset domain outputArena inside)
    (by
      intro left leftInside right rightInside same
      have keyNumber:=byteAddress_toNat key left (by have upper:=inputArena.upper; omega)
      have outNumber:=byteAddress_toNat out right (by have upper:=outputArena.upper; omega)
      have equal:=congrArg BitVec.toNat same
      rw [keyNumber,outNumber] at equal
      omega) returned childRun
  have middleEq:=Input.CallNormal.ignored_target source middle (ofString "key_to_nibbles") convertArguments _ KeyToNibbles.body callee .one
    args called returned childTarget childRun convertRun
  have nextOut : middle.locals.lookup (ofString "nb2")=some (.val (.word out)):=by rw [middleEq]; exact outCell
  have nextLength : middle.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 length))):=by rw [middleEq]; exact lengthCell
  have actual : eval middle result=some (output out length):=by
    simp [eval,result,amount,output,evalHOLExact,evalListHOLExact,localVar,toExact,nextOut,nextLength,panOpHOL,
      valueIsWord,valueWord,BitVec.ofNat_mul]
  obtain ⟨read,targetEq⟩:=Input.return_normal middle target result value returnRun
  have valueEq : value=output out length:=Option.some.inj (read.symm.trans actual)
  have callerCost:=KeyToNibbles.call_any_cost source key out length (by omega) (some none) convertArguments args installed
  change source.clock-(evaluateHOLFiniteState source convert).2.clock≤length/4+4 at callerCost
  rw [convertRun] at callerCost
  have shifted : KeyToNibbles.SpanFrame (callEntryStateHOLFinite source callee) childTarget (byteAddress out 0) (2*length):=by
    simpa only [byteAddress,BitVec.add_zero] using frame
  have memory:=shifted.allocated_frame (callEntryStateHOLFinite source callee) childTarget out (2*length) 0 (2*length) outputArena aligned (by omega)
  refine ⟨valueEq,?_,?_,?_,?_⟩
  · rw [targetEq,middleEq]
    exact view
  · rw [targetEq]
    exact callerCost
  · rw [targetEq,middleEq]
    exact frame.fields
  · intro query outside
    rw [targetEq,middleEq]
    exact memory query outside

end InitECandidate.Solver.Mpt.NibbleKey

#print axioms InitECandidate.Solver.Mpt.NibbleKey.tail_normal
