import InitECandidate.Solver.Mpt.NibbleKeySecureProgram
import InitECandidate.Solver.Mpt.NibbleKeyConvert
import InitECandidate.Solver.Mpt.KeyToNibblesCall

namespace InitECandidate.Solver.Mpt.NibbleKey
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual secure converter reads the genuine hash scratch bytes,
converts exactly32 bytes and returns its real fresh64-nibble buffer. -/
theorem secure_tail_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (hash out : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false)
    (hashCell : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hash)))
    (outCell : source.locals.lookup (ofString "nb")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena hash 32) (outputArena : AllocatedBytes.Arena out 64)
    (aligned : out.toNat%8=0) (before : hash.toNat+32≤out.toNat)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source secureTail=(some (.returned value),target)) :
    value=output out 32 ∧ TrieWalk.KeyView target.memory target.memaddrs target.be out 64 ∧
      source.clock-target.clock≤9 ∧ KeyToNibbles.writeMetadata target=KeyToNibbles.writeMetadata source ∧
      ∀ query : BitVec 64,query.toNat<out.toNat ∨ out.toNat+64≤query.toNat→target.memory query=source.memory query := by
  rw [secure_shapes.2.2] at normal
  obtain ⟨middle,convertRun,returnRun⟩:=Input.sequence_returned source target secureConvert (.return secureResult) value
    (Input.NoReturn.ignored_call (ofString "key_to_nibbles") secureConvertArguments source) normal
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) secureConvertArguments=some (KeyToNibbles.values hash out):=by
    simp [secureConvertArguments,KeyToNibbles.values,evalListHOLFinite,evalListHOLExact,localVar,evalHOLExact,toExact,hashCell,outCell]
  obtain ⟨_funded,clock,locals,view,frame⟩:=KeyToNibbles.call_normal source middle hash out little (by have upper:=outputArena.upper; omega)
    (fun offset inside=>AllocatedBytes.byte_mapped source hash 32 offset domain inputArena inside)
    (fun offset inside=>AllocatedBytes.byte_mapped source out 64 offset domain outputArena inside)
    (by
      intro left leftInside right rightInside same
      have first:=byteAddress_toNat hash left (by have upper:=inputArena.upper; omega)
      have second:=byteAddress_toNat out right (by have upper:=outputArena.upper; omega)
      have numbers:=congrArg BitVec.toNat same
      rw [first,second] at numbers
      omega) secureConvertArguments args installed convertRun
  have nextOut : middle.locals.lookup (ofString "nb")=some (.val (.word out)):=by rw [locals]; exact outCell
  have actual : eval middle secureResult=some (output out 32):=by
    simp [eval,secureResult,output,evalHOLExact,evalListHOLExact,localVar,toExact,nextOut]
  obtain ⟨read,targetEq⟩:=Input.return_normal middle target secureResult value returnRun
  have valueEq : value=output out 32:=Option.some.inj (read.symm.trans actual)
  have span : KeyToNibbles.SpanFrame source middle (byteAddress out 0) 64:=by
    simpa only [byteAddress,BitVec.add_zero] using (show KeyToNibbles.SpanFrame source middle out 64 from ⟨frame.fields,frame.memory⟩)
  have memory:=span.allocated_frame source middle out 64 0 64 outputArena aligned (by omega)
  refine ⟨valueEq,?_,?_,?_,?_⟩
  · rw [targetEq]; exact view
  · rw [targetEq]; change source.clock-middle.clock≤9; omega
  · rw [targetEq]; exact frame.fields
  · intro query outside; rw [targetEq]; exact memory query outside

end InitECandidate.Solver.Mpt.NibbleKey

#print axioms InitECandidate.Solver.Mpt.NibbleKey.secure_tail_normal
