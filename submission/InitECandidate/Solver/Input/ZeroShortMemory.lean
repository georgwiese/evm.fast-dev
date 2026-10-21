import InitECandidate.Solver.Input.ZeroByteMemory
import InitECandidate.Solver.Input.ZeroShortCost
import InitECandidate.Solver.Input.CopyZeroMemoryNormal

namespace InitECandidate.Solver.Input.ZeroShort
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The original short byte loops carry their real dst/n/i bindings and
preserve every word outside the literal/backing-word destination footprint. -/
theorem Model.memory (code) (test : ExpHOL 64) (body : ProgHOL 64) (stride length : Nat)
    (model : Model code test body stride length)
    (dstSafe : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary (ofString "dst") body current)
    (stepFrame : ∀ current target : PanSemStateFiniteExact 64 Guest.HostMemory,∀ dst query index,
      current.locals.lookup (ofString "dst")=some (.val (.word dst)) →
      current.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))) → index+stride≤length →
      CopyGeneral.Away dst query length → evaluateHOLFiniteState current body=(none,target) → target.memory query=current.memory query)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (dst query : BitVec 64) (index : Nat)
    (pointer : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (inside : index≤length) (position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (away : CopyGeneral.Away dst query length)
    (run : evaluateHOLFiniteState source (.while test body)=(none,post)) :
    post.locals.lookup (ofString "dst")=some (.val (.word dst)) ∧ valid length post ∧ post.memory query=source.memory query := by
  let invariant := fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>
    current.locals.lookup (ofString "dst")=some (.val (.word dst)) ∧ current.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length)))
  have next := MemoryAt.bounded_counter_loop_normal source.code (ofString "i") (ofString "n") test body stride length query model.summary model.advance invariant
    (by intro current ready; exact ready)
    (by intro current ready currentIndex bounded cell; exact model.read current currentIndex bounded cell ready.2)
    (by intro current codeEq ready currentIndex active cell target bodyRun
        have ds:=dstSafe current
        have ns:=model.summary current
        unfold LocalSummary at ds ns
        rw [bodyRun] at ds ns
        exact ⟨⟨(ds.1 rfl).trans ready.1,(ns.1 rfl).trans ready.2⟩,stepFrame current target dst query currentIndex ready.1 cell active away bodyRun⟩)
    source post index rfl ⟨pointer,count⟩ inside position run
  obtain ⟨currentIndex,bounded,cell⟩ := next.2.1
  exact ⟨next.1.1,⟨currentIndex,bounded,cell,next.1.2⟩,next.2.2⟩

/-- Actual unaligned memzero skips its word loops and executes the original
byte8/tail1 loops. No mapped-store or future-success premise is needed. -/
theorem unaligned_body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (dst query : BitVec 64) (length : Nat)
    (short : length<32) (unaligned : dst.toNat%8≠0)
    (pointer : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (away : CopyGeneral.Away dst query length)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source Zero.body=(some (.returned value),post)) : post.memory query=source.memory query := by
  let entry := bind source "i" 0#64
  have entryN : entry.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))) := (bind_lookup_other source "i" "n" 0#64 (by decide)).trans count
  have entryDst : entry.locals.lookup (ofString "dst")=some (.val (.word dst)) := (bind_lookup_other source "i" "dst" 0#64 (by decide)).trans pointer
  have mask : dst &&& 7#64≠0#64 := by
    intro zero
    have number:=congrArg BitVec.toNat zero
    rw [BitVec.toNat_and] at number
    change dst.toNat &&& 7=0 at number
    rw [show 7=2^3-1 from rfl,Nat.and_two_pow_sub_one_eq_mod] at number
    exact unaligned number
  have read : eval entry Zero.alignment=some (.val (.word 0#64)) := by
    simp [eval,Zero.alignment,localVar,evalHOLExact,evalListHOLExact,toExact,entryDst,valueIsWord,valueWord,wordOpHOL,wordOp,AndOp.and,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,mask]
  have skipped : evaluateHOLFiniteState entry (.ite Zero.alignment (.seq Zero.loop32 Zero.loopWord) .skip)=(none,entry) := by
    simp only [eval] at read
    rw [evaluateHOLFiniteState_ite,read]
    exact evaluateHOLFiniteState_skip entry
  rw [Zero.body_shape] at run
  obtain ⟨inner,remaining,endpoint⟩ := declaration_return_word source post "i" (.const 0#64) 0#64 _ value rfl run
  rw [StateSteps.next_sequence entry entry _ _ skipped (Nat.le_refl _)] at remaining
  have bytesSafe := while_local_summary (ofString "n") (Zero.condition 8#64) Zero.byteBody (ZeroByteFlow.byte_summary (ofString "n") (by decide))
  obtain ⟨middle,bytesRun,tailRun⟩ := Input.sequence_returned entry inner Zero.loopBytes _ value
    (by rw [Zero.other_loop_shapes.1]; exact (bytesSafe entry).2.1) remaining
  rw [Zero.other_loop_shapes.1] at bytesRun
  have first := Model.memory source.code (Zero.condition 8#64) Zero.byteBody 8 length (byte_model source.code length short)
    (ZeroByteFlow.byte_summary (ofString "dst") (by decide))
    (fun current target dst query index pointer position active away run=>ZeroByteFlow.byte_memory current target dst query length index pointer position active away run)
    entry middle dst query 0 entryDst entryN (Nat.zero_le _) (bind_lookup_same _ _ _) away bytesRun
  obtain ⟨index,indexBound,indexCell,lengthCell⟩ := first.2.1
  have tailSafe := while_local_summary (ofString "n") (.cmp .lower (localVar "i") (localVar "n")) Zero.tailBody (ZeroByteFlow.tail_summary (ofString "n") (by decide))
  obtain ⟨final,normal,returned⟩ := Input.sequence_returned middle inner Zero.loopTail _ value
    (by rw [Zero.other_loop_shapes.2]; exact (tailSafe middle).2.1) tailRun
  rw [Zero.other_loop_shapes.2] at normal
  have last := Model.memory source.code (.cmp .lower (localVar "i") (localVar "n")) Zero.tailBody 1 length (tail_model source.code length short)
    (ZeroByteFlow.tail_summary (ofString "dst") (by decide))
    (fun current target dst query index pointer position active away run=>ZeroByteFlow.tail_memory current target dst query length index pointer position active away run)
    middle final dst query index first.1 lengthCell indexBound indexCell away normal
  have returnMemory := MemoryAt.return_current final (.const 0#64) query
  rw [returned] at returnMemory
  rw [endpoint]
  exact returnMemory.trans (last.2.2.trans first.2.2)

/-- Real short padding call frame covers both aligned word-multiple and
unaligned ordinary-byte branches of the unchanged original memzero. -/
theorem call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64)) (dst query : BitVec 64) (length : Nat)
    (short : length<32) (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Zero.values dst length))
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (arena : AllocatedBytes.Arena dst length) (alignedMultiple : dst.toNat%8=0 → length%8=0)
    (away : CopyGeneral.Away dst query length)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memzero") arguments)=(none,post)) : post.memory query=source.memory query := by
  by_cases aligned : dst.toNat%8=0
  · exact MemoryAt.zero_normal source post arguments dst query length args installed domain arena aligned (alignedMultiple aligned) (fun offset bound=>(away offset bound).1) run
  · obtain ⟨callee,called,dstLocal,lengthLocal⟩ := Zero.environment source.code.lookup dst length (Zero.original_code source.code installed)
    exact MemoryAt.call_normal source post (ofString "memzero") arguments (Zero.values dst length) Zero.body callee .one query args called
      (fun target value evaluated=>unaligned_body_memory (callEntryStateHOLFinite source callee) target dst query length short aligned dstLocal lengthLocal away value evaluated) run

end InitECandidate.Solver.Input.ZeroShort

#print axioms InitECandidate.Solver.Input.ZeroShort.Model.memory
#print axioms InitECandidate.Solver.Input.ZeroShort.unaligned_body_memory
#print axioms InitECandidate.Solver.Input.ZeroShort.call_memory
