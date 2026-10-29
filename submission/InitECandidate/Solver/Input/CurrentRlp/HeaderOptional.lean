import InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix

namespace InitECandidate.Solver.Input.CurrentRlp.HeaderOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch HeaderEncoding HeaderFields

theorem optional_append (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tail : ProgHOL 64) :
    evaluateHOLFiniteState source (.seq optionalCode tail)=evaluateHOLFiniteState source (fields optionalFields tail) := by
  simp only [optionalCode,optionalFields,fields,evaluateHOLFiniteState_seq_line780]
  generalize evaluateHOLFiniteState source (call (.bytes 232 32))=first
  obtain ⟨firstResult,firstPost⟩:=first
  cases firstResult with
  | some result=>rfl
  | none=>
    generalize evaluateHOLFiniteState firstPost advance=second
    obtain ⟨secondResult,secondPost⟩:=second
    cases secondResult with
    | some result=>rfl
    | none=>
      generalize evaluateHOLFiniteState secondPost (call (.scalar 240))=third
      obtain ⟨thirdResult,thirdPost⟩:=third
      cases thirdResult <;> rfl

/-- The current-header flag is read from the actual retained header cell. -/
theorem choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64)
    (context : Context source original header buffer) :
    evaluateHOLFiniteState source afterBase=
      if wordAt original (address header 0)=0#64 then evaluateHOLFiniteState source suffix
      else evaluateHOLFiniteState source (fields optionalFields suffix) := by
  have read:=context.load_one source original header buffer 0 (by decide) (by decide)
  have testRead : eval source currentTest=some (.val (.word (if wordAt original (address header 0)=0#64 then 0#64 else 1#64))):=by
    simp only [eval] at read ⊢
    rw [currentTest,evalHOLExact,read]
    simp [evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simp only [eval] at testRead
  by_cases zero : wordAt original (address header 0)=0#64
  · rw [if_pos zero,afterBase,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,testRead]
    simp [zero,evaluateHOLFiniteState_skip]
  · rw [if_neg zero]
    rw [←optional_append source suffix]
    simp only [afterBase,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,testRead,if_neg zero]
    rfl

/-- The real optional branch and final list header cost at most103source
clock ticks on every outcome, after the actual base fields. -/
theorem cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64) (position : Nat)
    (context : Context source original header buffer) (installed : OriginalCode.Installed source.code)
    (bounded : (cursor buffer).toNat≤2952790016) (facts : ∀ field∈optionalFields,FieldFacts original header field)
    (lower : 9≤position) (upper : position≤866)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer))) :
    source.clock-(evaluateHOLFiniteState source afterBase).2.clock≤103 := by
  rw [choice source original header buffer context]
  split
  · have price:=HeaderSuffix.cost source original header buffer position context installed lower (by omega) p buf
    omega
  · have priced:=fields_cost source original header buffer optionalFields position context installed bounded facts
      (by change position+50≤1024; omega) p suffix 31 (by
        intro current finalPosition nextLower nextUpper reached
        have currentInstalled : OriginalCode.Installed current.code:=by rw [MemoryMetadata.code reached.metadata]; exact installed
        have currentBuf:=(reached.locals "buf" (by decide) (by decide)).trans buf
        exact HeaderSuffix.cost current original header buffer finalPosition reached.context currentInstalled (by omega)
          (by change finalPosition≤position+50 at nextUpper; omega) reached.pointer currentBuf)
    change source.clock-(evaluateHOLFiniteState source (fields optionalFields suffix)).2.clock≤72+31 at priced
    exact priced

/-- An actual returning optional branch supplies the same mapped final
encoding and protected older memory as the genuine suffix. -/
theorem normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64) (position : Nat)
    (context : Context source original header buffer) (installed : OriginalCode.Installed source.code)
    (bounded : (cursor buffer).toNat≤2952790016) (facts : ∀ field∈optionalFields,FieldFacts original header field)
    (lower : 9≤position) (upper : position≤866)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (value : ValueHOL 64) (returned : evaluateHOLFiniteState source afterBase=(some (.returned value),target)) :
    ∃ start encoded,1≤encoded ∧ encoded≤916 ∧ value=encodedPair start encoded ∧ AllocatedBytes.Arena start encoded ∧
      MemoryMetadata.erase target=MemoryMetadata.erase source ∧ OldMemory target.memory original buffer := by
  rw [choice source original header buffer context] at returned
  split at returned
  · exact HeaderSuffix.normal source target original header buffer position context installed lower (by omega) p buf value returned
  · obtain ⟨current,finalPosition,nextLower,nextUpper,reached,remaining⟩:=fields_returned source target original header buffer optionalFields position
      context installed bounded facts (by change position+50≤1024; omega) p suffix value returned
    have currentInstalled : OriginalCode.Installed current.code:=by rw [MemoryMetadata.code reached.metadata]; exact installed
    have currentBuf:=(reached.locals "buf" (by decide) (by decide)).trans buf
    obtain ⟨start,encoded,positive,size,answer,arena,metadata,memory⟩:=HeaderSuffix.normal current target original header buffer finalPosition
      reached.context currentInstalled (by omega) (by change finalPosition≤position+50 at nextUpper; omega) reached.pointer currentBuf value remaining
    exact ⟨start,encoded,positive,size,answer,arena,metadata.trans reached.metadata,memory⟩

end InitECandidate.Solver.Input.CurrentRlp.HeaderOptional

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderOptional.optional_append
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderOptional.choice
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderOptional.cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderOptional.normal
