import InitECandidate.Solver.Input.Copy32SpanWrites
import InitECandidate.Solver.Input.Copy32Bound
import InitECandidate.Solver.Input.LocalSummaryConditional

namespace InitECandidate.Solver.Input.Copy32Span
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch CounterFlow

/-- Frame real normal copy loops from their actual bounded counter and
literal stores, independently of the source pointer or its mapping. -/
theorem loop_frame (code) (test : ExpHOL 64) (body : ProgHOL 64) (stride : Nat)
    (positive : 0<stride) (block : Copy32Flow.Block code body stride) (writes : Writes stride body)
    (reads : StrideReads test stride 32) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (dst : BitVec 64) (codeEq : source.code=code)
    (dstCell : source.locals.lookup (ofString "dst")=some (.val (.word dst))) (valid : StrideInvariant 32 source)
    (normal : evaluateHOLFiniteState source (.while test body)=(none,target)) :
    Frame source target dst 32 ∧ target.locals.lookup (ofString "dst")=some (.val (.word dst)) ∧ StrideInvariant 32 target:=by
  let invariant:=fun current=>Frame source current dst 32 ∧ current.locals.lookup (ofString "dst")=some (.val (.word dst)) ∧ StrideInvariant 32 current
  apply loop_invariant_no_control code test body (fun current=>(block.summary current).2.2) invariant _ source target codeEq
    ⟨Frame.refl source dst 32,dstCell,valid⟩ normal
  intro current installed currentValid observed actual nonzero funded post bodyRun
  obtain ⟨earlier,currentDst,currentCounter⟩:=currentValid
  have saved:=currentCounter
  obtain ⟨index,iCell,nCell,bounded⟩:=saved
  have expected:=reads current index iCell nCell bounded
  have active : index.toNat+stride≤32:=by
    by_contra inactive
    rw [if_neg inactive] at expected
    have zero : observed=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using actual.symm.trans expected
    exact nonzero zero
  obtain ⟨written,nextDst⟩:=writes.normal (decClockHOLFinite current) post dst index 32 active currentDst iCell bodyRun
  have kept : Frame current post dst 32:=⟨written.fields,written.memory⟩
  have transition:=(stride_transition test body stride 32 positive (by decide) block.advance block.summary reads current currentCounter observed actual nonzero).2 funded
  rw [bodyRun] at transition
  exact ⟨earlier.trans source current post dst 32 kept,nextDst,(transition (Or.inl rfl)).1⟩

structure Normal (code) (program : ProgHOL 64) : Prop where
  summary : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary (ofString "n") program source
  run : ∀ source target : PanSemStateFiniteExact 64 Guest.HostMemory,∀ dst : BitVec 64,source.code=code→
    source.locals.lookup (ofString "dst")=some (.val (.word dst))→StrideInvariant 32 source→
    evaluateHOLFiniteState source program=(none,target)→
    Frame source target dst 32 ∧ target.locals.lookup (ofString "dst")=some (.val (.word dst)) ∧ StrideInvariant 32 target

theorem Normal.loop (code) (test : ExpHOL 64) (body : ProgHOL 64) (stride : Nat) (positive : 0<stride)
    (block : Copy32Flow.Block code body stride) (writes : Writes stride body) (reads : StrideReads test stride 32) : Normal code (.while test body):=
  ⟨while_local_summary _ _ _ block.summary,loop_frame code test body stride positive block writes reads⟩

theorem Normal.sequence (code) (first second : ProgHOL 64) (front : Normal code first) (back : Normal code second) : Normal code (.seq first second):=by
  refine ⟨local_summary_sequence _ _ _ front.summary back.summary,?_⟩
  intro source target dst installed dstCell valid normal
  obtain ⟨middle,firstRun,secondRun⟩:=sequence_none source target first second normal
  obtain ⟨firstFrame,middleDst,middleValid⟩:=front.run source middle dst installed dstCell valid firstRun
  have middleCode:=(evaluation_fields source middle first none firstRun).2.2.2.trans installed
  obtain ⟨secondFrame,lastDst,lastValid⟩:=back.run middle target dst middleCode middleDst middleValid secondRun
  exact ⟨firstFrame.trans source middle target dst 32 secondFrame,lastDst,lastValid⟩

theorem Normal.skip (code) : Normal code .skip:=by
  refine ⟨LocalPrefix.skip.summary_full,?_⟩
  intro source target dst installed dstCell valid normal
  rw [evaluateHOLFiniteState_skip] at normal
  cases normal
  exact ⟨Frame.refl source dst 32,dstCell,valid⟩

theorem Normal.conditional (code) (test : ExpHOL 64) (yes no : ProgHOL 64) (left : Normal code yes) (right : Normal code no) : Normal code (.ite test yes no):=by
  refine ⟨local_summary_conditional _ _ _ _ left.summary right.summary,?_⟩
  intro source post dst installed dstCell valid normal
  rw [evaluateHOLFiniteState_ite] at normal
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact (fun query=>Classical.propDecidable (source.memaddrs query)) test=value at normal
  cases value with
  | none=>cases normal
  | some value=>
    cases value with
    | rStruct fields=>cases normal
    | nStruct name fields=>cases normal
    | val payload=>
      cases payload with
      | word word=>
        change (if word=0 then evaluateHOLFiniteState source no else evaluateHOLFiniteState source yes)=(none,post) at normal
        by_cases zero : word=0
        · rw [if_pos zero] at normal; exact right.run source post dst installed dstCell valid normal
        · rw [if_neg zero] at normal; exact left.run source post dst installed dstCell valid normal

theorem loops (code) : Normal code Copy32.loop32 ∧ Normal code Copy32.loopWord ∧ Normal code Copy32.loopBytes ∧ Normal code Copy32.loopTail:=by
  rw [CopyWords.loop_shapes.1,CopyWords.loop_shapes.2,CopyBytes.loop_shapes.1,CopyBytes.loop_shapes.2]
  refine ⟨Normal.loop code _ _ 32 (by decide) (Copy32Flow.word_stores code _ _ 32 (Copy32Flow.increment code 32))
      (Writes.words [0,8,16,24] (by intro offset member; simp at member; omega) 32) (Copy32Flow.condition_reads 32 (by decide)),
    Normal.loop code _ _ 8 (by decide) (Copy32Flow.word_stores code _ _ 8 (Copy32Flow.increment code 8))
      (Writes.words [0] (by intro offset member; simp at member; omega) 8) (Copy32Flow.condition_reads 8 (by decide)),
    Normal.loop code _ _ 8 (by decide) (Copy32Flow.byte_stores code _ _ 8 (Copy32Flow.increment code 8))
      (Writes.bytes [0,1,2,3,4,5,6,7] (by intro offset member; simp at member; omega) 8) (Copy32Flow.condition_reads 8 (by decide)),
    Normal.loop code _ _ 1 (by decide) (Copy32Flow.tail_block code) (Writes.byte 0 (by decide) (Writes.finish 1)) Copy32Flow.tail_reads⟩

end InitECandidate.Solver.Input.Copy32Span

#print axioms InitECandidate.Solver.Input.Copy32Span.loop_frame
#print axioms InitECandidate.Solver.Input.Copy32Span.Normal.sequence
#print axioms InitECandidate.Solver.Input.Copy32Span.Normal.conditional
#print axioms InitECandidate.Solver.Input.Copy32Span.loops
