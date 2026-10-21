import InitECandidate.Solver.Mpt.WitnessCoreExtensionNormal
import InitECandidate.Solver.Mpt.FailGuard
import InitECandidate.Solver.Mpt.WitnessRecordFrame
import InitECandidate.Solver.Input.ScalarScopeTrace
import InitECandidate.Solver.Input.LoopNormal
import InitECandidate.Solver.Input.ScopeLookup

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def extensionFinishedState (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap nibbles length child previous kind : BitVec 64) (data : WitnessRecord.Description) :=
  let ready:=QueryBranch.bind source "ck" kind
  restore source "ck" (restore ready "ex" (metadataState (QueryBranch.bind (extensionAllocated ready heap nibbles length child) "ex" heap)
    heap data.pointer data.length previous))

/-- Whole actual extension return, including both failure guards and
the real kind load. Normal execution derives nonnull child and kind0/3;
the genuine constructor then derives allocation room and the exact pop. -/
theorem return_extension_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db heap nibbles length child previous kind : BitVec 64) (data : WitnessRecord.Description)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.extension nibbles length)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child)))
    (previousCell : source.memory record=.word previous)
    (childMapped : source.memaddrs child) (kindCell : source.memory child=.word kind)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (heapLower : 2713731432≤heap.toNat) (before : data.BeforeHeap heap.toNat)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source returnExtension=(none,post)) :
    child≠0#64 ∧ (kind=0#64 ∨ kind=3#64) ∧ AllocatedBytes.Arena heap 56 ∧ 2≤source.clock ∧
      post=extensionFinishedState source heap nibbles length child previous kind data := by
  rw [return_extension_shape] at normal
  obtain ⟨guardPost,guardRun,kindRun⟩:=Input.sequence_none source post _ extensionKindRead normal
  obtain ⟨passed,same⟩:=Fail.guard_normal source guardPost (.cmp .equal (localVar "result") (.const 0#64)) [.const 8#64] installed guardRun
  subst guardPost
  have nonzero : child≠0#64:=by
    intro zero
    have one : eval source (.cmp .equal (localVar "result") (.const 0#64))=some (.val (.word 1#64)):=by
      simp [eval,evalHOLExact,localVar,toExact,resultCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have impossible : (1#64 : BitVec 64)=0#64:=by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using one.symm.trans passed
    exact (by decide : (1#64 : BitVec 64)≠0#64) impossible
  have kindRead : eval source (readAt "result" 0#64)=some (.val (.word kind)):=by
    simp [eval,readAt,evalHOLExact,evalListHOLExact,localVar,toExact,resultCell,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,childMapped,kindCell]
  rw [extension_kind_read_shape] at kindRun
  obtain ⟨inner,continued,endpoint⟩:=Input.ScalarScope.declare_trace source post "ck" (readAt "result" 0#64) kind afterExtensionKind none kindRead kindRun
  let ready:=QueryBranch.bind source "ck" kind
  have currentKind : ready.locals.lookup (ofString "ck")=some (.val (.word kind)):=bind_lookup_same _ _ _
  rw [after_extension_kind_shape] at continued
  obtain ⟨guardPost,guardRun,createRun⟩:=Input.sequence_none ready inner _ extensionCreate continued
  obtain ⟨passed,same⟩:=Fail.guard_normal ready guardPost extensionKindTest [.const 8#64] installed guardRun
  subst guardPost
  have supported : kind=0#64 ∨ kind=3#64:=by
    by_contra neither
    have notZero : kind≠0#64:=fun zero=>neither (Or.inl zero)
    have notThree : kind≠3#64:=fun three=>neither (Or.inr three)
    have one : eval ready extensionKindTest=some (.val (.word 1#64)):=by
      simp [eval,extensionKindTest,truthy,evalHOLExact,evalListHOLExact,localVar,toExact,currentKind,
        notZero,notThree,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,valueIsWord,valueWord,wordOpHOL,wordOp]
      decide
    have impossible : (1#64 : BitVec 64)=0#64:=by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using one.symm.trans passed
    exact (by decide : (1#64 : BitVec 64)≠0#64) impossible
  have readyView:=view.of_fields source ready record db data rfl rfl
  have readyTop : ready.locals.lookup (ofString "top")=some (.val (.word record)):=
    (bind_lookup_other source "ck" "top" kind (by decide)).trans topCell
  have readyResult : ready.locals.lookup (ofString "result")=some (.val (.word child)):=
    (bind_lookup_other source "ck" "result" kind (by decide)).trans resultCell
  obtain ⟨nodeArena,funded,innerEq⟩:=extension_create_normal ready inner record db heap nibbles length child previous data readyView payload readyTop readyResult
    previousCell heapCell heapArena heapAligned heapLower before installed createRun
  exact ⟨nonzero,supported,nodeArena,funded,by rw [endpoint,innerEq]; rfl⟩

theorem extension_finished_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap nibbles length child previous kind : BitVec 64) (data : WitnessRecord.Description) :
    let post:=extensionFinishedState source heap nibbles length child previous kind data
    post.locals.lookup (ofString "top")=some (.val (.word previous)) ∧
      post.locals.lookup (ofString "result")=some (.val (.word heap)) := by
  dsimp only [extensionFinishedState]
  rw [Input.ScalarScope.restore_other _ _ "ck" "top" (by decide),Input.ScalarScope.restore_other _ _ "ck" "result" (by decide),
    Input.ScalarScope.restore_other _ _ "ex" "top" (by decide),Input.ScalarScope.restore_other _ _ "ex" "result" (by decide)]
  exact ⟨(metadata_fields _ _ _ _ _).1,(metadata_fields _ _ _ _ _).2.1⟩

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.return_extension_normal
#print axioms InitECandidate.Solver.Mpt.WitnessCore.extension_finished_fields
