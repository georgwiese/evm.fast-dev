import InitECandidate.Solver.Input.RlpWrite.BitLengthProgram

namespace InitECandidate.Solver.Input.RlpWrite.BitLength
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem local_frames (source middle target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (first : middle={source with locals:=middle.locals}) (second : target={middle with locals:=target.locals}) :
    target={source with locals:=target.locals} := by
  rw [second,first]

theorem frame_clock_le (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame : target={source with locals:=target.locals}) : target.clock≤source.clock := by
  have clock:=congrArg PanSemStateFiniteExact.clock frame
  change target.clock=source.clock at clock
  omega

/-- Complete actual straight-line binary-search bit length. Its six real
conditional updates return a natural number<=64 and change no nonlocal field. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64)
    (x : source.locals.lookup (ofString "x")=some (.val (.word value))) :
    ∃ target bits,bits≤64 ∧ evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 bits)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite source := by
  classical
  let entry:=bind source "n" 0#64
  have n0 : entry.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 0))):=bind_lookup_same _ _ _
  have x0 : entry.locals.lookup (ofString "x")=some (.val (.word value)):=
    (bind_lookup_other _ "n" "x" _ (by decide)).trans x
  obtain ⟨s32,v32,c32,c32Bound,v32Bound,r32,f32,x32,n32⟩:=stage_execute entry value 0 32 (by decide) value.isLt x0 n0
  obtain ⟨s16,v16,c16,c16Bound,v16Bound,r16,f16,x16,n16⟩:=stage_execute s32 v32 c32 16 (by decide) v32Bound x32 n32
  obtain ⟨s8,v8,c8,c8Bound,v8Bound,r8,f8,x8,n8⟩:=stage_execute s16 v16 c16 8 (by decide) v16Bound x16 n16
  obtain ⟨s4,v4,c4,c4Bound,v4Bound,r4,f4,x4,n4⟩:=stage_execute s8 v8 c8 4 (by decide) v8Bound x8 n8
  obtain ⟨s2,v2,c2,c2Bound,v2Bound,r2,f2,x2,n2⟩:=stage_execute s4 v4 c4 2 (by decide) v4Bound x4 n4
  obtain ⟨s1,v1,c1,c1Bound,v1Bound,r1,f1,x1,n1⟩:=stage_execute s2 v2 c2 1 (by decide) v2Bound x2 n2
  let bits:=c1+v1.toNat
  have bitsBound : bits≤64 := by change v1.toNat<2 at v1Bound; dsimp [bits]; omega
  have returnRun : evaluateHOLFiniteState s1 (.return (.op .add [localVar "n",localVar "x"]))=
      (some (.returned (.val (.word (BitVec.ofNat 64 bits)))),emptyLocalsHOLFinite s1) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,n1,x1,valueIsWord,valueWord,wordOpHOL,wordOp,
      bits,BitVec.ofNat_add,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have sequenceRun : evaluateHOLFiniteState entry (stages [32,16,8,4,2,1])=
      (some (.returned (.val (.word (BitVec.ofNat 64 bits)))),emptyLocalsHOLFinite s1) := by
    simp only [stages]
    rw [WitnessRadix.StateSteps.next_sequence entry s32 _ _ r32 (frame_clock_le _ _ f32),
      WitnessRadix.StateSteps.next_sequence s32 s16 _ _ r16 (frame_clock_le _ _ f16),
      WitnessRadix.StateSteps.next_sequence s16 s8 _ _ r8 (frame_clock_le _ _ f8),
      WitnessRadix.StateSteps.next_sequence s8 s4 _ _ r4 (frame_clock_le _ _ f4),
      WitnessRadix.StateSteps.next_sequence s4 s2 _ _ r2 (frame_clock_le _ _ f2),
      WitnessRadix.StateSteps.next_sequence s2 s1 _ _ r1 (frame_clock_le _ _ f1)]
    exact returnRun
  have declared:=ScalarScope.declare_execute source _ "n" (.const 0#64) 0#64 (stages [32,16,8,4,2,1]) _ rfl sequenceRun
  have frame16:=local_frames entry s32 s16 f32 f16
  have frame8:=local_frames entry s16 s8 frame16 f8
  have frame4:=local_frames entry s8 s4 frame8 f4
  have frame2:=local_frames entry s4 s2 frame4 f2
  have frame1:=local_frames entry s2 s1 frame2 f1
  let target:=restore source "n" (emptyLocalsHOLFinite s1)
  refine ⟨target,bits,bitsBound,?_,?_⟩
  · rw [body_shape]
    exact declared
  · have frame:=congrArg emptyLocalsHOLFinite frame1
    change emptyLocalsHOLFinite s1=emptyLocalsHOLFinite source at frame ⊢
    exact frame

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word value)])
    (code : source.code.lookup (ofString "bit_length64")=some (formals,body,.one)) (enough : 1≤source.clock) :
    ∃ bits,bits≤64 ∧ evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "bit_length64") expressions continuation)=
      (let output:=evaluateHOLFiniteState (bind {source with clock:=source.clock-1} name (BitVec.ofNat 64 bits)) continuation
      (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,x⟩:=CallNormal.unary_environment source.code.lookup (ofString "bit_length64") "x" body value code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,bits,bound,bodyRun,frame⟩:=execute entry value x
  have callerFrame : emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-1-0}:=frame
  have actual:=CallNormal.pure_return_execute source target name (ofString "bit_length64") expressions
    [.val (.word value)] body continuation callee (BitVec.ofNat 64 bits) 0 args called enough bodyRun callerFrame
  exact ⟨bits,bound,by simpa only [Nat.sub_zero] using actual⟩

end InitECandidate.Solver.Input.RlpWrite.BitLength

#print axioms InitECandidate.Solver.Input.RlpWrite.BitLength.execute
#print axioms InitECandidate.Solver.Input.RlpWrite.BitLength.call_execute
