import InitECandidate.Solver.Headers.DecodeProgram
import InitECandidate.Solver.Rlp.DecodeTrace

namespace InitECandidate.Solver.Headers.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original kind check either raises HdrErr10 without a source tick or
reaches the unchanged slice conversion with its actual list-kind word. -/
theorem kind_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload flag : BitVec 64)
    (topCell : source.locals.lookup (ofString "top")=some (Rlp.Item.result pointer header payload flag))
    (shape : source.eshapes.lookup (ofString "HdrErr")=some .one)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterTop=(result,post)) :
    source.clock-post.clock≤0 ∨ flag=1#64 ∧ evaluateHOLFiniteState source afterKind=(result,post) := by
  classical
  have dispatch : evaluateHOLFiniteState source kindGuard=
      if flag≠1#64 then evaluateHOLFiniteState source (.raise (ofString "HdrErr") (.const 10#64)) else (none,source) := by
    simp [kindGuard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,localVar,toExact,topCell,Rlp.Item.result,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [after_top_shape.1,evaluateHOLFiniteState_seq_line780,dispatch] at run
  by_cases listKind : flag=1#64
  · rw [if_neg (not_not_intro listKind)] at run
    exact Or.inr ⟨listKind,run⟩
  · rw [if_pos listKind] at run
    have raised : evaluateHOLFiniteState source (.raise (ofString "HdrErr") (.const 10#64))=
        (some (.exception (ofString "HdrErr") (.val (.word 10#64))),emptyLocalsHOLFinite source) := by
      simp [evaluateHOLFiniteState_raise,shape,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    rw [raised] at run
    have endpoint : source.clock=post.clock := congrArg (fun output=>output.2.clock) run
    exact Or.inl (by omega)

/-- Every actual header-decoder outcome either stops within its initial RLP
allowance or reaches original list slicing with a genuinely complete list,
retained physical input/globals, and the exact outer lexical restoration. -/
theorem top_kind_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (shape : source.eshapes.lookup (ofString "HdrErr")=some .one)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) :
    source.clock-post.clock≤60*length.toNat+44 ∨
      ∃ parsed header payload inner,
        Rlp.Decode.Returned source parsed pointer length cursor limit (Rlp.Item.result pointer header payload 1#64) ∧
        evaluateHOLFiniteState (Input.CallNormal.continuationEntry source parsed "top" (Rlp.Item.result pointer header payload 1#64)) afterKind=(result,inner) ∧
        post=restore source "top" inner := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) topArguments=some (Rlp.Header.values pointer length) := by
    simp [topArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,lengthCell]
  rw [body_shape] at run
  rcases Rlp.Decode.scoped_trace source post pointer length cursor limit "top" topArguments afterTop args arena fits installed result run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨parsed,answer,inner,returned,remaining,endpoint⟩ := reached
    obtain ⟨header,payload,flag,same,small,positive,extent,binary,listHeader⟩ := returned.complete
    subst answer
    let ready := Input.CallNormal.continuationEntry source parsed "top" (Rlp.Item.result pointer header payload flag)
    have topCell : ready.locals.lookup (ofString "top")=some (Rlp.Item.result pointer header payload flag) := by
      simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    have currentShape : ready.eshapes.lookup (ofString "HdrErr")=some .one := by
      change parsed.eshapes.lookup (ofString "HdrErr")=_
      rw [returned.exceptions]
      exact shape
    rcases kind_trace ready inner pointer header payload flag topCell currentShape result remaining with stopped|continued
    · have endClock : post.clock=inner.clock := by rw [endpoint]; rfl
      change parsed.clock-inner.clock≤0 at stopped
      have back := evaluateHOLFiniteState_clock_le ready afterTop
      rw [remaining] at back
      change inner.clock≤parsed.clock at back
      have price := returned.cost
      exact Or.inl (by omega)
    · obtain ⟨one,continued⟩ := continued
      subst flag
      exact Or.inr ⟨parsed,header,payload,inner,returned,continued,endpoint⟩

end InitECandidate.Solver.Headers.Decode

#print axioms InitECandidate.Solver.Headers.Decode.kind_trace
#print axioms InitECandidate.Solver.Headers.Decode.top_kind_trace
