import InitECandidate.Solver.Input.HeaderEncoding.NormalRoom
import InitECandidate.Solver.Input.RlpLength.EntryProgram
import InitECandidate.Solver.Input.CallPrefixScopedActual

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def headerActions : List CallPrefix.Action:=[
  .scoped (ofString "mark") .one (ofString "heap_mark") [],
  .scoped (ofString "he") HeaderEncoding.returnShape (ofString "encode_header") [WitnessRadix.QueryBranch.localVar "hdr"]]

theorem body_header_actions : body=CallPrefix.program headerActions afterHeader := by
  rw [entry_shape]
  rfl

theorem header_actions_never : NoReturn.Never (CallPrefix.program headerActions .skip) :=
  NoReturn.scoped_call _ _ _ _ _ (NoReturn.scoped_call _ _ _ _ _ NoReturn.skip)

/-- Any actual normal block-length computation supplies the stronger
encoder temporary-space requirement through the real nested call. -/
theorem normal_room (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word buffer))) (bounded : buffer.toNat≤33806089496)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    buffer.toNat+1056≤33806089496 := by
  rw [body_header_actions] at normal
  obtain ⟨current,inner,execution,endpoint,remaining⟩:=CallPrefix.normal_trace source post headerActions afterHeader value header_actions_never normal
  obtain ⟨middle,first,next⟩:=execution.head
  have preserved : GlobalEffects.Preserves (ofString "heap_ptr") source.code
      (CallPrefix.program [.scoped (ofString "mark") .one (ofString "heap_mark") []] .skip):=by
    apply GlobalEffects.scoped_body _ source.code _ _ _ _ _ [] HeapScope.markBody .one
      (OriginalRlp.heap_mark source.code installed)
    · rw [HeapScope.mark_shape]
      exact GlobalEffects.returned _ _ _
    · exact GlobalEffects.skip _ _
  have middleHeap:=(first.globals (ofString "heap_ptr") preserved).trans heap
  have middleInstalled : OriginalCode.Installed middle.code:=by rw [first.runtime.2.2.2.1]; exact installed
  obtain ⟨after,second,tail⟩:=next.head
  obtain ⟨values,actualBody,callee,returnShape,returned,childTarget,args,called,run⟩:=second.scoped_actual
  have bodyEq:=GlobalEffects.lookup_body middle.code (ofString "encode_header") HeaderEncoding.formals HeaderEncoding.body HeaderEncoding.returnShape
    (OriginalRlp.encode_header middle.code middleInstalled) values actualBody callee returnShape called
  subst actualBody
  exact HeaderEncoding.normal_room (callEntryStateHOLFinite middle callee) childTarget buffer middleInstalled middleHeap bounded returned run

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.body_header_actions
#print axioms InitECandidate.Solver.Input.RlpLength.Block.header_actions_never
#print axioms InitECandidate.Solver.Input.RlpLength.Block.normal_room
