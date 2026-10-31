import InitECandidate.Solver.Rlp.ItemCallFrame
import InitECandidate.Solver.Rlp.ItemCallEncoding
import InitECandidate.Solver.Input.ScopedCallTrace

namespace InitECandidate.Solver.Rlp.Item
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- All actual original item-call outcomes either stop within their local
allowance or expose the real decoded tuple and protected current arena at
the genuine continuation. Successful later parsing is never a premise. -/
theorem scoped_frame_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length cursor limit : BitVec 64) (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "rlp_item") arguments continuation)=(outcome,post)) :
    source.clock-post.clock≤60*length.toNat+42 ∨ ∃ target header payload flag inner,
      Valid pointer length.toNat (result pointer header payload flag) ∧ Validation.Arena target cursor limit ∧
      Validation.Above source target cursor.toNat ∧ target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧
      target.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr") ∧
      target.clock≤source.clock ∧ source.clock-target.clock≤60*length.toNat+42 ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name (result pointer header payload flag)) continuation=(outcome,inner) ∧
      post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString "rlp_item") body resultShape pointer length (original_code source.code installed)
  have entryArena:=Validation.Arena.of_fields source (callEntryStateHOLFinite source callee) cursor limit arena rfl rfl
  have price:=body_cost (callEntryStateHOLFinite source callee) pointer length cursor limit pointerLocal lengthLocal entryArena fits installed
  rcases Input.CallNormal.scoped_trace source post name resultShape (ofString "rlp_item") arguments _ body continuation callee resultShape (60*length.toNat+41)
      args called price outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,spent,continued,endpoint⟩:=reached
    obtain ⟨header,payload,flag,valueEq,valid,nextArena,above,domain,endian,codeEq,heapEq,bodyPrice⟩:=
      body_frame (callEntryStateHOLFinite source callee) target pointer length cursor limit pointerLocal lengthLocal entryArena fits installed value bodyRun
    rw [valueEq] at continued
    exact Or.inr ⟨target,header,payload,flag,inner,valid,nextArena,above,domain,endian,codeEq,heapEq,forward,spent,continued,endpoint⟩

end InitECandidate.Solver.Rlp.Item

#print axioms InitECandidate.Solver.Rlp.Item.scoped_frame_trace
