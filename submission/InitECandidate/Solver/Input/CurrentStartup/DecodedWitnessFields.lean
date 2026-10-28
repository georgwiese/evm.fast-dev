import InitECandidate.Solver.Input.CurrentStartup.WitnessPrefixFrame

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- All six actual witness fields at the final witness return. Later list
allocations and their SI stores preserve the earlier pointer/count pairs. -/
theorem WitnessHeadersReturn.Result.witness_fields
    {origin : DecoderOrigin} {input : Guest.InputBlob}
    {source ready post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord rq nodes codes headers : BitVec 64}
    {payloadLength nodeStart nodeLength codeStart codeLength headerStart headerLength : Nat}
    (data : WitnessHeadersReturn.Result (decoderOrigin:=origin) input source ready post pointer si record gasWord rq nodes codes headers
      payloadLength nodeStart nodeLength codeStart codeLength headerStart headerLength) :
    post.memory (si+40#64)=.word (VarList.decodedArray nodes nodeLength) ∧
    post.memory (si+48#64)=.word (BitVec.ofNat 64 (VarList.decodedCount input nodeStart nodeLength)) ∧
    post.memory (si+56#64)=.word (VarList.decodedArray codes codeLength) ∧
    post.memory (si+64#64)=.word (BitVec.ofNat 64 (VarList.decodedCount input codeStart codeLength)) ∧
    post.memory (si+72#64)=.word (VarList.decodedArray headers headerLength) ∧
    post.memory (si+80#64)=.word (BitVec.ofNat 64 (VarList.decodedCount input headerStart headerLength)) := by
  obtain ⟨codeSource,codeData⟩ := data.origin
  obtain ⟨nodeSource,nodePost,nodeData,nodeEndpoint⟩ := codeData.origin
  have headerFrame (offset : Nat) (small : offset≤64) :
      post.memory (si+BitVec.ofNat 64 offset)=source.memory (si+BitVec.ofNat 64 offset) := by
    apply data.memory
    · rw [data.context.si_field_number input ready pointer si record gasWord payloadLength offset (by omega)]
      have a:=data.context.recordAfter; have b:=data.arrayAfter
      omega
    · exact data.context.si_fields_ne input ready pointer si record gasWord payloadLength offset 72 (by omega) (by decide) (by omega)
    · exact data.context.si_fields_ne input ready pointer si record gasWord payloadLength offset 80 (by omega) (by decide) (by omega)
  have codeFrame (offset : Nat) (small : offset≤48) :
      source.memory (si+BitVec.ofNat 64 offset)=codeSource.memory (si+BitVec.ofNat 64 offset) := by
    apply codeData.memory
    · rw [codeData.context.si_field_number input source pointer si record gasWord payloadLength offset (by omega)]
      have a:=codeData.context.recordAfter; have b:=codeData.arrayAfter
      omega
    · exact codeData.context.si_fields_ne input source pointer si record gasWord payloadLength offset 56 (by omega) (by decide) (by omega)
    · exact codeData.context.si_fields_ne input source pointer si record gasWord payloadLength offset 64 (by omega) (by decide) (by omega)
  exact ⟨(headerFrame 40 (by decide)).trans ((codeFrame 40 (by decide)).trans nodeData.nodePointer),
    (headerFrame 48 (by decide)).trans ((codeFrame 48 (by decide)).trans nodeData.nodeCount),
    (headerFrame 56 (by decide)).trans codeData.codePointer,
    (headerFrame 64 (by decide)).trans codeData.codeCount,data.headerPointer,data.headerCount⟩

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn.Result.witness_fields
