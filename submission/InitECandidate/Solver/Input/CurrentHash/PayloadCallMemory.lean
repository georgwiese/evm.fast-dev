import InitECandidate.Solver.Input.CurrentHash.PayloadMemory
import InitECandidate.Solver.Input.CurrentHash.PayloadCallCost

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Complete real current payload caller protects arbitrary earlier metadata
outside the actual output/length chunk and restores the entering heap. All
entry obligations concern this caller and the same normal callee return. -/
theorem call_frame {input : Guest.InputBlob} (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (blob record array cursor chunk out zeros query : BitVec 64) (length start size : Nat)
    (context : MerkleMemory.Context source cursor zeros record) (decoded : Payload.ReturnedImage input source blob record array length start size)
    (inputBound : input.length%2^64≤251655056) (inputArena : AllocatedBytes.Arena blob (input.length%2^64))
    (recordArena : AllocatedBytes.Arena record 136) (recordAligned : record.toNat%8=0)
    (recordBefore : record.toNat+136≤cursor.toNat) (arrayBefore : array.toNat+16*VarList.decodedCount input start size≤cursor.toNat)
    (chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)))
    (chunkArena : AllocatedBytes.Arena chunk 32) (chunkAligned : chunk.toNat%8=0) (chunkBefore : chunk.toNat+32≤record.toNat)
    (before : query.toNat<cursor.toNat) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (FixedRecord.scalarValues record out))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_payload") arguments)=(none,post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  obtain ⟨callee,called,payload,output⟩ := word_pair_environment source.code.lookup (ofString "htr_payload") (ofString "pl") (ofString "out") body .one record out
    (by decide) (original_code source.code context.installed)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post (ofString "htr_payload") arguments actual
  have valuesEq := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  let entry := callEntryStateHOLFinite source callee
  have image : Payload.ReturnedImage input entry blob record array length start size := decoded.of_frame rfl
  have ready : Before input entry blob record array cursor chunk out zeros length start size := ⟨context.at_callee callee,image,inputBound,inputArena,recordArena,recordAligned,
    payload,output,recordBefore,arrayBefore,chunkCell,chunkArena,chunkAligned,chunkBefore⟩
  have frame := body_frame ready query before chunkAway outAway returned bodyRun
  rw [endpoint]
  exact frame

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.call_frame
