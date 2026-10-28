import InitECandidate.Solver.Input.CurrentHash.PayloadCost
import InitECandidate.Solver.Input.WordPairEnvironment

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual current two-word payload caller. Input data and arena facts refer
to this same caller state; its checked callee supplies the real pl/out bindings.
No successful future hash, extra allocator room or output bytes are assumed. -/
theorem call_cost {input : Guest.InputBlob} (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (blob record array cursor chunk out zeros : BitVec 64) (length start size : Nat)
    (context : MerkleMemory.Context source cursor zeros record) (decoded : Payload.ReturnedImage input source blob record array length start size)
    (inputBound : input.length%2^64≤251655056) (inputArena : AllocatedBytes.Arena blob (input.length%2^64))
    (recordArena : AllocatedBytes.Arena record 136) (recordAligned : record.toNat%8=0)
    (recordBefore : record.toNat+136≤cursor.toNat) (arrayBefore : array.toNat+16*VarList.decodedCount input start size≤cursor.toNat)
    (chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)))
    (chunkArena : AllocatedBytes.Arena chunk 32) (chunkAligned : chunk.toNat%8=0) (chunkBefore : chunk.toNat+32≤record.toNat)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (FixedRecord.scalarValues record out))
    (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "htr_payload") arguments)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤bodyPrice input length start size+1 := by
  obtain ⟨callee,called,payload,output⟩ := word_pair_environment source.code.lookup (ofString "htr_payload") (ofString "pl") (ofString "out") body .one record out
    (by decide) (original_code source.code context.installed)
  let entry := callEntryStateHOLFinite source callee
  have image : Payload.ReturnedImage input entry blob record array length start size := decoded.of_frame rfl
  have ready : Before input entry blob record array cursor chunk out zeros length start size := ⟨context.at_callee callee,image,inputBound,inputArena,recordArena,recordAligned,
    payload,output,recordBefore,arrayBefore,chunkCell,chunkArena,chunkAligned,chunkBefore⟩
  exact ClockCost.call_current_terminating source post destination (ofString "htr_payload") arguments (FixedRecord.scalarValues record out) body callee .one (bodyPrice input length start size)
    args called (by intro observed target evaluated noTimeout; exact body_cost ready observed evaluated noTimeout) result actual notTimeout

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.call_cost
