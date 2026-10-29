import InitECandidate.Solver.Input.RlpLength.EntryProgram

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Data (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array payload : BitVec 64) (txStart txLength wdStart wdCount : Nat) : Prop where
  txBound : txLength≤251655056
  wdSmall : wdCount<2^31
  heap : Blob.HeapInput source input pointer
  records : VarList.Records source input pointer array txStart txLength
  inside : wdStart+44*wdCount≤input.length%2^64
  mapped : ∀ offset∈([32,40,48,56] : List Nat),source.memaddrs (payload+BitVec.ofNat 64 offset)
  txs : source.memory (payload+32#64)=.word (VarList.decodedArray array txLength)
  ntx : source.memory (payload+40#64)=.word (BitVec.ofNat 64 (VarList.decodedCount input txStart txLength))
  withdrawals : source.memory (payload+48#64)=.word (pointer+BitVec.ofNat 64 wdStart)
  nwd : source.memory (payload+56#64)=.word (BitVec.ofNat 64 wdCount)

theorem Data.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array payload : BitVec 64) (txStart txLength wdStart wdCount : Nat)
    (memory : target.memory=source.memory) (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (data : Data source input pointer array payload txStart txLength wdStart wdCount) :
    Data target input pointer array payload txStart txLength wdStart wdCount := by
  refine ⟨data.txBound,data.wdSmall,Blob.HeapInput.of_fields source target input pointer memory.symm domain.symm endian.symm data.heap,
    VarList.Records.of_memory source target input pointer array txStart txLength memory data.records,data.inside,?_,?_,?_,?_,?_⟩
  · intro offset member; rw [domain]; exact data.mapped offset member
  all_goals rw [memory]
  · exact data.txs
  · exact data.ntx
  · exact data.withdrawals
  · exact data.nwd

theorem Data.of_old_memory (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array payload buffer : BitVec 64) (txStart txLength wdStart wdCount : Nat)
    (frame : HeaderEncoding.OldMemory target.memory source.memory buffer)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (inputBefore : pointer.toNat+input.length%2^64≤buffer.toNat)
    (arrayBefore : txLength≠0→array.toNat+16*VarList.decodedCount input txStart txLength≤buffer.toNat)
    (cellsBefore : ∀ offset∈([32,40,48,56] : List Nat),(payload+BitVec.ofNat 64 offset).toNat<buffer.toNat)
    (data : Data source input pointer array payload txStart txLength wdStart wdCount) :
    Data target input pointer array payload txStart txLength wdStart wdCount := by
  refine ⟨data.txBound,data.wdSmall,frame.heap_input source target input pointer buffer domain endian inputBefore data.heap,
    frame.records source target input pointer array buffer txStart txLength arrayBefore data.records,data.inside,?_,?_,?_,?_,?_⟩
  · intro offset member; rw [domain]; exact data.mapped offset member
  · rw [frame _ (cellsBefore 32 (by simp))]; exact data.txs
  · rw [frame _ (cellsBefore 40 (by simp))]; exact data.ntx
  · rw [frame _ (cellsBefore 48 (by simp))]; exact data.withdrawals
  · rw [frame _ (cellsBefore 56 (by simp))]; exact data.nwd

/-- Real declarations of header length, decoded transaction array/count,
and both loop counters, followed by the complete checked block tail. -/
theorem after_release_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array payload headerStart : BitVec 64) (txStart txLength wdStart wdCount headerLength : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (data : Data source input pointer array payload txStart txLength wdStart wdCount)
    (codes : Codes source) (headerBound : headerLength≤916)
    (he : source.locals.lookup (ofString "he")=some (HeaderEncoding.encodedPair headerStart headerLength))
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word payload)))
    (enough : 12*VarList.decodedCount input txStart txLength+43*wdCount+33≤source.clock) :
    ∃ target encoded paid,25*wdCount≤encoded ∧ encoded≤817879876+57*wdCount ∧
      paid≤12*VarList.decodedCount input txStart txLength+43*wdCount+33 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source afterRelease=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} := by
  classical
  have totalRead : eval source (.rfield 1 (localVar "he"))=some (.val (.word (BitVec.ofNat 64 headerLength))) := by
    simp [eval,evalHOLExact,toExact,localVar,he,HeaderEncoding.encodedPair]
  let st:=bind source "total" (BitVec.ofNat 64 headerLength)
  have plT : st.locals.lookup (ofString "pl")=some (.val (.word payload)):=
    (bind_lookup_other _ "total" "pl" _ (by decide)).trans pl
  have txMapped : st.memaddrs (payload+32#64):=data.mapped 32 (by simp)
  have txStored : st.memory (payload+32#64)=.word (VarList.decodedArray array txLength):=data.txs
  have txRead : eval st (payloadCell 32#64)=some (.val (.word (VarList.decodedArray array txLength))) := by
    simp [eval,payloadCell,evalHOLExact,evalListHOLExact,toExact,localVar,plT,valueIsWord,valueWord,wordOpHOL,wordOp,
      memLoadHOLExact,isWfShapeExactHOL,txMapped,txStored]
  let sa:=bind st "txs" (VarList.decodedArray array txLength)
  have plA : sa.locals.lookup (ofString "pl")=some (.val (.word payload)):=
    (bind_lookup_other _ "txs" "pl" _ (by decide)).trans plT
  have countMapped : sa.memaddrs (payload+40#64):=data.mapped 40 (by simp)
  have countStored : sa.memory (payload+40#64)=.word (BitVec.ofNat 64 (VarList.decodedCount input txStart txLength)):=data.ntx
  have countRead : eval sa (payloadCell 40#64)=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input txStart txLength)))) := by
    simp [eval,payloadCell,evalHOLExact,evalListHOLExact,toExact,localVar,plA,valueIsWord,valueWord,wordOpHOL,wordOp,
      memLoadHOLExact,isWfShapeExactHOL,countMapped,countStored]
  let sn:=bind sa "ntx" (BitVec.ofNat 64 (VarList.decodedCount input txStart txLength))
  let sl:=bind sn "tl" 0#64
  let si:=bind sl "i" 0#64
  have setup : WitnessRadix.BuildEntry.Initializes source entryBindings si
      (fun output=>restore source "total" (restore st "txs" (restore sa "ntx" (restore sn "tl" (restore sl "i" output))))) :=
    .step _ totalRead (.step _ txRead (.step _ countRead (.step _ rfl (.step _ rfl (.done _)))))
  have txsI : si.locals.lookup (ofString "txs")=some (.val (.word (VarList.decodedArray array txLength))):=
    (bind_lookup_other _ "i" "txs" _ (by decide)).trans ((bind_lookup_other _ "tl" "txs" _ (by decide)).trans
      ((bind_lookup_other _ "ntx" "txs" _ (by decide)).trans (bind_lookup_same _ _ _)))
  have nI : si.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input txStart txLength)))):=
    (bind_lookup_other _ "i" "ntx" _ (by decide)).trans ((bind_lookup_other _ "tl" "ntx" _ (by decide)).trans (bind_lookup_same _ _ _))
  have tlI : si.locals.lookup (ofString "tl")=some (.val (.word 0#64)):=
    (bind_lookup_other _ "i" "tl" _ (by decide)).trans (bind_lookup_same _ _ _)
  have plI : si.locals.lookup (ofString "pl")=some (.val (.word payload)):=
    (bind_lookup_other _ "i" "pl" _ (by decide)).trans ((bind_lookup_other _ "tl" "pl" _ (by decide)).trans
      ((bind_lookup_other _ "ntx" "pl" _ (by decide)).trans plA))
  have totalI : si.locals.lookup (ofString "total")=some (.val (.word (BitVec.ofNat 64 headerLength))):=
    (bind_lookup_other _ "i" "total" _ (by decide)).trans ((bind_lookup_other _ "tl" "total" _ (by decide)).trans
      ((bind_lookup_other _ "ntx" "total" _ (by decide)).trans ((bind_lookup_other _ "txs" "total" _ (by decide)).trans (bind_lookup_same _ _ _))))
  obtain ⟨target,encoded,paid,lower,upper,bound,number,run,frame⟩:=transaction_phase_execute si input pointer array payload txStart txLength wdStart wdCount headerLength
    data.txBound data.wdSmall (by omega) domain (Blob.HeapInput.of_fields source si input pointer rfl rfl rfl data.heap)
    (VarList.Records.of_memory source si input pointer array txStart txLength rfl data.records) data.inside txsI (bind_lookup_same _ _ _) nI tlI plI totalI
    (data.mapped 56 (by simp)) data.nwd (data.mapped 48 (by simp)) data.withdrawals codes.bytesSize codes.withdrawal codes.wordSize
    codes.tailCodes.listLength codes.tailCodes.headerLength codes.headerCodes.u256Codes.bytesCodes.beCode enough
  let final:=restore source "total" (restore st "txs" (restore sa "ntx" (restore sn "tl" (restore sl "i" target))))
  refine ⟨final,encoded,paid,lower,by omega,bound,number,?_,?_⟩
  · have declarations:=WitnessRadix.BuildEntry.declarations_execute setup transactionPhase
    rw [run] at declarations
    exact declarations
  · exact frame

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.Data.of_fields
#print axioms InitECandidate.Solver.Input.RlpLength.Block.Data.of_old_memory
#print axioms InitECandidate.Solver.Input.RlpLength.Block.after_release_execute
