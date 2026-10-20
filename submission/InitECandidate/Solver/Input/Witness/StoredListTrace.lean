import InitECandidate.Solver.Input.Witness.Fields
import InitECandidate.Solver.Input.BytesList.CallerTrace

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

/-- Every outcome of the original byte-list call followed by its actual SI
stores. Parser/size rejections propagate; passing reaches the unchanged
continuation with physical records, exact heap and earlier-word frames. -/
theorem stored_list_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array limit maximum si : BitVec 64) (start length offset : Nat)
    (heap : Blob.HeapInput source input pointer) (inside : start+length≤input.length%2^64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (lower : 2701131776≤pointer.toNat) (aligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (arrayAfter : pointer.toNat+input.length%2^64+8≤array.toNat)
    (room : array.toNat+4*length≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word array)))
    (allocCode : source.code.lookup (ofString "alloc")=some (PersistentAlloc.formals,PersistentAlloc.body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one)
    (varCode : source.code.lookup (ofString "ssz_split_var_list")=some (VarList.formals,VarList.body,VarList.returnShape))
    (code : source.code.lookup (ofString "decode_bytes_list")=some (BytesList.formals,BytesList.body,VarList.returnShape))
    (siLocal : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (siArena : Arena si 96) (siAligned : si.toNat%8=0) (siAfter : pointer.toNat+input.length%2^64+8≤si.toNat)
    (siBefore : si.toNat+96≤array.toNat) (offsetInside : offset+16≤96) (offsetAligned : offset%8=0)
    (name : String) (different : ofString name≠ofString "si") (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=
      some (BytesList.values (pointer+BitVec.ofNat 64 start) (BitVec.ofNat 64 length) limit maximum))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) VarList.returnShape (ofString "decode_bytes_list") expressions
      (.seq (pointerStore name offset) (.seq (countStore name offset) continuation)))=(result,post)) (notTimeout : result≠some .timeOut) :
    (∃ error : BitVec 64,(error=20#64 ∨ error=21#64 ∨ error=22#64 ∨ error=23#64 ∨ error=70#64) ∧ result=some (.exception (ofString "SszErr") (.val (.word error))) ∧ source.clock-post.clock≤2*(length/4)+4) ∨
    (∃ next innerPost,
      next.locals=source.locals.update (ofString name,BytesList.pairValue (VarList.decodedArray array length) (VarList.decodedCount input start length)) ∧
      VarList.Records next input pointer array start length ∧ VarList.decodedCount input start length≤limit.toNat ∧
      (∀ index<VarList.decodedCount input start length,
        (VarList.recordLength input start length (VarList.decodedCount input start length) index).toNat≤maximum.toNat) ∧
      Blob.HeapInput next input pointer ∧
      next.memory (byteAddress si offset)=.word (VarList.decodedArray array length) ∧
      next.memory (byteAddress si (offset+8))=.word (BitVec.ofNat 64 (VarList.decodedCount input start length)) ∧
      next.globals.lookup (ofString "heap_ptr")=some (.val (.word (VarList.nextCursor array (VarList.decodedCount input start length)))) ∧
      source.clock-next.clock≤2*(length/4)+4 ∧ next.clock≤source.clock ∧
      (∀ query,query.toNat<array.toNat → query≠byteAddress si offset → query≠byteAddress si (offset+8) → next.memory query=source.memory query) ∧
      BackingLayout.control next=BackingLayout.control
        (if length=0 then source else PersistentAlloc.post source array (BitVec.ofNat 64 (16*(Guest.GasLimit.le32 input start/4)))) ∧
      evaluateHOLFiniteState next continuation=(result,innerPost) ∧ post=restore source name innerPost) := by
  classical
  rcases BytesList.caller_trace source post input pointer array limit maximum start length
    heap inside domain lower aligned arrayAligned arrayAfter room heapGlobal allocCode failCode exceptionShape varCode code
    name expressions (.seq (pointerStore name offset) (.seq (countStore name offset) continuation)) args result run notTimeout with rejected | normal
  · exact Or.inl rejected
  obtain ⟨decoded,innerPost,decodedLocals,records,countLimit,decodedHeap,lengthBound,clockCost,clockUpper,oldMemory,codes,domains,shapes,tailRun,postEq,control⟩ := normal
  have countFacts:=VarList.Records.cells decoded input pointer array start length (domains.trans domain) records
  have countNat : (BitVec.ofNat 64 (VarList.decodedCount input start length)).toNat=VarList.decodedCount input start length := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have:=countFacts.2.1;omega)]
  have nextSi : decoded.locals.lookup (ofString "si")=some (.val (.word si)) := by
    rw [decodedLocals]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show (ofString name==ofString "si")=false from beq_eq_false_iff_ne.mpr different] using siLocal
  have tupleLocal : decoded.locals.lookup (ofString name)=some (VarList.pairValue (VarList.decodedArray array length)
      (BitVec.ofNat 64 (VarList.decodedCount input start length)).toNat) := by
    rw [decodedLocals,countNat]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,BytesList.pairValue]
  obtain ⟨stores,firstCell,secondCell,storeFrame⟩:=pair_stores decoded si (VarList.decodedArray array length)
    (BitVec.ofNat 64 (VarList.decodedCount input start length)) name offset continuation nextSi tupleLocal (domains.trans domain)
    siArena siAligned offsetInside offsetAligned
  let next:=pairStored decoded si offset (VarList.decodedArray array length) (BitVec.ofNat 64 (VarList.decodedCount input start length))
  have nextRecords:=records_after_pair_stores decoded input pointer array si (VarList.decodedArray array length)
    (BitVec.ofNat 64 (VarList.decodedCount input start length)) start length offset records siArena offsetInside siBefore
  have firstNumber:=byteAddress_toNat si offset (by have:=siArena.upper;omega)
  have secondNumber:=byteAddress_toNat si (offset+8) (by have:=siArena.upper;omega)
  have firstHeap:=Blob.HeapInput.store_separate decoded input pointer (byteAddress si offset) (VarList.decodedArray array length)
    decodedHeap aligned (by have:=siArena.upper;omega) (Or.inr (by rw [firstNumber];omega))
  have nextHeap:=Blob.HeapInput.store_separate _ input pointer (byteAddress si (offset+8))
    (BitVec.ofNat 64 (VarList.decodedCount input start length)) firstHeap aligned (by have:=siArena.upper;omega)
    (Or.inr (by rw [secondNumber];omega))
  have cursor:=VarList.cursor_of_control source decoded input array start length countFacts.1 arrayAligned room heapGlobal control
  refine Or.inr ⟨next,innerPost,decodedLocals,nextRecords,countLimit,lengthBound,nextHeap,firstCell,secondCell,cursor.1,
    clockCost,clockUpper,?_,control,stores.symm.trans tailRun,postEq⟩
  intro query before firstAway secondAway
  exact (storeFrame query firstAway secondAway).trans (oldMemory query before)

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.stored_list_trace
