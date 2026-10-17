import InitECandidate.Solver.MutableTable.FindPrepared

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix

/-- Complete original htab_find_slot for32-byte keys at an aligned query:
actual header reads, hash call, index declaration, comparator scan and return.
Physical table, ABI/code, allocation and clock premises remain explicit. -/
theorem aligned32_find (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Parameters)
    (cells : HeaderCells source table p) (keyLength : p.keyLength=32#64)
    (bits : Nat) (small : bits<64) (capacity : p.capacity=BitVec.ofNat 64 (2^bits))
    (order : List Nat) (room : order.length<2^bits) (keys : Nat→WitnessRadix.ByteKeys.Key)
    (binary : ∀ i<2^bits,usedByte source p (BitVec.ofNat 64 i)=some 0 ∨ usedByte source p (BitVec.ofNat 64 i)=some 1)
    (covered : ∀ i<2^bits,usedByte source p (BitVec.ofNat 64 i)=some 1→i∈order)
    (views : ∀ i<2^bits,usedByte source p (BitVec.ofNat 64 i)=some 1→
      WitnessRadix.MemoryBytes.ByteView source (p.keys+BitVec.ofNat 64 i*p.stride) (keys i))
    (fits : ∀ i<2^bits,(p.keys+BitVec.ofNat 64 i*p.stride).toNat+32<2^64)
    (query : WitnessRadix.ByteKeys.Key) (queryView : WitnessRadix.MemoryBytes.ByteView source p.key query)
    (queryFits : p.key.toNat+32<2^64) (little : source.be=false)
    (words : Fin 4→BitVec 64) (aligned : p.key &&& 7#64=0#64)
    (wordMapped : ∀ i : Fin 4,source.memaddrs (p.key+BitVec.ofNat 64 (8*i.val)))
    (wordStored : ∀ i : Fin 4,source.memory (p.key+BitVec.ofNat 64 (8*i.val))=.word (words i))
    (hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (memeqCode : source.code.lookup (ofString "memeq")=some (WitnessRadix.Memeq32.formals,WitnessRadix.Memeq32.body,.one))
    (enough : 6*order.length+1≤source.clock) :
    ∃ paid value,paid≤6*order.length+1 ∧
      (evaluateHOLFiniteState source body).1=some (.returned (.val (.word value))) ∧
      emptyLocalsHOLFinite (evaluateHOLFiniteState source body).2=emptyLocalsHOLFinite {source with clock:=source.clock-paid} := by
  classical
  let hash:=Hash.resultWord words
  let index:=hash &&& (p.capacity-1#64)
  let start:=hash.toNat%(2^bits)
  let headers:=headerState source p
  let hashEntered:=bind {headers with clock:=source.clock-1} "h" hash
  let entered:=prepared source p hash index
  have startInside : start<2^bits:=Nat.mod_lt _ (Nat.two_pow_pos bits)
  have indexEq : index=pathIndex bits start 0:=masked_start p hash bits small capacity
  have locals : Locals entered p (pathIndex bits start 0) := by
    rw [← indexEq]
    exact prepared_locals source p hash index cells.keyLocal
  have viewEntered:=WitnessRadix.MemoryBytes.byteView_of_fields source entered rfl rfl rfl _ _ queryView
  have tableViews : ∀ i<2^bits,usedByte entered p (BitVec.ofNat 64 i)=some 1→
      WitnessRadix.MemoryBytes.ByteView entered (p.keys+BitVec.ofNat 64 i*p.stride) (keys i) := by
    intro i inside occupied
    exact WitnessRadix.MemoryBytes.byteView_of_fields source entered rfl rfl rfl _ _ (views i inside occupied)
  obtain ⟨paid,value,bound,result,frame⟩:=scan32_count_bound entered p bits start small startInside capacity order room keys query locals keyLength
    binary covered tableViews fits viewEntered queryFits little memeqCode (by change 6*order.length≤source.clock-1;omega)
  let post:=(evaluateHOLFiniteState entered afterIndex).2
  have tailRun : evaluateHOLFiniteState entered afterIndex=(some (.returned (.val (.word value))),post):=Prod.ext result rfl
  have iRun : evaluateHOLFiniteState hashEntered afterHash=
      (some (.returned (.val (.word value))),restore hashEntered "i" post) := by
    rw [afterHash]
    exact Input.ScalarScope.declare_execute hashEntered post "i" initialIndex index afterIndex _ (initial_index_read source p hash) tailRun
  have distinct : ([ofString "used",ofString "keys",ofString "stride",ofString "klen",ofString "cap",ofString "key"] : List MlS).Nodup:=by decide
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,and_true,List.nodup_nil] at distinct
  have keyH : headers.locals.lookup (ofString "key")=some (.val (.word p.key)) := by
    have keyLocal:=cells.keyLocal
    simp_all [headers,headerState,WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have klenH : headers.locals.lookup (ofString "klen")=some (.val (.word 32#64)) := by
    simp_all [headers,headerState,WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have args : evalListHOLFinite headers (h:=fun address=>Classical.propDecidable (headers.memaddrs address)) [localVar "key",localVar "klen"]=some [.val (.word p.key),.val (.word 32#64)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,keyH,klenH]
  have hashRun:=Hash.aligned32_call headers p.key words "h" [localVar "key",localVar "klen"] afterHash args hashCode aligned wordMapped wordStored (by change 1≤source.clock;omega)
  change evaluateHOLFiniteState headers hashCall=(let output:=evaluateHOLFiniteState hashEntered afterHash;(output.1,restore headers "h" output.2)) at hashRun
  rw [iRun] at hashRun
  obtain ⟨restoreStack,setup⟩:=header_executes source table p cells
  have prefixRun:=WitnessRadix.ProgramPrefix.execute setup hashCall
  have whole : evaluateHOLFiniteState source body=(some (.returned (.val (.word value))),restoreStack (restore headers "h" (restore hashEntered "i" post))) := by
    rw [header_shape,prefixRun,hashRun]
  refine ⟨paid+1,value,by omega,?_,?_⟩
  · rw [whole]
  · rw [whole,WitnessRadix.ProgramPrefix.restoration_frame setup]
    change emptyLocalsHOLFinite post=emptyLocalsHOLFinite {source with clock:=source.clock-(paid+1)}
    have subtract : source.clock-1-paid=source.clock-(paid+1):=by omega
    have canonical : emptyLocalsHOLFinite {entered with clock:=entered.clock-paid}=
        emptyLocalsHOLFinite {source with clock:=source.clock-(paid+1)} := by
      change emptyLocalsHOLFinite {source with clock:=source.clock-1-paid}=
        emptyLocalsHOLFinite {source with clock:=source.clock-(paid+1)}
      rw [subtract]
    exact frame.trans canonical

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.aligned32_find
