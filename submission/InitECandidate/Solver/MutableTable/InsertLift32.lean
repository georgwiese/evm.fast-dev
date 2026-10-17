import InitECandidate.Solver.MutableTable.InsertHeader
import InitECandidate.Solver.MutableTable.HashMemory32

namespace InitECandidate.Solver.MutableTable.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem initial_index_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Find.Parameters)
    (order position hash : BitVec 64) :
    eval (bind {headerState source p order position with clock:=source.clock-1} "h" hash) Find.initialIndex=
      some (.val (.word (hash &&& (p.capacity-1#64)))) := by
  have fold (a b : BitVec 64) : AndOp.and a (AndOp.and b (18446744073709551615#64))=a &&& b := by
    change a &&& (b &&& BitVec.allOnes 64)=a &&& b
    rw [BitVec.and_allOnes]
  have distinct : ([ofString "h",ofString "order_pos",ofString "order",ofString "used",ofString "keys",
    ofString "stride",ofString "klen",ofString "cap"] : List MlS).Nodup:=by decide
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,and_true,List.nodup_nil] at distinct
  simp_all [eval,Find.initialIndex,Find.mask,evalHOLExact,evalListHOLExact,toExact,localVar,headerState,Find.headerState,
    WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,valueIsWord,valueWord,wordOpHOL,wordOp,fold]

/-- Lift the actual insertion suffix through all seven header reads, the
real byte-key hash body/call, index declaration and lexical scopes. -/
theorem lift_tail32 (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Find.Parameters)
    (order position : BitVec 64) (cells : Find.HeaderCells source table p) (keyLength : p.keyLength=32#64)
    (orderMapped : source.memaddrs (table+56#64)) (orderCell : source.memory (table+56#64)=.word order)
    (positionMapped : source.memaddrs (table+64#64)) (positionCell : source.memory (table+64#64)=.word position)
    (query : WitnessRadix.ByteKeys.Key) (queryView : WitnessRadix.MemoryBytes.ByteView source p.key query)
    (queryFits : p.key.toNat+32<2^64) (little : source.be=false)
    (hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (paid : Nat) (memory : WitnessRadix.WordWrites.Memory) (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (tailRun : evaluateHOLFiniteState
      (prepared source p order position (Hash.keyHash query) (Hash.keyHash query &&& (p.capacity-1#64))) afterIndex=
      (some (.returned (.val (.word 0#64))),post))
    (frame : emptyLocalsHOLFinite post=emptyLocalsHOLFinite
      {source with memory:=memory,clock:=source.clock-1-paid}) (enough : 1≤source.clock) :
    ∃ target,evaluateHOLFiniteState source body=(some (.returned (.val (.word 0#64))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=memory,clock:=source.clock-(paid+1)} := by
  let hash:=Hash.keyHash query
  let index:=hash &&& (p.capacity-1#64)
  let headers:=headerState source p order position
  let hashEntered:=bind {headers with clock:=source.clock-1} "h" hash
  have iRun : evaluateHOLFiniteState hashEntered afterHash=
      (some (.returned (.val (.word 0#64))),restore hashEntered "i" post) := by
    exact Input.ScalarScope.declare_execute hashEntered post "i" Find.initialIndex index afterIndex _
      (initial_index_read source p order position hash) tailRun
  have distinct : ([ofString "order_pos",ofString "order",ofString "used",ofString "keys",ofString "stride",ofString "klen",ofString "cap",ofString "key"] : List MlS).Nodup:=by decide
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,and_true,List.nodup_nil] at distinct
  have keyH : headers.locals.lookup (ofString "key")=some (.val (.word p.key)) := by
    have original:=cells.keyLocal
    simp_all [headers,headerState,Find.headerState,WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have klenH : headers.locals.lookup (ofString "klen")=some (.val (.word 32#64)) := by
    simp_all [headers,headerState,Find.headerState,WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have args : evalListHOLFinite headers (h:=fun address=>Classical.propDecidable (headers.memaddrs address))
      [localVar "key",localVar "klen"]=some [.val (.word p.key),.val (.word 32#64)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,keyH,klenH]
  have hashRun:=Hash.memory_call headers p.key query "h" [localVar "key",localVar "klen"] afterHash
    args hashCode queryView queryFits little enough
  change evaluateHOLFiniteState headers
    (.decCall (ofString "h") .one (ofString "htab_hash") [localVar "key",localVar "klen"] afterHash)=
      (let output:=evaluateHOLFiniteState hashEntered afterHash;(output.1,restore headers "h" output.2)) at hashRun
  rw [iRun] at hashRun
  obtain ⟨restoreStack,setup⟩:=header_executes source table p order position cells orderMapped orderCell positionMapped positionCell
  have prefixRun:=WitnessRadix.ProgramPrefix.execute setup
    (.decCall (ofString "h") .one (ofString "htab_hash") [localVar "key",localVar "klen"] afterHash)
  let target:=restoreStack (restore headers "h" (restore hashEntered "i" post))
  refine ⟨target,?_,?_⟩
  · rw [body_shape,prefixRun,hashRun]
  · rw [show emptyLocalsHOLFinite target=emptyLocalsHOLFinite (restore headers "h" (restore hashEntered "i" post)) from
      WitnessRadix.ProgramPrefix.restoration_frame setup _]
    change emptyLocalsHOLFinite post=_
    rw [frame]
    have subtract : source.clock-1-paid=source.clock-(paid+1):=by omega
    rw [subtract]

end InitECandidate.Solver.MutableTable.Insert

#print axioms InitECandidate.Solver.MutableTable.Insert.initial_index_read
#print axioms InitECandidate.Solver.MutableTable.Insert.lift_tail32
