import InitECandidate.Solver.MutableTable.FindMemory32

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix

/-- Lift an already checked actual scan/return through every real header,
hash/index declaration and scope of original find_slot. This is a composition
lemma; the supplied run is only its actual afterIndex suffix. -/
theorem lift_tail32 (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Parameters)
    (cells : HeaderCells source table p) (keyLength : p.keyLength=32#64)
    (query : WitnessRadix.ByteKeys.Key) (queryView : WitnessRadix.MemoryBytes.ByteView source p.key query)
    (queryFits : p.key.toNat+32<2^64) (little : source.be=false)
    (hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (value : BitVec 64) (paid : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (tailRun : evaluateHOLFiniteState (prepared source p (Hash.keyHash query) (Hash.keyHash query &&& (p.capacity-1#64))) afterIndex=
      (some (.returned (.val (.word value))),post))
    (frame : emptyLocalsHOLFinite post=emptyLocalsHOLFinite
      {prepared source p (Hash.keyHash query) (Hash.keyHash query &&& (p.capacity-1#64)) with clock:=source.clock-1-paid})
    (enough : 1≤source.clock) :
    ∃ target,evaluateHOLFiniteState source body=(some (.returned (.val (.word value))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-(paid+1)} := by
  let hash:=Hash.keyHash query
  let index:=hash &&& (p.capacity-1#64)
  let headers:=headerState source p
  let hashEntered:=bind {headers with clock:=source.clock-1} "h" hash
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
  have hashRun:=Hash.memory_call headers p.key query "h" [localVar "key",localVar "klen"] afterHash args hashCode queryView queryFits little enough
  change evaluateHOLFiniteState headers hashCall=(let output:=evaluateHOLFiniteState hashEntered afterHash;(output.1,restore headers "h" output.2)) at hashRun
  rw [iRun] at hashRun
  obtain ⟨restoreStack,setup⟩:=header_executes source table p cells
  have prefixRun:=WitnessRadix.ProgramPrefix.execute setup hashCall
  let target:=restoreStack (restore headers "h" (restore hashEntered "i" post))
  refine ⟨target,?_,?_⟩
  · rw [header_shape,prefixRun,hashRun]
  · rw [show emptyLocalsHOLFinite target=emptyLocalsHOLFinite (restore headers "h" (restore hashEntered "i" post)) from
      WitnessRadix.ProgramPrefix.restoration_frame setup _]
    change emptyLocalsHOLFinite post=emptyLocalsHOLFinite {source with clock:=source.clock-(paid+1)}
    have canonical : emptyLocalsHOLFinite {prepared source p hash index with clock:=source.clock-1-paid}=
        emptyLocalsHOLFinite {source with clock:=source.clock-(paid+1)} := by
      have subtract : source.clock-1-paid=source.clock-(paid+1):=by omega
      change emptyLocalsHOLFinite {source with clock:=source.clock-1-paid}=_
      rw [subtract]
    exact frame.trans canonical

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.lift_tail32
