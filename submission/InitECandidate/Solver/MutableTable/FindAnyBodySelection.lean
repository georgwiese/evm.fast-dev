import InitECandidate.Solver.MutableTable.FindAnyHashNormal
import InitECandidate.Solver.MutableTable.FindAnyBodyCost
import InitECandidate.Solver.MutableTable.FindAnySelection
import InitECandidate.Solver.Input.ScalarScopeTrace

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine normal full original finder selects an actual occupied slot
or its absent sentinel. Query bytes, hash injectivity and future successful
reads are not assumptions of this physical result. -/
theorem any_body_selection (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Parameters)
    (cells : HeaderCells source table p) (keyLength : p.keyLength=32#64)
    (bits : Nat) (small : bits<64) (capacity : p.capacity=BitVec.ofNat 64 (2^bits))
    (order : List Nat) (room : order.length<2^bits)
    (binary : ∀ i<2^bits,usedByte source p (BitVec.ofNat 64 i)=some 0 ∨ usedByte source p (BitVec.ofNat 64 i)=some 1)
    (covered : ∀ i<2^bits,usedByte source p (BitVec.ofNat 64 i)=some 1→i∈order)
    (fits : ∀ i<2^bits,(p.keys+BitVec.ofNat 64 i*p.stride).toNat+32<2^64)
    (mapped : ∀ i<2^bits,∀ offset<32,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress (p.keys+BitVec.ofNat 64 i*p.stride) offset)))
    (hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (memeqCode : source.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ answer,value=.val (.word answer) ∧ Selection source p answer := by
  let headers:=headerState source p
  have distinct : ([ofString "used",ofString "keys",ofString "stride",ofString "klen",ofString "cap",ofString "key"] : List MlS).Nodup := by decide
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,and_true,List.nodup_nil] at distinct
  have keyH : headers.locals.lookup (ofString "key")=some (.val (.word p.key)) := by
    have keyLocal:=cells.keyLocal
    simp_all [headers,headerState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have klenH : headers.locals.lookup (ofString "klen")=some (.val (.word 32#64)) := by
    simp_all [headers,headerState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  obtain ⟨restoreStack,setup⟩ := header_executes source table p cells
  have actual:=ProgramPrefix.execute setup hashCall
  have resultEq:=congrArg Prod.fst normal
  rw [header_shape,actual] at resultEq
  have hashRun : evaluateHOLFiniteState headers hashCall=(some (.returned value),(evaluateHOLFiniteState headers hashCall).2) := Prod.ext resultEq rfl
  obtain ⟨hash,inner,funded,continued,endpoint⟩ := any_hash_normal headers _ p.key keyH klenH hashCode value hashRun
  let index:=hash &&& (p.capacity-1#64)
  let start:=hash.toNat%(2^bits)
  let hashEntry:=QueryBranch.bind {headers with clock:=headers.clock-1} "h" hash
  let entered:=prepared source p hash index
  change evaluateHOLFiniteState hashEntry (.dec (ofString "i") .one initialIndex afterIndex)=(some (.returned value),inner) at continued
  obtain ⟨scanPost,scanRun,scanEnd⟩ := Input.ScalarScope.declare_trace hashEntry inner "i" initialIndex index afterIndex _
    (initial_index_read source p hash) continued
  have startInside : start<2^bits := Nat.mod_lt _ (Nat.two_pow_pos bits)
  obtain ⟨length,bounded,chain⟩ := general_chain_of_order source p .word bits start small startInside capacity order room binary covered fits mapped
  have indexEq : index=pathIndex bits start 0 := masked_start p hash bits small capacity
  have locals : Locals entered p (pathIndex bits start 0) := by
    rw [← indexEq]
    exact prepared_locals source p hash index cells.keyLocal
  exact any_chain_selection source p _ length chain keyLength entered scanPost locals rfl memeqCode value scanRun

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.any_body_selection
