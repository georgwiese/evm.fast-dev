import InitECandidate.Solver.MutableTable.FindAnyHashCost
import InitECandidate.Solver.MutableTable.FindAnyLoop
import InitECandidate.Solver.MutableTable.FindGeneralBuild

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The complete original32-byte finder costs at most six source ticks
per occupied slot plus its real hash call. Query reads may fail or be
unaligned; only the actual table's physical ownership/occupancy is required. -/
theorem any_body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Parameters)
    (cells : HeaderCells source table p) (keyLength : p.keyLength=32#64)
    (bits : Nat) (small : bits<64) (capacity : p.capacity=BitVec.ofNat 64 (2^bits))
    (order : List Nat) (room : order.length<2^bits)
    (binary : ∀ i<2^bits,usedByte source p (BitVec.ofNat 64 i)=some 0 ∨ usedByte source p (BitVec.ofNat 64 i)=some 1)
    (covered : ∀ i<2^bits,usedByte source p (BitVec.ofNat 64 i)=some 1→i∈order)
    (fits : ∀ i<2^bits,(p.keys+BitVec.ofNat 64 i*p.stride).toNat+32<2^64)
    (mapped : ∀ i<2^bits,∀ offset<32,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress (p.keys+BitVec.ofNat 64 i*p.stride) offset)))
    (hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (memeqCode : source.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one)) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤6*order.length+1 := by
  let headers:=headerState source p
  have distinct : ([ofString "used",ofString "keys",ofString "stride",ofString "klen",ofString "cap",ofString "key"] : List MlS).Nodup := by decide
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,and_true,List.nodup_nil] at distinct
  have keyH : headers.locals.lookup (ofString "key")=some (.val (.word p.key)) := by
    have keyLocal:=cells.keyLocal
    simp_all [headers,headerState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have klenH : headers.locals.lookup (ofString "klen")=some (.val (.word 32#64)) := by
    simp_all [headers,headerState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have hashPrice:=any_hash_call_cost headers p.key keyH klenH hashCode (6*order.length) (by
    intro hash
    let index:=hash &&& (p.capacity-1#64)
    let start:=hash.toNat%(2^bits)
    let entered:=prepared source p hash index
    have startInside : start<2^bits := Nat.mod_lt _ (Nat.two_pow_pos bits)
    obtain ⟨length,bounded,chain⟩ := general_chain_of_order source p .word bits start small startInside capacity order room binary covered fits mapped
    have indexEq : index=pathIndex bits start 0 := masked_start p hash bits small capacity
    have locals : Locals entered p (pathIndex bits start 0) := by
      rw [← indexEq]
      exact prepared_locals source p hash index cells.keyLocal
    have scan:=any_chain_suffix_cost source p _ length chain keyLength entered locals rfl memeqCode
    have estimate : entered.clock-(evaluateHOLFiniteState entered afterIndex).2.clock≤6*order.length := scan.trans (by omega)
    exact Input.ClockCost.declared_current (QueryBranch.bind {headers with clock:=headers.clock-1} "h" hash) "i" initialIndex index afterIndex (6*order.length)
      (initial_index_read source p hash) estimate)
  obtain ⟨restoreStack,setup⟩ := header_executes source table p cells
  have actual:=ProgramPrefix.execute setup hashCall
  have restoreFrame:=ProgramPrefix.restoration_frame setup (evaluateHOLFiniteState headers hashCall).2
  have restoreClock:=congrArg PanSemStateFiniteExact.clock restoreFrame
  change (restoreStack (evaluateHOLFiniteState headers hashCall).2).clock=(evaluateHOLFiniteState headers hashCall).2.clock at restoreClock
  rw [header_shape,actual]
  change source.clock-(restoreStack (evaluateHOLFiniteState headers hashCall).2).clock≤6*order.length+1
  rw [restoreClock]
  exact hashPrice

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.any_body_cost
