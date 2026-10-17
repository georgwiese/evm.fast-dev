import InitECandidate.Solver.MutableTable.FindHeader

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def prepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (hash index : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory:=
  bind (bind {headerState source p with clock:=source.clock-1} "h" hash) "i" index

theorem prepared_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (hash index : BitVec 64)
    (key : source.locals.lookup (ofString "key")=some (.val (.word p.key))) : Locals (prepared source p hash index) p index := by
  have distinct : ([ofString "i",ofString "h",ofString "used",ofString "keys",ofString "stride",ofString "klen",ofString "cap",ofString "key"] : List MlS).Nodup:=by decide
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,and_true,List.nodup_nil] at distinct
  constructor
  all_goals simp_all [prepared,headerState,WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,key]

theorem initial_index_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (hash : BitVec 64) :
    eval (bind {headerState source p with clock:=source.clock-1} "h" hash) initialIndex=
      some (.val (.word (hash &&& (p.capacity-1#64)))) := by
  have fold (a b : BitVec 64) : AndOp.and a (AndOp.and b (18446744073709551615#64))=a &&& b := by
    change a &&& (b &&& BitVec.allOnes 64)=a &&& b
    rw [BitVec.and_allOnes]
  have distinct : ([ofString "i",ofString "h",ofString "used",ofString "keys",ofString "stride",ofString "klen",ofString "cap",ofString "key"] : List MlS).Nodup:=by decide
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,and_true,List.nodup_nil] at distinct
  simp_all [eval,initialIndex,mask,evalHOLExact,evalListHOLExact,toExact,localVar,headerState,
    WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,valueIsWord,valueWord,wordOpHOL,wordOp,fold]

theorem masked_start (p : Parameters) (hash : BitVec 64) (bits : Nat) (small : bits<64)
    (capacity : p.capacity=BitVec.ofNat 64 (2^bits)) :
    hash &&& (p.capacity-1#64)=pathIndex bits (hash.toNat%(2^bits)) 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [capacity,Probe.power_mask hash bits small,path_number bits _ 0 small]
  simp only [Probe.slot,Nat.add_zero,Nat.mod_mod]

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.prepared_locals
#print axioms InitECandidate.Solver.MutableTable.Find.initial_index_read
#print axioms InitECandidate.Solver.MutableTable.Find.masked_start
