import InitECandidate.Solver.MutableTable.InsertCopy32
import InitECandidate.Solver.MutableTable.FindPrepared

namespace InitECandidate.Solver.MutableTable.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix

theorem append_executes {F : Type} {source middle target : PanSemStateFiniteExact 64 F}
    {first second : List Action} {restoreFirst restoreSecond : PanSemStateFiniteExact 64 F→PanSemStateFiniteExact 64 F}
    (front : Executes source first middle restoreFirst) (back : Executes middle second target restoreSecond) :
    Executes source (first++second) target (fun post=>restoreFirst (restoreSecond post)) := by
  induction front with
  | done=>exact back
  | declare word read next ih=>exact .declare word read (ih back)
  | allocate pointer amount read code heap fits enough next ih=>exact .allocate pointer amount read code heap fits enough (ih back)
  | command run clock next ih=>exact .command run clock (ih back)

def headerState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Find.Parameters) (order position : BitVec 64) :
    PanSemStateFiniteExact 64 Guest.HostMemory:=bind (bind (Find.headerState source p) "order" order) "order_pos" position

def prepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Find.Parameters)
    (order position hash index : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory:=
  bind (bind {headerState source p order position with clock:=source.clock-1} "h" hash) "i" index

/-- All seven actual raw-insertion header declarations and their scopes. -/
theorem header_executes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Find.Parameters)
    (order position : BitVec 64) (header : Find.HeaderCells source table p)
    (orderMapped : source.memaddrs (table+56#64)) (orderCell : source.memory (table+56#64)=.word order)
    (positionMapped : source.memaddrs (table+64#64)) (positionCell : source.memory (table+64#64)=.word position) :
    ∃ restoreStack,Executes source headerActions (headerState source p order position) restoreStack := by
  obtain ⟨restoreFirst,front⟩:=Find.header_executes source table p header
  let headers:=Find.headerState source p
  have distinct : ([ofString "order",ofString "used",ofString "keys",ofString "stride",ofString "klen",ofString "cap",ofString "t"] : List MlS).Nodup:=by decide
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,and_true,List.nodup_nil] at distinct
  have tLocal : headers.locals.lookup (ofString "t")=some (.val (.word table)) := by
    have original:=header.tableLocal
    simp_all [headers,Find.headerState,WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have orderRead:=Find.table_read headers table 56#64 order tLocal orderMapped orderCell
  have nextLocal : (bind headers "order" order).locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other _ "order" "t" _ (by decide)).trans tLocal
  have positionRead:=Find.table_read (bind headers "order" order) table 64#64 position nextLocal positionMapped positionCell
  have back : Executes headers [.declare "order" (Find.tableLoad 56#64),.declare "order_pos" (Find.tableLoad 64#64)]
      (headerState source p order position) _ :=.declare order orderRead (.declare position positionRead (.done _))
  exact ⟨_,append_executes front back⟩

theorem prepared_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Find.Parameters)
    (order position hash index : BitVec 64) (key : source.locals.lookup (ofString "key")=some (.val (.word p.key))) :
    Find.Locals (prepared source p order position hash index) p index := by
  have distinct : ([ofString "i",ofString "h",ofString "order_pos",ofString "order",ofString "used",ofString "keys",
    ofString "stride",ofString "klen",ofString "cap",ofString "key"] : List MlS).Nodup:=by decide
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,and_true,List.nodup_nil] at distinct
  constructor
  all_goals simp_all [prepared,headerState,Find.headerState,WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,key]

end InitECandidate.Solver.MutableTable.Insert

#print axioms InitECandidate.Solver.MutableTable.Insert.header_executes
#print axioms InitECandidate.Solver.MutableTable.Insert.prepared_locals
