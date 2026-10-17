import InitECandidate.Solver.MutableTable.InsertHeader

namespace InitECandidate.Solver.MutableTable.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem prepared_data (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Find.Parameters)
    (table order position hash index value : BitVec 64)
    (tLocal : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (valueLocal : source.locals.lookup (ofString "value")=some (.val (.word value))) :
    (prepared source p order position hash index).locals.lookup (ofString "t")=some (.val (.word table)) ∧
    (prepared source p order position hash index).locals.lookup (ofString "value")=some (.val (.word value)) ∧
    (prepared source p order position hash index).locals.lookup (ofString "order")=some (.val (.word order)) ∧
    (prepared source p order position hash index).locals.lookup (ofString "order_pos")=some (.val (.word position)) := by
  have distinct : ([ofString "i",ofString "h",ofString "order_pos",ofString "order",ofString "used",ofString "keys",
    ofString "stride",ofString "klen",ofString "cap",ofString "t",ofString "value"] : List MlS).Nodup:=by decide
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,and_true,List.nodup_nil] at distinct
  simp_all [prepared,headerState,Find.headerState,WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]

end InitECandidate.Solver.MutableTable.Insert

#print axioms InitECandidate.Solver.MutableTable.Insert.prepared_data
