import InitECandidate.Solver.PanFieldStoresFrame
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment
import InitECandidate.Solver.Input.OriginalCode

namespace InitECandidate.Solver.Mpt.InsertLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.guestFn__insert_into_leaf with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "node",.one),(ofString "rk",.one),(ofString "rl",.one),(ofString "vptr",.one),(ofString "vlen",.one)]
def afterKey : ProgHOL 64:=match body with | .dec _ _ _ rest=>rest | _=>.skip
def afterLength : ProgHOL 64:=match afterKey with | .dec _ _ _ rest=>rest | _=>.skip
def lengthChoice : ProgHOL 64:=match afterLength with | .seq first _=>first | _=>.skip
def compareScope : ProgHOL 64:=match lengthChoice with | .ite _ yes _=>yes | _=>.skip
def compareGuard : ProgHOL 64:=match compareScope with | .decCall _ _ _ _ rest=>rest | _=>.skip
def replaceBody : ProgHOL 64:=match compareGuard with | .ite _ yes _=>yes | _=>.skip
def fields (pointer size : BitVec 64) : List FieldStores.Field:=
  [⟨48,.saved "vptr" pointer⟩,⟨56,.saved "vlen" size⟩]
def post (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node pointer size : BitVec 64):=
  {source with memory:=WordWrites.write source.memory (FieldStores.writes node (fields pointer size))}

set_option maxRecDepth 100000 in
theorem replace_shape (pointer size : BitVec 64) : replaceBody=FieldStores.program "node" "" (fields pointer size) (.return (localVar "node")) := by
  simp only [replaceBody,compareGuard,compareScope,lengthChoice,afterLength,afterKey,body,Guest.guestFn__insert_into_leaf,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,fields,FieldStores.program,FieldStores.address,
    FieldStores.Value.expression,addConst,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "_insert_into_leaf")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 249 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn__insert_into_leaf) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn__insert_into_leaf,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- Execute the unchanged matching-leaf replacement stores and return.
Only the actual two value fields change; their mapping follows from the
current registered leaf allocation. -/
theorem replace_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node pointer size : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena node 64) (aligned : node.toNat%8=0) :
    evaluateHOLFiniteState source replaceBody=(some (.returned (.val (.word node))),emptyLocalsHOLFinite (post source node pointer size)) := by
  have ready (field : FieldStores.Field) (member : field∈fields pointer size) : field.value.Ready source "" 0#64:=by
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact pointerCell
    · exact sizeCell
  have geometry (field : FieldStores.Field) (member : field∈fields pointer size) : field.offset<64 ∧ field.offset%8=0:=by
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> constructor <;> simp
  have avoid (reader : FieldStores.Field) (member : reader∈fields pointer size) (writer : FieldStores.Field) (writerIn : writer∈fields pointer size) :
      reader.value.Avoid 0#64 (node+BitVec.ofNat 64 writer.offset):=by
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> trivial
  have run:=FieldStores.execute source "node" "" node 0#64 (fields pointer size) nodeCell ready
    (fun field member=>AllocatedBytes.word_mapped source node 64 field.offset domain arena (geometry field member).1 aligned (geometry field member).2)
    avoid (.return (localVar "node"))
  rw [replace_shape pointer size,run]
  simp [evaluateHOLFiniteState_return,evalHOLExact,toExact,localVar,nodeCell,shapeOfHOLExact,sizeOfShapeWithContextHOL,post]

theorem post_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node pointer size query : BitVec 64)
    (away48 : query≠node+48#64) (away56 : query≠node+56#64) :
    (post source node pointer size).memory query=source.memory query := by
  apply WordWrites.write_away
  simpa [FieldStores.writes,fields] using And.intro away48 away56

theorem post_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node pointer size : BitVec 64) :
    (post source node pointer size).memory (node+48#64)=.word pointer ∧
      (post source node pointer size).memory (node+56#64)=.word size := by
  simp [post,fields,FieldStores.writes,WordWrites.write,StoreWord.put,FieldStores.Value.word,BitVec.add_right_inj]

end InitECandidate.Solver.Mpt.InsertLeaf

#print axioms InitECandidate.Solver.Mpt.InsertLeaf.replace_shape
#print axioms InitECandidate.Solver.Mpt.InsertLeaf.original_code
#print axioms InitECandidate.Solver.Mpt.InsertLeaf.replace_execute
#print axioms InitECandidate.Solver.Mpt.InsertLeaf.post_away
#print axioms InitECandidate.Solver.Mpt.InsertLeaf.post_cells
